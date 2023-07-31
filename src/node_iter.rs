use std::fmt::Debug;

use crate::{Node, Page};

/// A [`Page`] and iteration metadata in the [`NodeIter`] stack.
#[derive(Debug)]
struct PageVisit<'a, const N: usize, K> {
    page: &'a Page<N, K>,

    /// The 0-based index of the node to visit next in this page.
    idx: usize,

    /// The outcome of the last visit.
    state: VisitState,
}

/// Describes what action was previously taken (if any) for the indexed node.
#[derive(Debug)]
enum VisitState {
    /// The indexed node has not yet been visited.
    ///
    /// If the node has a lt_pointer, the state shall move to
    /// [`Self::Descended`] and the tree will be traversed downwards to the
    /// first leaf.
    ///
    /// If the node contains no lt_pointer, it will be yielded to the iterator.
    Unvisited,

    /// The node was previously visited, but not yielded due to the presence of
    /// a lt_pointer to descend down. It will be yielded next.
    Descended,
}

/// An iterator over [`Node`], yielded in ascending key order.
#[derive(Debug)]
pub(crate) struct NodeIter<'a, const N: usize, K> {
    /// A stack of visited pages as the iterator descends the tree.
    ///
    /// Approx log_{16}N max entries.
    stack: Vec<PageVisit<'a, N, K>>,
}

impl<'a, const N: usize, K> NodeIter<'a, N, K> {
    pub(crate) fn new(p: &'a Page<N, K>) -> Self {
        Self {
            stack: vec![PageVisit {
                page: p,
                idx: 0,
                state: VisitState::Unvisited,
            }],
        }
    }
}

impl<'a, const N: usize, K> Iterator for NodeIter<'a, N, K> {
    type Item = &'a Node<N, K>;

    fn next(&mut self) -> Option<Self::Item> {
        'outer: loop {
            let p = self.stack.pop()?;

            // Try and load the indexed node in this page.
            let n = match p.page.nodes().iter().nth(p.idx) {
                Some(v) => v,
                None => {
                    // No more nodes, instead visit the high page next, if any.
                    if let Some(h) = p.page.high_page() {
                        self.stack.push(PageVisit {
                            page: h,
                            idx: 0,
                            state: VisitState::Unvisited,
                        });
                    }

                    // Loop again, potentially popping the just-added high page,
                    // or popping a higher-level page (moving up the tree) if
                    // none.
                    continue 'outer;
                }
            };

            match p.state {
                VisitState::Unvisited => {
                    // This node has not been yielded, nor descended.
                    //
                    // If it has a lt_pointer, descend down it and visit this
                    // node later.
                    if let Some(lt) = n.lt_pointer() {
                        // Push this page back onto the stack to be revisited.
                        self.stack.push(PageVisit {
                            state: VisitState::Descended,
                            ..p
                        });
                        // And push the newly discovered page onto the stack.
                        self.stack.push(PageVisit {
                            state: VisitState::Unvisited,
                            idx: 0,
                            page: lt,
                        });
                        // Pop it off the next loop iteration and visit the
                        // first node.
                        continue 'outer;
                    }

                    // Otherwise there's no lt_pointer to follow in this node,
                    // so this node should be yielded and the page's node index
                    // incremented for the next iteration so the next node is
                    // visited.
                }
                VisitState::Descended => {
                    // The current index was previously descended down.
                    assert!(n.lt_pointer().is_some());
                    // But was never yielded.
                    //
                    // Advance the page's node index for the next iteration, and
                    // yield it now.
                }
            }

            self.stack.push(PageVisit {
                state: VisitState::Unvisited,
                idx: p.idx + 1,
                page: p.page,
            });

            return Some(n);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{
        digest::{Digest, ValueDigest},
        test_util::IntKey,
        Node,
    };

    const MOCK_VALUE: ValueDigest<32> = ValueDigest::new(Digest::new([0; 32]));

    //                    ┌ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ┐
    //                      ┌───┬───┬───────┐
    //                    │ │ 7 │11 │ high  │ Level 2 │
    //                      └───┴───┴───────┘
    //                    └ ─ ┬ ─ ─ ─ ─ ┬ ─ ─ ─ ─ ─ ─ ┘
    //                   ┌────┘         └─────────┐
    //                   ▼                        ▼
    //       ┌ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─  ┌ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ┐
    //         ┌───┬───┬───┐        │   ┌───┬───────┐
    //       │ │ 3 │ 4 │ 6 │Level 1   │ │15 │ high  │ Level 1 │
    //         └───┴───┴───┘        │   └───┴───────┘
    //       └ ─ ┬ ─ ─ ─ ┬ ─ ─ ─ ─ ─  └ ─ ─ ─ ─ ┬ ─ ─ ─ ─ ─ ─ ┘
    //           └┐      └──────────┐           └─────┐
    //            ▼                 ▼                 ▼
    //    ┌ ─ ─ ─ ─ ─ ─ ─ ┐ ┌ ─ ─ ─ ─ ─ ─ ─ ┐ ┌ ─ ─ ─ ─ ─ ─ ─ ┐
    //      ┌───┐             ┌───┐             ┌───┐
    //    │ │ 2 │ Level 0 │ │ │ 5 │ Level 0 │ │ │42 │ Level 0 │
    //      └───┘             └───┘             └───┘
    //    └ ─ ─ ─ ─ ─ ─ ─ ┘ └ ─ ─ ─ ─ ─ ─ ─ ┘ └ ─ ─ ─ ─ ─ ─ ─ ┘

    #[test]
    fn test_order() {
        let lt0 = Page::new(0, vec![Node::new(IntKey::new(2), MOCK_VALUE, None)]);
        let gt0 = Page::new(0, vec![Node::new(IntKey::new(5), MOCK_VALUE, None)]);

        let lt1 = Page::new(
            1,
            vec![
                Node::new(IntKey::new(3), MOCK_VALUE, Some(lt0.into())),
                Node::new(IntKey::new(4), MOCK_VALUE, None),
                Node::new(IntKey::new(6), MOCK_VALUE, Some(gt0.into())),
            ],
        );

        let high2 = Page::new(1, vec![Node::new(IntKey::new(42), MOCK_VALUE, None)]);
        let mut high = Page::new(1, vec![Node::new(IntKey::new(15), MOCK_VALUE, None)]);
        high.insert_high_page(high2.into());

        let mut root = Page::new(
            2,
            vec![
                Node::new(IntKey::new(7), MOCK_VALUE, Some(lt1.into())),
                Node::new(IntKey::new(11), MOCK_VALUE, None),
            ],
        );
        root.insert_high_page(high.into());

        let key_order = NodeIter::new(&root)
            .map(|v| v.key().unwrap())
            .collect::<Vec<_>>();

        assert_eq!(key_order.as_slice(), [2, 3, 4, 5, 6, 7, 11, 15, 42]);
    }
}
