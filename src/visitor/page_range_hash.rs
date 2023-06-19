use crate::{diff::PageRange, Node, Page};

use super::Visitor;

/// Record the page range & hashes for the visited pages.
#[derive(Debug)]
pub(crate) struct PageRangeHashVisitor<'a, K> {
    out: Vec<PageRange<'a, K>>,
}

impl<'a, K> Default for PageRangeHashVisitor<'a, K> {
    fn default() -> Self {
        Self {
            out: Default::default(),
        }
    }
}

impl<'a, const N: usize, K> Visitor<'a, N, K> for PageRangeHashVisitor<'a, K>
where
    K: PartialOrd,
{
    fn visit_node(&mut self, _node: &'a Node<N, K>) -> bool {
        true
    }

    fn visit_page(&mut self, page: &'a Page<N, K>, _high_page: bool) -> bool {
        if !page.nodes().is_empty() {
            let p = PageRange::new(
                get_min(page),
                get_max(page),
                page.hash()
                    .expect("page hash must be calculated before serialising")
                    .clone(),
            );
            self.out.push(p);
        }
        true
    }
}

impl<'a, K> PageRangeHashVisitor<'a, K> {
    pub(crate) fn finalise(self) -> Vec<PageRange<'a, K>> {
        self.out
    }
}

/// Descend down the minimum (left most) path (if any) and return the minimum
/// key in the subtree rooted at `p`.
fn get_min<const N: usize, K>(p: &'_ Page<N, K>) -> &'_ K {
    let v = p.nodes().get(0).and_then(|v| v.lt_pointer());
    if let Some(v) = v {
        return get_min(v);
    }

    p.min_key()
}

/// Chase the high page pointers to the maximum page value of the subtree rooted
/// at `p`.
fn get_max<const N: usize, K>(p: &'_ Page<N, K>) -> &'_ K {
    p.high_page()
        .map(|v| get_max(v))
        .unwrap_or_else(|| p.max_key())
}

#[cfg(test)]
mod tests {
    use siphasher::sip128::SipHasher24;

    use crate::{
        digest::{Digest, ValueDigest},
        test_util::IntKey,
    };

    use super::*;

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
    fn test_page_ranges() {
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

        root.maybe_generate_hash(&SipHasher24::default());

        let mut v = PageRangeHashVisitor::default();
        root.in_order_traversal(&mut v, false);

        let got = v
            .finalise()
            .into_iter()
            .map(|v| (v.start().unwrap(), v.end().unwrap()))
            .collect::<Vec<_>>();

        // Pre-order page traversal:
        assert_matches::assert_matches!(
            got.as_slice(),
            [(2, 42), (2, 6), (2, 2), (5, 5), (15, 42), (42, 42)]
        );
    }

    /// The root page has a child page, but no values within the subtree are
    /// smaller than the root page's minimum.
    #[test]
    fn test_page_range_no_smaller_subtree() {
        let level_0 = Page::new(
            0,
            vec![
                Node::new(IntKey::new(2), MOCK_VALUE, None),
                Node::new(IntKey::new(3), MOCK_VALUE, None),
            ],
        );

        let mut level_1 = Page::new(
            1,
            vec![
                Node::new(IntKey::new(1), MOCK_VALUE, None),
                Node::new(IntKey::new(4), MOCK_VALUE, Some(level_0.into())),
            ],
        );

        level_1.maybe_generate_hash(&SipHasher24::default());

        let mut v = PageRangeHashVisitor::default();
        level_1.in_order_traversal(&mut v, false);

        let got = v
            .finalise()
            .into_iter()
            .map(|v| (v.start().unwrap(), v.end().unwrap()))
            .collect::<Vec<_>>();

        // Pre-order page traversal:
        assert_matches::assert_matches!(got.as_slice(), [(1, 4), (2, 3),]);
    }
}
