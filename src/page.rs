use std::{cmp::Ordering, hash::Hasher, ops::DerefMut};

use siphasher::sip128::{Hasher128, SipHasher24};

use crate::{
    digest::{Digest, PageDigest, ValueDigest},
    node::Node,
    visitor::Visitor,
};

/// A group of [`Node`] instances of the same level.
#[derive(Debug, PartialEq, Eq, Clone)]
pub struct Page<const N: usize, K> {
    level: u8,

    /// The cached hash in this page; the cumulation of the hashes of the
    /// sub-tree rooted at this page.
    tree_hash: Option<PageDigest>,

    /// A vector of nodes in this page, ordered min to max by key.
    nodes: Vec<Node<N, K>>,

    /// The page for keys greater-than all keys in nodes.
    high_page: Option<Box<Page<N, K>>>,
}

impl<const N: usize, K> Page<N, K> {
    pub(super) const fn new(level: u8, nodes: Vec<Node<N, K>>) -> Self {
        Self {
            level,
            tree_hash: None,
            nodes,
            high_page: None,
        }
    }

    /// Returns the the [`Node`] in this page.
    pub fn nodes(&self) -> &[Node<N, K>] {
        &self.nodes
    }

    /// Returns the tree level / deterministic / logical hight of this page in
    /// the tree.
    pub const fn level(&self) -> u8 {
        self.level
    }

    /// Return the cached hash of this page if any, covering the nodes and the
    /// sub-tree rooted at `self`.
    pub fn hash(&self) -> Option<&PageDigest> {
        self.tree_hash.as_ref()
    }

    pub(crate) fn insert_high_page(&mut self, p: Box<Self>) {
        debug_assert!(self.high_page.is_none());
        debug_assert!(!p.nodes().is_empty());

        // Invalidate the hash of this page.
        self.tree_hash = None;
        self.high_page = Some(p)
    }

    pub(crate) fn high_page(&self) -> Option<&Self> {
        self.high_page.as_deref()
    }

    /// Perform a depth-first, pre-order traversal, yielding each [`Page`] and
    /// [`Node`] to `visitor`.
    ///
    /// If `high_page` is true, this page was linked to from the parent via a
    /// high page pointer.
    pub(crate) fn pre_order_traversal<T>(&self, visitor: &mut T, high_page: bool) -> bool
    where
        T: Visitor<N, K>,
    {
        if !visitor.visit_page(self, high_page) {
            return false;
        }

        for node in &self.nodes {
            if !node.depth_first(visitor) {
                return false;
            }
        }

        if !visitor.post_visit_page(self) {
            return false;
        }

        if let Some(h) = &self.high_page {
            if !h.pre_order_traversal(visitor, true) {
                return false;
            }
        }

        true
    }

    /// Return the minimum key stored in this page.
    ///
    /// # Panics
    ///
    /// Panics if there are no nodes in this page.
    pub(crate) fn min_key(&self) -> &K {
        self.nodes.first().unwrap().key()
    }

    /// Return the maximum key stored in this page.
    ///
    /// # Panics
    ///
    /// Panics if there are no nodes in this page.
    pub(crate) fn max_key(&self) -> &K {
        self.nodes.last().unwrap().key()
    }
}

impl<const N: usize, K> Page<N, K>
where
    K: AsRef<[u8]>,
{
    /// Generate the page hash and cache the value, covering the nodes and the
    /// sub-tree rooted at `self`.
    pub fn maybe_generate_hash(&mut self, hasher: &SipHasher24) {
        if self.tree_hash.is_some() {
            return;
        }

        let mut h = *hasher;

        // NOTE: changing the ordering of the hashed elements is a breaking
        // change.
        //
        // This order may be changed only if releasing a new major version.

        // Hash all nodes & their child pages
        for n in &mut self.nodes {
            // Hash the lt child page of this node, if any
            if let Some(child_hash) = n.lt_pointer_mut().as_deref_mut().map(|v| {
                v.maybe_generate_hash(hasher);
                v.hash().unwrap()
            }) {
                h.write(child_hash.as_ref());
            }

            // Hash the node value itself
            h.write(n.key().as_ref());
            h.write(n.value_hash().as_ref());
        }

        // Hash the high page, if any
        if let Some(high_hash) = self.high_page.as_deref_mut().map(|v| {
            v.maybe_generate_hash(hasher);
            v.hash().unwrap()
        }) {
            h.write(high_hash.as_ref());
        }

        self.tree_hash = Some(PageDigest::new(Digest::new(h.finish128().as_bytes())));
    }
}

impl<const N: usize, K> Page<N, K>
where
    K: PartialOrd + Clone,
{
    /// Insert or update the value hash of `key`, setting it to `value`, found
    /// at tree `level`.
    ///
    /// Returns true if the key was found, or false otherwise.
    ///
    /// If the key is found/modified, the cached page hash is invalidated.
    pub(crate) fn upsert(&mut self, key: &K, level: u8, value: ValueDigest<N>) -> bool {
        match level.cmp(&self.level) {
            // Level is less than this page's level - descend down the tree.
            Ordering::Less => {
                // A non-zero page can never be empty, and level is less than
                // this page, which means this page must be non-zero.
                debug_assert_ne!(!self.level, 0);
                debug_assert!(!self.nodes.is_empty());

                // Mark the page as "dirty" causing the hash to be recomputed on
                // demand, coalescing multiple updates instead of hashing for
                // each.
                self.tree_hash = None;

                // Find the node that is greater-than-or-equal-to key to descend
                // into.
                //
                // Otherwise insert this node into the high page.
                let ptr = self.nodes.partition_point(|v| *key > *v.key());

                let page = match self.nodes.get_mut(ptr) {
                    Some(v) => {
                        debug_assert!(v.key() > key);
                        v.lt_pointer_mut()
                    }
                    None => &mut self.high_page,
                };

                let page = page.get_or_insert_with(|| Box::new(Self::new(level, vec![])));
                if !page.upsert(key, level, value.clone()) {
                    insert_intermediate_page(page, key.clone(), level, value);
                }
            }
            Ordering::Equal => self.upsert_node(key, value),
            // Level is more than this page's level
            Ordering::Greater => {
                // This level is lower than the desired level, the parent is
                // higher than the desired level.
                //
                // Returning false will case the parent will insert a new page.
                return false; // No need to update the hash of this subtree
            }
        }

        // This page, or one below it was modified. Invalidate the pre-computed
        // page hash, if any.
        //
        // This marks the page as "dirty" causing the hash to be recomputed on
        // demand, coalescing multiple updates instead of hashing for each.
        self.tree_hash = None;
        true
    }

    /// Insert a node into this page, splitting any child pages as necessary.
    pub(crate) fn upsert_node(&mut self, key: &K, value: ValueDigest<N>) {
        // Find the appropriate child pointer to follow.
        let idx = self.nodes.partition_point(|v| *key > *v.key());

        // At this point the new key should be inserted has been identified -
        // node_idx points to the first node greater-than-or-equal to key.
        //
        // In this example, we're inserting the key "C":
        //
        //                                      node_idx
        //                                          ║
        //                                          ║
        //                                          ▼
        //                         ┌──────────┬──────────┐
        //                         │ LT Node  │ GTE Node │
        //                         │    A     │    E     │
        //                         └──────────┴──────────┘
        //                               │          │
        //                        ┌──────┘          │
        //                        ▼                 ▼
        //                  ┌─Page──────┐     ┌─Page──────┐
        //                  │           │     │ ┌───┬───┐ │
        //                  │ Always LT │     │ │ B │ D │ │
        //                  │  new key  │     │ └───┴───┘ │
        //                  └───────────┘     └───────────┘
        //
        // The less-than node never needs splitting, because all the keys within
        // it are strictly less than the insert key.
        //
        // The GTE child page does need splitting - all the keys less than "C"
        // need moving into the new node's less-than page.
        //
        // If the new "C" node will be inserted at the end of the node array,
        // there's no GTE node to check - instead the high page may contain
        // relevant nodes that must be split.

        let page_to_split = match self.nodes.get_mut(idx) {
            Some(n) if *n.key() == *key => {
                n.update_value_hash(value);
                return;
            }
            Some(n) => n.lt_pointer_mut(),
            None => &mut self.high_page,
        };

        // Split the higher-page, either within a GTE node or the high page.
        let mut new_lt_page = split_off_lt(page_to_split, key).map(Box::new);

        if let Some(lt_page) = &mut new_lt_page {
            debug_assert!(self.level > lt_page.level);
            debug_assert!(!lt_page.nodes.is_empty());
            debug_assert!(lt_page.max_key() < key);

            let high_page_lt = split_off_lt(&mut lt_page.high_page, key);
            let gte_page = std::mem::replace(&mut lt_page.high_page, high_page_lt.map(Box::new));
            if let Some(gte_page) = gte_page {
                debug_assert!(self.level > gte_page.level);
                debug_assert!(!gte_page.nodes.is_empty());
                debug_assert!(gte_page.max_key() > key);

                self.insert_high_page(gte_page);
            }
        }

        self.nodes
            .insert(idx, Node::new(key.clone(), value, new_lt_page));
    }
}

/// Split `page`, mutating it such that it contains only nodes with keys ordered
/// strictly-less than `key`, returning a new [`Page`] containing the
/// greater-than-or-equal-to nodes.
///
/// If splitting `page` would leave it with no nodes, it is set to [`None`].
///
/// NOTE: this only splits the page provided - it is up to the caller to split
/// any high pages as necessary.
///
/// # Panics
///
/// This method panics if attempting to split a non-empty page (root pages are
/// never split).
fn split_off_lt<const N: usize, T, K>(page: &mut Option<T>, key: &K) -> Option<Page<N, K>>
where
    K: PartialOrd,
    T: DerefMut<Target = Page<N, K>>,
{
    let mut page_ref = page.as_deref_mut()?;
    debug_assert!(!page_ref.nodes.is_empty());

    // A page should be split into two parts - one page containing the elements
    // less-than "key", and one containing parts greater-or-equal to "key".
    let partition_idx = page_ref.nodes.partition_point(|v| key > v.key());

    // All the nodes are greater-than-or-equal-to "key" - there's no less-than
    // nodes to return.
    if partition_idx == 0 {
        debug_assert!(page_ref.min_key() > key);

        // The first gte node may have a lt_pointer with nodes that are lt key.
        return split_off_lt(page_ref.nodes[0].lt_pointer_mut(), key);
    }

    // All the nodes are less than key.
    //
    // As an optimisation, simply return the existing page as the new page
    // (retaining the pre-computed hash) and invalidate the old page.
    if partition_idx == page_ref.nodes.len() {
        debug_assert!(page_ref.max_key() < key);

        // The page may have a high page, which may have nodes within the
        // (max(nodes.key), key) range
        let lt_high_nodes = split_off_lt(&mut page_ref.high_page, key);

        // Put the lt nodes back into the high page, taking the gte nodes.
        let gte_page = std::mem::replace(&mut page_ref.high_page, lt_high_nodes.map(Box::new));

        // Initialise the page we're about to return.
        let lt_page = Some(std::mem::replace(
            page_ref,
            Page::new(page_ref.level, vec![]),
        ));

        // Put the gte nodes into the input page, if any (page should contain
        // all gte nodes after this split).
        match gte_page {
            Some(p) => *page_ref = *p,
            None => *page = None,
        }

        return lt_page;
    }

    // Invalidate the page hash as at least one node will be removed.
    page_ref.tree_hash = None;

    // Obtain the set of nodes that are greater-than-or-equal-to "key".
    let gte_nodes: Vec<_> = page_ref.nodes.drain(partition_idx..).collect();
    debug_assert!(!gte_nodes.is_empty());

    // page_ref now contains the lt nodes, and a high page that may be non-empty
    // and gte than key.

    // Initialise a new page to hold the gte nodes.
    let mut gte_page = Page::new(page_ref.level, gte_nodes);
    debug_assert!(gte_page.max_key() > key);

    // Move the input high page onto the new gte page (which continues to be gte
    // than the nodes taken from the input page).
    if let Some(h) = page_ref.high_page.take() {
        debug_assert!(!h.nodes.is_empty());
        debug_assert!(h.level < page_ref.level);
        debug_assert!(h.min_key() > key);
        gte_page.insert_high_page(h);
    }

    // The first gte node may contain a lt_pointer with keys lt key, recurse
    // into it.
    let lt_key_high_nodes = split_off_lt(gte_page.nodes.first_mut().unwrap().lt_pointer_mut(), key);

    // In which case it is gte all node keys in the lt page (or it wouldn't have
    // been on the gte node).
    //
    // Add this to the new lt_page's high page next.

    // Replace the input page with the gte nodes, taking the page containing the
    // lt nodes and returning them to the caller.
    let mut lt_page = std::mem::replace(page_ref, gte_page);
    debug_assert!(!lt_page.nodes.is_empty());
    debug_assert!(lt_page.max_key() < key);

    // Insert the high page, if any.
    if let Some(h) = lt_key_high_nodes {
        debug_assert!(h.level < page_ref.level);
        debug_assert!(h.max_key() < key);
        debug_assert!(!h.nodes.is_empty());
        lt_page.insert_high_page(Box::new(h));
    }

    Some(lt_page)
}

pub(crate) fn insert_intermediate_page<const N: usize, T, K>(
    child_page: &mut T,
    key: K,
    level: u8,
    value: ValueDigest<N>,
) where
    K: PartialOrd + Clone,
    T: DerefMut<Target = Page<N, K>>,
{
    // Terminology:
    //
    //     * parent_page:
    //          top of the stack, parent of child_page
    //     * intermediate/new page:
    //          intermediate page with level between parent_page and child_page to
    //          be inserted between them.
    //     * child_page:
    //          the lower page, child of parent_page
    //

    // The child page asked this page to insert a new intermediate page at this
    // location.
    //
    //                        ┌──────────┐
    //                        │ New Root │
    //                   ┌────│    B     │─────┐         Level N
    //                   │    └──────────┘     │
    //              lt_pointer            high_page
    //                   │                     │
    //                   │                     │
    //          ┌ ─ ─ ─ ─│─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─│─ ─ ─ ─ ─ ─ ─ ─ ─ ┐
    //             ┌─────▼────┐          ┌─────▼────┐
    //          │  │ LT Node  │          │ GTE Node │  Child Page │
    //             │    A     │          │    C     │     Level 0
    //          │  └──────────┘          └──────────┘             │
    //           ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─
    //
    // The child page must be split into nodes less-than key, and those
    // greater-than-or-equal to key to preserve the ordering once this new page
    // containing key is inserted. Both halves must be linked into the new page.

    debug_assert!(child_page.level() < level);
    debug_assert!(!child_page.nodes.is_empty());

    // Create the new node.
    let node = Node::new(key.clone(), value, None);

    // Create the new intermediate page, between the parent page and the child
    // page.
    let mut intermediate_page = Page::new(level, vec![node]);

    // Split the child page into (less-than, greater-than) pages, split at the
    // point where key would reside.
    //
    // NOTE: this may leave "page" empty if all the nodes moved to the lt page.
    let mut lt_page = {
        let child_page2 = child_page.deref_mut();
        let mut child_page_ref = Some(&mut *child_page2);
        split_off_lt(&mut child_page_ref, &key)
    };

    // If all the nodes moved out of the child_page and into lt_page it
    // indicates that all nodes had keys less-than the new key, meaning there
    // may be nodes in the lt_page high page that need splitting, as it may
    // contain values between max(lt_page.nodes) and key.
    //
    // For example, when inserting 4:
    //
    //                              ┌ ─ ─ ─ ─ ─ ─ ─ ─ ─
    //                                ┌───┐ New Parent │
    //                           ┌──│ │ 4 │    Level 2
    //                           │    └───┘            │
    //                           │  └ ─ ─ ─ ─ ─ ─ ─ ─ ─
    //                           │
    //                ┌ ─ ─ ─ ─ ─│─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─
    //                   ┌───┬───▼───────┐  Child Page │
    //                │  │ 1 │ 2 │ high  │     Level 1
    //                   └───┴───┴───────┘             │
    //                └ ─ ─ ─ ─ ─ ─ ─│─ ─ ─ ─ ─ ─ ─ ─ ─
    //                               │
    //                           ┌ ─ ▼ ─ ─ ─ ─ ─ ─ ─ ─ ┐
    //                             ┌───┬───┐
    //                           │ │ 3 │ 5 │   Level 0 │
    //                             └───┴───┘
    //                           └ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ┘
    //
    // The existing entry of 5 must be moved, as it is greater than the new
    // parent:
    //
    //                              ┌ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─
    //                                            New Parent │
    //                              │ ┌───┬───────┐  Level 2
    //                            ┌───│ 4 │ high  │───┐      │
    //                            │ │ └───┴───────┘   │
    //                            │  ─ ─ ─ ─ ─ ─ ─ ─ ─│─ ─ ─ ┘
    //                            ▼                   │
    //           ┌ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─    │
    //              ┌───┬───┬───────┐  Child Page │   │
    //           │  │ 1 │ 2 │ high  │     Level 1     │
    //              └───┴───┴───────┘             │   │
    //           └ ─ ─ ─ ─ ─ ─ ─│─ ─ ─ ─ ─ ─ ─ ─ ─    │
    //                          ▼                     ▼
    //                  ┌ ─ ─ ─ ─ ─ ─ ─       ┌ ─ ─ ─ ─ ─ ─ ─
    //                   ┌───┐         │       ┌───┐         │
    //                  ││ 3 │ Level 0        ││ 5 │ Level 0
    //                   └───┘         │       └───┘         │
    //                  └ ─ ─ ─ ─ ─ ─ ─       └ ─ ─ ─ ─ ─ ─ ─
    //
    // To do this, we split the high page, attaching the lt_nodes to the lt_page
    // created above, and attach the remaining gte_nodes to the high_page of the
    // intermediate_page.
    if let Some(lt_page) = &mut lt_page {
        debug_assert!(level > lt_page.level);
        debug_assert!(!lt_page.nodes.is_empty());
        debug_assert!(*lt_page.max_key() < key);

        let high_page_lt = split_off_lt(&mut lt_page.high_page, &key);
        let gte_page = std::mem::replace(&mut lt_page.high_page, high_page_lt.map(Box::new));
        if let Some(gte_page) = gte_page {
            debug_assert!(level > gte_page.level);
            debug_assert!(!gte_page.nodes.is_empty());
            debug_assert!(*gte_page.max_key() > key);

            intermediate_page.insert_high_page(gte_page);
        }
    }

    // Replace the page pointer at this level to point to the new page, taking
    // the page that now contains the lt nodes after the split.
    let gte_page = std::mem::replace(child_page.deref_mut(), intermediate_page);

    // At this point, we have this structure:
    //
    //                         ┌─────────────┐
    //                         │  This Page  │
    //                         └─────────────┘
    //                                │
    //                                ▼
    //                      ┌───────────────────┐
    //                      │ Intermediate Page │
    //                      └───────────────────┘
    //
    // The lt_page and gtw_pages need linking into the new node within the new
    // intermediate page.

    *child_page.nodes[0].lt_pointer_mut() = lt_page.map(Box::new);
    if !gte_page.nodes.is_empty() {
        debug_assert!(*gte_page.max_key() > key);
        debug_assert!(level > gte_page.level);
        child_page.high_page = Some(Box::new(gte_page));
    }
}

#[cfg(test)]
mod tests {
    use assert_matches::assert_matches;

    use super::*;
    use crate::{assert_tree, digest::Digest};

    const MOCK_VALUE: ValueDigest<1> = ValueDigest::new(Digest::new([0; 1]));
    const MOCK_PAGE_HASH: PageDigest = PageDigest::new(Digest::new([0; 16]));

    #[test]
    #[should_panic(expected = "!page_ref.nodes.is_empty()")]
    fn test_split_page_empty() {
        let mut gte_page = Some(Box::new(Page::<1, _>::new(42, vec![])));
        let _lt_page = split_off_lt(&mut gte_page, &5);
    }

    #[test]
    fn test_split_page_single_node_lt() {
        let mut gte_page = Some(Box::new(Page::new(
            42,
            vec![Node::new(2, MOCK_VALUE, None)],
        )));

        gte_page.as_mut().unwrap().tree_hash = Some(MOCK_PAGE_HASH);

        let lt_page = split_off_lt(&mut gte_page, &5);
        assert_matches!(gte_page, None);

        assert_matches!(lt_page, Some(p) => {
            assert_eq!(p.level, 42);

            // The unmodified page has the hash retained.
            assert_eq!(p.tree_hash, Some(MOCK_PAGE_HASH));

            assert_eq!(p.nodes, [
                Node::new(2, MOCK_VALUE, None),
            ]);
        });
    }

    #[test]
    fn test_split_page_single_node_gt() {
        let mut gte_page = Some(Box::new(Page::new(
            42,
            vec![Node::new(2, MOCK_VALUE, None)],
        )));

        gte_page.as_mut().unwrap().tree_hash = Some(MOCK_PAGE_HASH);

        let lt_page = split_off_lt(&mut gte_page, &1);
        assert_matches!(gte_page, Some(p) => {
            assert_eq!(p.level, 42);

            // The unmodified page has the hash retained.
            assert_eq!(p.tree_hash, Some(MOCK_PAGE_HASH));

            assert_eq!(p.nodes, [
                Node::new(2, MOCK_VALUE, None),
            ]);
        });

        assert_matches!(lt_page, None);
    }

    #[test]
    fn test_split_page_eq() {
        let mut gte_page = Some(Box::new(Page::new(
            42,
            vec![
                Node::new(1, MOCK_VALUE, None),
                Node::new(2, MOCK_VALUE, None),
                Node::new(4, MOCK_VALUE, None),
            ],
        )));

        gte_page.as_mut().unwrap().tree_hash = Some(MOCK_PAGE_HASH);

        let lt_page = split_off_lt(&mut gte_page, &2);
        assert_matches!(gte_page, Some(p) => {
            assert_eq!(p.level, 42);
            assert_eq!(p.tree_hash, None);

            assert_eq!(p.nodes, [
                Node::new(2, MOCK_VALUE, None),
                Node::new(4, MOCK_VALUE, None)
            ]);
        });

        assert_matches!(lt_page, Some(p) => {
            assert_eq!(p.level, 42);

            // The modified page has the hash invalidated.
            assert_eq!(p.tree_hash, None);

            assert_eq!(p.nodes, [
                Node::new(1, MOCK_VALUE, None),
            ]);
        });
    }

    #[test]
    fn test_split_page_lt() {
        let mut gte_page = Some(Box::new(Page::new(
            42,
            vec![
                Node::new(1, MOCK_VALUE, None),
                Node::new(2, MOCK_VALUE, None),
                Node::new(4, MOCK_VALUE, None),
            ],
        )));

        gte_page.as_mut().unwrap().tree_hash = Some(MOCK_PAGE_HASH);

        let lt_page = split_off_lt(&mut gte_page, &3);
        assert_matches!(gte_page, Some(p) => {
            assert_eq!(p.level, 42);
            assert_eq!(p.tree_hash, None);

            assert_eq!(p.nodes, [
                Node::new(4, MOCK_VALUE, None)
            ]);
        });

        assert_matches!(lt_page, Some(p) => {
            assert_eq!(p.level, 42);

            // The modified page has the hash invalidated.
            assert_eq!(p.tree_hash, None);

            assert_eq!(p.nodes, [
                Node::new(1, MOCK_VALUE, None),
                Node::new(2, MOCK_VALUE, None),
            ]);
        });
    }

    #[test]
    fn test_split_page_all_gt() {
        let mut gte_page = Some(Box::new(Page::new(
            42,
            vec![
                Node::new(1, MOCK_VALUE, None),
                Node::new(2, MOCK_VALUE, None),
                Node::new(4, MOCK_VALUE, None),
            ],
        )));

        gte_page.as_mut().unwrap().tree_hash = Some(MOCK_PAGE_HASH);

        let lt_page = split_off_lt(&mut gte_page, &0);
        assert_matches!(gte_page, Some(p) => {
            assert_eq!(p.level, 42);

            // The new page containing all the nodes retains the pre-computed
            // hash.
            assert_eq!(p.tree_hash, Some(MOCK_PAGE_HASH));

            assert_eq!(p.nodes, [
                Node::new(1, MOCK_VALUE, None),
                Node::new(2, MOCK_VALUE, None),
                Node::new(4, MOCK_VALUE, None),
            ]);
        });

        assert_matches!(lt_page, None);
    }

    #[test]
    fn test_split_page_all_lt() {
        let mut gte_page = Some(Box::new(Page::new(
            42,
            vec![
                Node::new(1, MOCK_VALUE, None),
                Node::new(2, MOCK_VALUE, None),
                Node::new(4, MOCK_VALUE, None),
            ],
        )));

        gte_page.as_mut().unwrap().tree_hash = Some(MOCK_PAGE_HASH);

        let lt_page = split_off_lt(&mut gte_page, &10);
        assert_matches!(gte_page, None);

        assert_matches!(lt_page, Some(p) => {
            assert_eq!(p.level, 42);

            // The unmodified page retains the pre-computed hash.
            assert_eq!(p.tree_hash, Some(MOCK_PAGE_HASH));

            assert_eq!(p.nodes, [
                Node::new(1, MOCK_VALUE, None),
                Node::new(2, MOCK_VALUE, None),
                Node::new(4, MOCK_VALUE, None),
            ]);
        });
    }

    #[test]
    fn test_upsert_less_than_split_child() {
        let mut p = Page::new(1, vec![Node::new(4, MOCK_VALUE, None)]);

        p.upsert(&3, 0, MOCK_VALUE);
        p.upsert(&1, 0, MOCK_VALUE);
        p.upsert(&2, 1, MOCK_VALUE);

        assert_tree!(page = p);
    }

    #[test]
    fn test_split_page_recursive_lt_pointer() {
        let mut lt_pointer_page = Page::new(52, vec![Node::new(86, MOCK_VALUE, None)]);
        lt_pointer_page.tree_hash = Some(MOCK_PAGE_HASH);

        let mut root = Box::new(Page::new(
            42,
            vec![Node::new(161, MOCK_VALUE, Some(Box::new(lt_pointer_page)))],
        ));
        root.tree_hash = Some(MOCK_PAGE_HASH);

        let key = 160;

        let mut root = Some(root);
        let lt_page = split_off_lt(&mut root, &key);

        assert_matches!(lt_page, Some(p) => {
            assert_eq!(p.level, 52);
            assert_matches!(p.nodes(), [n] if *n.key() == 86)
        });
    }

    #[test]
    fn test_split_page_recursive_high_page() {
        let mut high_page = Page::new(32, vec![Node::new(44, MOCK_VALUE, None)]);
        high_page.tree_hash = Some(MOCK_PAGE_HASH);

        let mut root = Box::new(Page::new(42, vec![Node::new(42, MOCK_VALUE, None)]));
        root.tree_hash = Some(MOCK_PAGE_HASH);
        root.insert_high_page(Box::new(high_page));

        let key = 43;

        let mut root = Some(root);
        let lt_page = split_off_lt(&mut root, &key);

        assert_matches!(lt_page, Some(p) => {
            assert_eq!(p.level, 42);
            assert_matches!(p.nodes(), [n] if *n.key() == 42)
        });
        assert_matches!(root, Some(p) => {
            assert_eq!(p.level, 32);
            assert_matches!(p.nodes(), [n] if *n.key() == 44)
        });
    }
}
