//! Tree difference calculation algorithm & associated types.

mod diff_builder;
mod page_range;
mod page_range_snapshot;
mod range_list;

use std::{fmt::Debug, iter::Peekable};

pub use page_range::*;
pub use page_range_snapshot::*;

use crate::diff::diff_builder::DiffListBuilder;

/// An inclusive range of keys that differ between two serialised ordered sets
/// of [`PageRange`].
#[derive(Debug, PartialEq)]
pub struct DiffRange<'a, K> {
    /// The inclusive start & end key bounds of this range to sync.
    start: &'a K,
    end: &'a K,
}

impl<'a, K> Clone for DiffRange<'a, K> {
    fn clone(&self) -> Self {
        Self {
            start: self.start,
            end: self.end,
        }
    }
}

impl<'a, K> DiffRange<'a, K> {
    /// Returns true if the range within `self` overlaps any portion of the
    /// range within `p`.
    pub(crate) fn overlaps(&self, p: &Self) -> bool
    where
        K: PartialOrd,
    {
        p.end() >= self.start() && p.start() <= self.end()
    }

    /// Returns the inclusive start of this [`DiffRange`], identifying the start
    /// of an inconsistency between trees.
    pub fn start(&self) -> &K {
        self.start
    }

    /// Returns the inclusive end of this [`DiffRange`], identifying the end of
    /// an inconsistency between trees.
    pub fn end(&self) -> &K {
        self.end
    }
}

/// Compute the difference between `local` and `peer`, returning the set of
/// [`DiffRange`] covering the inconsistent key ranges found in `peer`.
///
/// ```rust
/// use merkle_search_tree::{MerkleSearchTree, diff::diff};
///
/// // Initialise a "peer" tree.
/// let mut node_a = MerkleSearchTree::default();
/// node_a.upsert("bananas", &42);
/// node_a.upsert("plátanos", &42);
///
/// // Initialise the "local" tree with differing keys
/// let mut node_b = MerkleSearchTree::default();
/// node_b.upsert("donkey", &42);
///
/// // Generate the tree hashes before serialising the page ranges
/// node_a.root_hash();
/// node_b.root_hash();
///
/// // Generate the tree page bounds & hashes, and feed into the diff function
/// let diff_range = diff(
///     node_b.serialise_page_ranges().unwrap().into_iter(),
///     node_a.serialise_page_ranges().unwrap().into_iter(),
/// );
///
/// // The diff_range contains all the inclusive key intervals the "local" tree
/// // should fetch from the "peer" tree to converge.
/// assert_matches::assert_matches!(diff_range.as_slice(), [range] => {
///     assert_eq!(range.start(), &"bananas");
///     assert_eq!(range.end(), &"plátanos");
/// });
/// ```
///
/// # State Convergence
///
/// To converge the state of the two trees, the key ranges in the returned
/// [`DiffRange`] instances should be requested from `peer` and used to update
/// the state of `local`.
///
/// If `local` is a superset of `peer` (contains all the keys in `peer` and the
/// values are consistent), or the two trees are identical, no [`DiffRange`]
/// intervals are returned.
///
/// # Termination
///
/// A single invocation to [`diff()`] always terminates, and completes in `O(n)`
/// time and space. Inconsistent page ranges (if any) are minimised in
/// `O(n_consistent * n_inconsistent)` time and `O(n)` space.
///
/// In the absence of further external updates to either tree, this algorithm
/// terminates (leaving `local` and `peer` fully converged) and no diff is
/// returned within a finite number of sync rounds between the two trees.
///
/// If a one-way sync is performed (pulling inconsistent keys from `peer` and
/// updating `local`, but never syncing the other way around) this algorithm MAY
/// NOT terminate.
pub fn diff<'p, 'a: 'p, T, U, K>(local: T, peer: U) -> Vec<DiffRange<'p, K>>
where
    T: IntoIterator<Item = PageRange<'a, K>>,
    U: IntoIterator<Item = PageRange<'p, K>>,
    K: PartialOrd + Ord + Debug + 'p + 'a,
{
    let local = local.into_iter();
    let peer = peer.into_iter();

    // Any two merkle trees can be expressed as a series of overlapping page
    // ranges, either consistent in content (hashes match), or inconsistent
    // (hashes differ).
    //
    // This algorithm builds two sets of intervals - one for key ranges that are
    // fully consistent between the two trees, and one for inconsistent ranges.
    //
    // This DiffListBuilder helps construct these lists, and merges them into a
    // final, non-overlapping, deduplicated, and minimised set of ranges that
    // are inconsistent between trees as described above.
    let mut diff_builder = DiffListBuilder::default();

    let mut local = local.peekable();
    let mut peer = peer.peekable();

    debug!("calculating diff");

    let root = match peer.peek() {
        Some(v) => v.clone(),
        None => return vec![],
    };

    recurse_diff(&root, &mut peer, &mut local, &mut diff_builder);

    diff_builder.into_diff_vec()
}

#[cfg_attr(any(test, feature = "tracing"), tracing::instrument(skip(peer, local)))]
fn recurse_subtree<'p, 'a: 'p, T, U, K>(
    subtree_root: &PageRange<'p, K>,
    peer: &mut Peekable<U>,
    local: &mut Peekable<T>,
    diff_builder: &mut DiffListBuilder<'p, K>,
) -> bool
where
    T: Iterator<Item = PageRange<'a, K>>,
    U: Iterator<Item = PageRange<'p, K>>,
    K: PartialOrd + Ord + Debug + 'p + 'a,
{
    // Recurse into the subtree, which will exit immediately if the next value
    // in peer is not rooted at subtree_root (without consuming the iter value).
    recurse_diff(subtree_root, peer, local, diff_builder);

    // Invariant - when returning from this call, the entire subtree rooted at
    // the peer_subtree_root should have been evaluated and the next peer page
    // (if any) escapes the subtree.

    while let Some(p) = peer.next_if(|v| subtree_root.is_superset_of(v)) {
        debug!(
            peer_page=?p,
            "requesting unevaluated subtree page"
        );
        // Add all the un-evaluated peer sub-tree pages to the sync list.
        diff_builder.inconsistent(p.start(), p.end());
    }

    debug_assert!(peer
        .peek()
        .map(|v| !subtree_root.is_superset_of(v))
        .unwrap_or(true));

    true
}

#[cfg_attr(any(test, feature = "tracing"), tracing::instrument(skip(peer, local)))]
fn recurse_diff<'p, 'a: 'p, T, U, K>(
    subtree_root: &PageRange<'p, K>,
    peer: &mut Peekable<U>,
    local: &mut Peekable<T>,
    diff_builder: &mut DiffListBuilder<'p, K>,
) where
    T: Iterator<Item = PageRange<'a, K>>,
    U: Iterator<Item = PageRange<'p, K>>,
    K: PartialOrd + Ord + Debug + 'p + 'a,
{
    // The last visited peer page, if any.
    let mut last_p = None;

    // Process this subtree, descending down inconsistent paths recursively, and
    // iterating through the tree.
    loop {
        let p = match maybe_advance_within(subtree_root, peer) {
            Some(v) => v,
            None => {
                trace!("no more peer pages in subtree");
                return;
            }
        };

        let mut l = match maybe_advance_within(&p, local) {
            Some(v) => v,
            None => {
                // If the local subtree range is a superset of the peer subtree
                // range, the two are guaranteed to be inconsistent due to the
                // local node containing more keys (potentially the sole cause
                // of that inconsistency).
                //
                // Fetching any pages from the less-up-to-date peer may be
                // spurious, causing no useful advancement of state.
                if let Some(local) = local.peek() {
                    if local.is_superset_of(&p) {
                        trace!(
                            peer_page=?p,
                            local_page=?local,
                            "local page is a superset of peer"
                        );
                        return;
                    }
                }

                // If there's no matching local page that overlaps with p, then
                // there must be be one or more keys to be synced from the peer
                // to populate the missing local pages.
                //
                // Request the range starting from the end of the last checked p
                // (last_p), or the start of the subtree_root if none.
                let start = last_p
                    .as_ref()
                    .map(|v: &PageRange<'_, K>| v.end())
                    .unwrap_or(subtree_root.start());
                // And end at the next local page key, or the page end.
                //
                // Any pages missing between p.end and the end of this subtree
                // will be added by the caller (recurse_subtree).
                let end = local
                    .peek()
                    .map(|v| v.start().min(p.end()))
                    .unwrap_or(p.end());
                if end >= start {
                    debug!(
                        peer_page=?p,
                        "no more local pages in subtree - requesting missing page ranges"
                    );
                    diff_builder.inconsistent(start, end);
                } else {
                    trace!(
                        peer_page=?p,
                        "no more local pages in subtree"
                    );
                }

                return;
            }
        };

        last_p = Some(p.clone());

        // Never escape the subtree rooted at p_parent.
        //
        // Disable for fuzzing to test with fully random inputs.
        #[cfg(not(fuzzing))]
        debug_assert!(subtree_root.is_superset_of(&p));

        trace!(
            peer_page=?p,
            local_page=?l,
            "visit page"
        );

        // Advance the local cursor to minimise the comparable range, in turn
        // minimising the sync range.
        while let Some(v) = local.next_if(|v| v.is_superset_of(&p)) {
            trace!(
                peer_page=?p,
                skip_local_page=?l,
                local_page=?v,
                "shrink local diff range"
            );
            l = v;
        }

        if l.hash() == p.hash() {
            debug!(
                peer_page=?p,
                local_page=?l,
                "hash match - consistent page"
            );

            // Record this page as fully consistent.
            diff_builder.consistent(p.start(), p.end());

            // Skip visiting the pages in the subtree rooted at the current
            // page: they're guaranteed to be consistent due to the consistent
            // parent hash.
            skip_subtree(&p, peer);
        } else {
            debug!(
                peer_page=?p,
                local_page=?l,
                "hash mismatch"
            );

            diff_builder.inconsistent(p.start(), p.end());
        }

        // Evaluate the sub-tree, causing all the (consistent) child ranges to
        // be added to the consistent list to, shrink this inconsistent range
        // (or simply advancing through the subtree if this page is consistent).
        recurse_subtree(&p, peer, local, diff_builder);
    }
}

/// Return the next [`PageRange`] if it is part of the sub-tree rooted at
/// `parent`.
fn maybe_advance_within<'a, 'p, K, T>(
    parent: &PageRange<'p, K>,
    cursor: &mut Peekable<T>,
) -> Option<PageRange<'a, K>>
where
    T: Iterator<Item = PageRange<'a, K>>,
    K: PartialOrd + 'a,
{
    if cursor
        .peek()
        .map(|p| !parent.is_superset_of(p))
        .unwrap_or_default()
    {
        return None;
    }

    cursor.next()
}

/// Advance `iter` to the next page that does not form part of the subtree
/// rooted at the given `subtree_root`.
#[inline(always)]
fn skip_subtree<'p, T, K>(subtree_root: &PageRange<'p, K>, iter: &mut Peekable<T>)
where
    T: Iterator<Item = PageRange<'p, K>>,
    K: PartialOrd + Ord + Debug + 'p,
{
    while iter.next_if(|v| subtree_root.is_superset_of(v)).is_some() {}
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use assert_matches::assert_matches;
    use proptest::prelude::*;

    use super::*;
    use crate::{
        digest::PageDigest,
        test_util::{IntKey, Node},
    };

    const fn new_digest(lsb: u8) -> PageDigest {
        PageDigest::new([0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, lsb])
    }

    macro_rules! test_page_is_superset_of {
        (
			$name:ident,
			a = [$a_start:expr, $a_end:expr],
			b = [$b_start:expr, $b_end:expr],
			a_is_parent = $want:expr // Should a.contains(b) be true?
		) => {
            paste::paste! {
                #[test]
                fn [<test_page_is_superset_of_ $name>]() {
                    let a = PageRange::new(&$a_start, $a_end, new_digest(42));
                    let b = PageRange::new(&$b_start, $b_end, new_digest(42));

                    assert!(a.is_superset_of(&b) == $want);
                }
            }
        };
    }

    test_page_is_superset_of!(inclusive, a = [1, &10], b = [1, &10], a_is_parent = true);

    test_page_is_superset_of!(full, a = [1, &10], b = [2, &9], a_is_parent = true);

    test_page_is_superset_of!(start, a = [2, &10], b = [1, &9], a_is_parent = false);

    test_page_is_superset_of!(end, a = [1, &8], b = [2, &9], a_is_parent = false);

    test_page_is_superset_of!(outside, a = [1, &10], b = [0, &11], a_is_parent = false);

    // Tests below model this tree:
    //
    //                          ┌ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ┐
    //                            ┌───┬───┬───────┐
    //                          │ │ 7 │11 │ high  │ Level 2 │
    //                            └───┴───┴───────┘
    //                          └ ─ ┬ ─ ─ ─ ─ ┬ ─ ─ ─ ─ ─ ─ ┘
    //                         ┌────┘         └─────┐
    //                         ▼                    ▼
    //             ┌ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─ ─  ┌ ─ ─ ─ ─ ─ ─ ─ ┐
    //               ┌───┬───┬───┐        │   ┌───┐
    //             │ │ 3 │ 4 │ 6 │Level 1   │ │15 │ Level 1 │
    //               └───┴───┴───┘        │   └───┘
    //             └ ─ ┬ ─ ─ ─ ┬ ─ ─ ─ ─ ─  └ ─ ─ ─ ─ ─ ─ ─ ┘
    //             ┌───┘       └─────┐
    //             ▼                 ▼
    //     ┌ ─ ─ ─ ─ ─ ─ ─ ┐ ┌ ─ ─ ─ ─ ─ ─ ─ ┐
    //       ┌───┐             ┌───┐
    //     │ │ 2 │ Level 0 │ │ │ 5 │ Level 0 │
    //       └───┘             └───┘
    //     └ ─ ─ ─ ─ ─ ─ ─ ┘ └ ─ ─ ─ ─ ─ ─ ─ ┘

    #[test]
    fn test_no_diff() {
        enable_logging!();

        let local = vec![
            PageRange::new(&2, &15, new_digest(1)),
            PageRange::new(&2, &6, new_digest(2)),
            PageRange::new(&2, &2, new_digest(3)),
            PageRange::new(&5, &5, new_digest(4)),
            PageRange::new(&15, &15, new_digest(5)),
        ];

        let peer = local.clone();

        assert_matches!(diff(local, peer).as_slice(), []);
    }

    #[test]
    fn test_diff_peer_missing_last_page() {
        enable_logging!();

        let local = vec![
            PageRange::new(&2, &15, new_digest(1)),
            PageRange::new(&2, &6, new_digest(2)),
            PageRange::new(&2, &2, new_digest(3)),
            PageRange::new(&5, &5, new_digest(4)),
            PageRange::new(&15, &15, new_digest(5)),
        ];

        let mut peer = local.clone();

        // Remove the last page
        let _ = peer.pop().unwrap();

        // Invalidate the root/parent and update the peer root range to reflect
        // the missing last page
        peer[0] = PageRange::new(peer[0].start(), &11, new_digest(42));

        // Nothing to ask for - the peer is behind
        assert_matches!(diff(local, peer).as_slice(), []);
    }

    #[test]
    fn test_diff_local_missing_last_page() {
        enable_logging!();

        let mut local = vec![
            PageRange::new(&2, &15, new_digest(1)),
            PageRange::new(&2, &6, new_digest(2)),
            PageRange::new(&2, &2, new_digest(3)),
            PageRange::new(&5, &5, new_digest(4)),
            PageRange::new(&15, &15, new_digest(5)),
        ];

        let peer = local.clone();

        // Remove the last page
        let _ = local.pop().unwrap();

        // Invalidate the root/parent and update the local root range to reflect
        // the missing last page
        local[0] = PageRange::new(local[0].start(), &11, new_digest(42));

        assert_matches!(
            diff(local, peer).as_slice(),
            [DiffRange { start: 6, end: 15 }]
        );
    }

    /// The peer is missing a child page.
    ///
    /// This means the local tree has an inconsistent hash for the
    /// missing-child's parent, causing it to request the full range between the
    /// end of it and the next consistent hash (an empty sync range).
    #[test]
    fn test_diff_peer_missing_leaf_page() {
        enable_logging!();

        let local = vec![
            PageRange::new(&2, &15, new_digest(1)),
            PageRange::new(&2, &6, new_digest(2)),
            PageRange::new(&2, &2, new_digest(3)),
            PageRange::new(&5, &5, new_digest(4)),
            PageRange::new(&15, &15, new_digest(5)),
        ];

        let peer = vec![
            PageRange::new(
                &3, // Differs
                &15,
                new_digest(42), // Differs
            ),
            PageRange::new(
                &3, // Differs
                &6,
                new_digest(43), // Differs
            ),
            //
            // No page containing 2 at level 0
            PageRange::new(&5, &5, new_digest(4)),
            PageRange::new(&15, &15, new_digest(5)),
        ];

        assert_matches!(diff(local, peer).as_slice(), []);
    }

    #[test]
    fn test_diff_local_missing_leaf_page() {
        enable_logging!();

        let local = vec![
            PageRange::new(
                &3, // Differs
                &15,
                new_digest(42), // Differs
            ),
            PageRange::new(
                &3, // Differs
                &6,
                new_digest(43), // Differs
            ),
            //
            // No page containing 2 at level 0
            PageRange::new(&5, &5, new_digest(4)),
            PageRange::new(&15, &15, new_digest(5)),
        ];

        let peer = vec![
            PageRange::new(&2, &15, new_digest(1)),
            PageRange::new(&2, &6, new_digest(2)),
            PageRange::new(&2, &2, new_digest(3)),
            PageRange::new(&5, &5, new_digest(4)),
            PageRange::new(&15, &15, new_digest(5)),
        ];

        assert_matches!(
            diff(local, peer).as_slice(),
            [DiffRange { start: 2, end: 15 }]
        );
    }

    #[test]
    fn test_diff_local_missing_subtree() {
        enable_logging!();

        let local = vec![
            PageRange::new(
                &3,
                &15,
                new_digest(42), // Differs
            ),
            PageRange::new(&15, &15, new_digest(5)),
        ];

        let peer = vec![
            PageRange::new(&2, &15, new_digest(1)),
            PageRange::new(&2, &6, new_digest(2)),
            PageRange::new(&2, &2, new_digest(3)),
            PageRange::new(&5, &5, new_digest(4)),
            PageRange::new(&15, &15, new_digest(5)),
        ];

        assert_matches!(
            diff(local, peer).as_slice(),
            [DiffRange { start: 2, end: 15 }]
        );
    }

    #[test]
    fn test_diff_peer_missing_subtree() {
        enable_logging!();

        let local = vec![
            PageRange::new(&2, &15, new_digest(1)),
            PageRange::new(&2, &6, new_digest(2)),
            PageRange::new(&2, &2, new_digest(3)),
            PageRange::new(&5, &5, new_digest(4)),
            PageRange::new(&15, &15, new_digest(5)),
        ];

        let peer = vec![
            PageRange::new(
                &3,
                &15,
                new_digest(42), // Differs
            ),
            PageRange::new(&15, &15, new_digest(5)),
        ];

        assert_matches!(diff(local, peer).as_slice(), []);
    }

    #[test]
    fn test_diff_leaf_page_hash() {
        enable_logging!();

        let peer = vec![
            PageRange::new(
                &2,
                &15,
                new_digest(42), // Differs
            ),
            PageRange::new(
                &2,
                &6,
                new_digest(42), // Differs
            ),
            PageRange::new(&2, &2, new_digest(3)),
            PageRange::new(&5, &5, new_digest(4)),
            PageRange::new(&15, &15, new_digest(5)),
        ];

        let local = vec![
            PageRange::new(&2, &15, new_digest(1)),
            PageRange::new(&2, &6, new_digest(2)),
            PageRange::new(&2, &2, new_digest(3)),
            PageRange::new(&5, &5, new_digest(4)),
            PageRange::new(&15, &15, new_digest(5)),
        ];

        assert_matches!(
            diff(local, peer).as_slice(),
            // Range (3,6) is optimal, but this gets the job done.
            [DiffRange { start: 2, end: 15 }]
        );
    }

    #[test]
    fn test_diff_peer_extra_key_last_page() {
        enable_logging!();

        let local = vec![
            PageRange::new(&2, &15, new_digest(1)),
            PageRange::new(&2, &6, new_digest(2)),
            PageRange::new(&2, &2, new_digest(3)),
            PageRange::new(&5, &5, new_digest(4)),
            PageRange::new(&15, &15, new_digest(5)),
        ];

        let mut peer = local.clone();
        let end = peer.last_mut().unwrap();
        *end = PageRange::new(end.start(), &16, new_digest(42));

        // Root hash differs to reflect differing child
        peer[0] = PageRange::new(peer[0].start(), &16, new_digest(42));

        assert_matches!(
            diff(local, peer).as_slice(),
            [DiffRange { start: 6, end: 16 }]
        );
    }

    #[test]
    fn test_diff_root_page_hash() {
        enable_logging!();

        let local = vec![
            PageRange::new(&2, &15, new_digest(1)),
            PageRange::new(&2, &6, new_digest(2)),
            PageRange::new(&2, &2, new_digest(3)),
            PageRange::new(&5, &5, new_digest(4)),
            PageRange::new(&15, &15, new_digest(5)),
        ];

        let mut peer = local.clone();

        // Root hash differs due to added key 8
        peer[0] = PageRange::new(peer[0].start(), peer[0].end(), new_digest(42));

        // Without the reduce_sync_range optimisation, this root inconsistency
        // would cause a fetch against the whole tree (start: 2, end: 15).
        //
        // Instead, the known-good sub-tree pages can be removed from the sync
        // range.
        assert_matches!(
            diff(local, peer).as_slice(),
            [DiffRange { start: 6, end: 15 }]
        );
    }

    #[test]
    fn test_diff_peer_intermediate_bounds() {
        enable_logging!();

        // This breaks the convention of the same tree being used, and instead
        // pushes 7 down into level 1.
        //
        // It appears in the peer only.

        let local = vec![
            PageRange::new(&2, &15, new_digest(1)),
            PageRange::new(&2, &6, new_digest(2)),
            PageRange::new(&2, &2, new_digest(3)),
            PageRange::new(&5, &5, new_digest(4)),
            PageRange::new(&15, &15, new_digest(5)),
        ];

        let mut peer = local.clone();

        // Root hash differs due to added key 8
        peer[1] = PageRange::new(peer[1].start(), &7, new_digest(42));

        peer[0] = PageRange::new(peer[0].start(), peer[0].end(), new_digest(42));

        assert_matches!(
            diff(local, peer).as_slice(),
            [DiffRange { start: 2, end: 15 }]
        );
    }

    #[test]
    fn test_diff_peer_intermediate_bounds_and_inconsistent_subtree_leaf() {
        enable_logging!();

        // This breaks the convention of the same tree being used, and instead
        // pushes 7 down into level 1.
        //
        // It appears in the peer only, and additionally the value of 2 is
        // modified.

        let local = vec![
            PageRange::new(&2, &15, new_digest(1)),
            PageRange::new(&2, &6, new_digest(2)),
            PageRange::new(&2, &2, new_digest(3)),
            PageRange::new(&5, &5, new_digest(4)),
            PageRange::new(&15, &15, new_digest(5)),
        ];

        let mut peer = local.clone();

        // Extend key range of 1st child to 2-6 to 2-7
        peer[1] = PageRange::new(peer[1].start(), &7, new_digest(42));

        // Key 2 value change
        peer[2] = PageRange::new(peer[2].start(), peer[2].end(), new_digest(42));

        // Root hash
        peer[0] = PageRange::new(peer[0].start(), peer[0].end(), new_digest(42));

        assert_matches!(
            diff(local, peer.clone()).as_slice(),
            [DiffRange { start: 2, end: 15 }]
        );

        let mut local = peer.clone();

        // Only 2 should remain different - reset the hash.
        local[2] = PageRange::new(local[2].start(), local[2].end(), new_digest(3));
        peer[1] = PageRange::new(peer[1].start(), peer[1].end(), new_digest(2));
        peer[0] = PageRange::new(peer[0].start(), peer[0].end(), new_digest(1));

        // 2, 15 because the root page is inconsistent and there's no consistent
        // pages that shrink the range.
        assert_matches!(
            diff(local, peer).as_slice(),
            [DiffRange { start: 2, end: 15 }]
        );
    }

    /// Construct a test where a child page is inconsistent and should not call
    /// recurse_diff() as there's no subtree to evaluate.
    ///
    /// Additionally another child page is also inconsistent but skipped because
    /// the local node has a larger key range than the peer.
    #[test]
    fn test_child_page_inconsistent_no_subtree_recurse() {
        enable_logging!();

        let local = vec![
            PageRange::new(&0, &17995215864353464453_usize, new_digest(1)),
            PageRange::new(&0, &1331283967702353742, new_digest(2)),
            PageRange::new(
                &2425302987964992968,
                &3632803506728089373, // Larger key range than peer
                new_digest(3),
            ),
            PageRange::new(
                &4706903583207578752, // Shorter key range than peer (missing first key)
                &4707132771120484774,
                new_digest(4),
            ),
            PageRange::new(&17995215864353464453, &17995215864353464453, new_digest(5)),
        ];
        let peer = vec![
            PageRange::new(
                &0,
                &17995215864353464453_usize,
                new_digest(11), // Differs
            ),
            PageRange::new(&0, &1331283967702353742, new_digest(2)),
            PageRange::new(
                &2425302987964992968,
                &3541571342636567061,
                new_digest(13), // Differs
            ),
            PageRange::new(
                &3632803506728089373,
                &4707132771120484774,
                new_digest(14), // Differs
            ),
            PageRange::new(&17995215864353464453, &17995215864353464453, new_digest(5)),
        ];

        assert_matches!(
            diff(local, peer).as_slice(),
            [DiffRange {
                start: 1331283967702353742,
                end: 17995215864353464453
            }]
        );
    }

    // If the bounds of the peer page exceed that of the local page on both
    // sides, make sure both sides are requested to minimise round trips.
    #[test]
    fn test_diff_peer_bounds_larger_both_sides() {
        enable_logging!();

        let local = vec![PageRange::new(&2, &15, new_digest(1))];
        let peer = vec![PageRange::new(&1, &42, new_digest(2))];

        assert_matches!(
            diff(local, peer).as_slice(),
            [DiffRange { start: 1, end: 42 }]
        );
    }

    #[test]
    fn test_diff_empty_peer() {
        enable_logging!();

        let peer = vec![];
        let local = vec![PageRange::new(&1, &42, new_digest(1))];

        assert_matches!(diff(local, peer).as_slice(), []);
    }

    #[test]
    fn test_diff_empty_local() {
        enable_logging!();

        let local = vec![];
        let peer = vec![PageRange::new(&1, &42, new_digest(1))];

        assert_matches!(
            diff(local, peer).as_slice(),
            [DiffRange { start: 1, end: 42 }]
        );
    }

    #[test]
    fn test_trivial_sync_differing_values() {
        enable_logging!();

        let mut a = Node::default();
        a.upsert(IntKey::new(42), 1);

        let mut b = Node::default();
        b.upsert(IntKey::new(42), 2);

        assert_eq!(sync_round(&mut a, &mut b), 1);
        assert_eq!(sync_round(&mut a, &mut b), 0);

        assert_eq!(sync_round(&mut a, &mut b), 0);
        assert_eq!(sync_round(&mut a, &mut b), 0);

        assert_eq!(a, b);
    }

    #[test]
    fn test_trivial_sync_differing_keys() {
        enable_logging!();

        let mut a = Node::default();
        a.upsert(IntKey::new(42), 1);

        let mut b = Node::default();
        b.upsert(IntKey::new(24), 1);

        assert_eq!(sync_round(&mut a, &mut b), 0, "a => b");
        assert_eq!(sync_round(&mut a, &mut b), 0, "a => b");
        assert_eq!(sync_round(&mut b, &mut a), 1, "b => a");
        assert_eq!(sync_round(&mut b, &mut a), 0, "b => a");
        assert_eq!(sync_round(&mut a, &mut b), 2, "a => b");
        assert_eq!(sync_round(&mut a, &mut b), 0, "a => b");
        assert_eq!(sync_round(&mut b, &mut a), 0, "b => a");
        assert_eq!(sync_round(&mut b, &mut a), 0, "b => a");

        assert_eq!(a, b);
    }

    /// Test the case where the local root page is a superset of the peer.
    ///
    /// This is an example of the peer needing to sync in order for the local
    /// node to sync the missing peer keys. Because the range bounds do not
    /// match, the peer -> local sync is not attempted until the peer has
    /// obtained the local keys, making the page ranges match, allowing the page
    /// to be peer -> local sync to complete.
    #[test]
    fn test_local_superset_of_peer() {
        enable_logging!();

        let mut a = Node::default();
        a.upsert(IntKey::new(244067356035258375), 0);

        let mut b = Node::default();
        b.upsert(IntKey::new(0), 0);
        b.upsert(IntKey::new(2750749774246655017), 0);

        assert_eq!(sync_round(&mut a, &mut b), 0, "a => b run 1");
        assert_eq!(sync_round(&mut b, &mut a), 2, "b => a run 1");
        assert_eq!(sync_round(&mut a, &mut b), 3, "a => b run 2");
        assert_eq!(sync_round(&mut b, &mut a), 0, "b => a run 2");
        assert_eq!(sync_round(&mut a, &mut b), 0, "a => b run 3");
        assert_eq!(sync_round(&mut b, &mut a), 0, "b => a run 3");

        assert_eq!(a, b);
    }

    // Construct a test with a level 2 root node that is absent in the local
    // tree, but who's presence does not affect the min/max ranges of the root
    // (in essence, the peer has an extra level / key than local, but ranges
    // match).
    #[test]
    fn test_root_single_node_covered() {
        enable_logging!();

        // 0: 2356959391436047
        // 1: 1827784367256368463
        // 2: 8090434540329235177
        // 3: 8090434540343951592
        let mut a = Node::default();
        a.upsert(IntKey::new(2356959391436047), 0);
        a.upsert(IntKey::new(8090434540343951592), 0);

        // 2356959391436047 is lt subtree of 8090434540343951592

        // pull two subtrees:
        //   * start range mismatch for 0 -> 1, 2 -> 3
        //   * end range mismatch

        // this should complete B, but doesn't include the value in between the
        // pulled ranges (1, 2) which is a level higher.

        let mut b = Node::default();
        b.upsert(IntKey::new(1827784367256368463), 0);
        b.upsert(IntKey::new(8090434540329235177), 0);

        assert_eq!(sync_round(&mut a, &mut b), 2, "a => b run 1");
        assert_eq!(sync_round(&mut b, &mut a), 4, "b => a run 1");

        assert_eq!(sync_round(&mut a, &mut b), 0, "a => b run 2");
        assert_eq!(sync_round(&mut b, &mut a), 0, "b => a run 2");

        assert_eq!(sync_round(&mut a, &mut b), 0, "a => b run 3");
        assert_eq!(sync_round(&mut b, &mut a), 0, "b => a run 3");

        assert_eq!(a, b);
    }

    /// One node has a tree range that is a superset of the other.
    #[test]
    fn test_superset() {
        enable_logging!();

        // 0
        // 1479827427186972579
        // 6895546778622627890
        // 8090434540329235177
        let mut a = Node::default();
        a.upsert(IntKey::new(1479827427186972579), 0);
        a.upsert(IntKey::new(6895546778622627890), 0);

        let mut b = Node::default();
        b.upsert(IntKey::new(0), 0);
        b.upsert(IntKey::new(8090434540329235177), 0);

        assert_eq!(sync_round(&mut a, &mut b), 0, "a => b run 1");
        // B contains a range superset, so it believes it has everything
        // already.

        assert_eq!(sync_round(&mut b, &mut a), 2, "b => a run 1");
        // A pulls the missing keys within B.

        assert_eq!(sync_round(&mut a, &mut b), 4, "a => b run 2");
        // Subsequently B pulls all the keys from A (as B's existing keys were
        // within the A's range now being fetched due to a hash mismatch).

        assert_eq!(sync_round(&mut b, &mut a), 0, "b => a run 2");
        assert_eq!(sync_round(&mut a, &mut b), 0, "a => b run 3");
        assert_eq!(sync_round(&mut b, &mut a), 0, "b => a run 3");

        assert_eq!(a, b);
    }

    /// Construct a test where both roots contain a single key, both with
    /// differing values - each node needs to pull their peer's root key.
    #[test]
    fn test_both_roots_single_differing_node() {
        enable_logging!();

        let mut a = Node::default();
        a.upsert(IntKey::new(3541571342636567061), 0);
        a.upsert(IntKey::new(4706901308862946071), 0);
        a.upsert(IntKey::new(4706903583207578752), 0);

        let mut b = Node::default();
        b.upsert(IntKey::new(3632796868130453657), 0);
        b.upsert(IntKey::new(3632803506728089373), 0);
        b.upsert(IntKey::new(4707132771120484774), 0);

        for _i in 0..100 {
            sync_round(&mut a, &mut b);
            sync_round(&mut b, &mut a);
        }

        assert_eq!(sync_round(&mut a, &mut b), 0);
        assert_eq!(sync_round(&mut b, &mut a), 0);

        assert_eq!(a, b);
    }

    /// OLD: Previously ensured only the "leading edge" missing keys are fetched
    /// - the common case for new monotonic keys added to a tree.
    ///
    /// Disabled to reduce average sync cost.
    #[test]
    fn test_leading_edge_range_sync() {
        enable_logging!();

        let mut a = Node::default();
        a.upsert(IntKey::new(1), 0);
        a.upsert(IntKey::new(2), 0);
        a.upsert(IntKey::new(3), 0);
        a.upsert(IntKey::new(4), 0);
        a.upsert(IntKey::new(5), 0);
        a.upsert(IntKey::new(6), 0);
        a.upsert(IntKey::new(7), 0);
        a.upsert(IntKey::new(8), 0);
        a.upsert(IntKey::new(9), 0);
        a.upsert(IntKey::new(10), 0);

        let mut b = Node::default();
        b.upsert(IntKey::new(1), 0);
        b.upsert(IntKey::new(2), 0);
        b.upsert(IntKey::new(3), 0);
        b.upsert(IntKey::new(4), 0);
        b.upsert(IntKey::new(5), 0);
        b.upsert(IntKey::new(6), 0);

        assert_eq!(sync_round(&mut a, &mut b), 10, "a => b run 1");
        assert_eq!(sync_round(&mut b, &mut a), 0, "b => a run 1");

        assert_eq!(sync_round(&mut a, &mut b), 0, "a => b run 2");
        assert_eq!(sync_round(&mut b, &mut a), 0, "b => a run 2");

        assert_eq!(a, b);
    }

    const MAX_NODE_KEYS: usize = 100;

    prop_compose! {
        /// Yield a set of keys covering the full u64 range, driving randomness
        /// of tree node placements instead of collisions.
        fn arbitrary_large_key_set()(kv_pairs in prop::collection::hash_set(
            (any::<u64>(), any::<u64>()),
            0..MAX_NODE_KEYS)
        ) -> HashSet<(u64, u64)> {
            kv_pairs
        }
    }

    prop_compose! {
        /// Yield a small set of keys, to arbitrarily increase the collision
        /// count between peers by having them generate the same keys with
        /// differing values.
        fn arbitrary_small_key_set()(kv_pairs in prop::collection::hash_set(
            (0_u64..50, 0_u64..50),
            0..MAX_NODE_KEYS)
        ) -> HashSet<(u64, u64)> {
            kv_pairs
        }
    }

    prop_compose! {
        /// Yield an arbitrary [`Node`] containing up to 100 random key/value
        /// pairs.
        fn arbitrary_node()(kv_pairs in prop_oneof![
            arbitrary_large_key_set(),
            arbitrary_small_key_set()
        ]) -> Node {
            let mut node = Node::default();
            for (k, v) in kv_pairs {
                node.upsert(IntKey::new(k), v);
            }
            node
        }
    }

    proptest! {
        /// Perform a synchronisation test that asserts two arbitrary trees
        /// (potentially containing no overlapping key/values) converge to the
        /// same state after repeated synchronisation rounds.
        #[test]
        fn prop_sync_trees(mut a in arbitrary_node(), mut b in arbitrary_node()) {
            enable_logging!();

            // Bound the number of sync rounds needed to converge to at most 1
            // key being sync'd per round.
            let max_count = a.key_count() + b.key_count() + 1;
            let mut count = 0;

            loop {
                // Perform a two-way sync.
                let a_to_b = sync_round(&mut a, &mut b);
                let b_to_a = sync_round(&mut b, &mut a);
                if a_to_b == 0 && b_to_a == 0 {
                    // If no progress was made, stop syncing.
                    break;
                }

                // Syncing should never pull more than the full peer tree.
                assert!(a_to_b <= a.key_count());
                assert!(b_to_a <= b.key_count());

                count += 1;
                if count >= max_count {
                    panic!("failed to sync a => b in round limit");
                }
            }

            // Ensure the nodes are now consistent.
            assert_eq!(a, b);
        }

        /// Invariant: page ranges yielded from an [`OwnedPageRange`] are
        /// identical to those from the borrowed [`PageRange`] equivalent.
        #[test]
        fn prop_owned_page_range_equivalent(mut a in arbitrary_node()) {
            enable_logging!();

            let _ = a.root_hash();
            let a_ref = a.serialise_page_ranges().unwrap();
            let a_owned = PageRangeSnapshot::from(a_ref.clone());

            let a_owned_iter = a_owned.iter();
            let a_ref_iter = a_ref.iter().cloned();

            assert!(a_owned_iter.eq(a_ref_iter));
        }
    }

    /// Perform a single sync round, pulling differences from a into b.
    ///
    /// Returns the number of fetched pages.
    fn sync_round(from: &mut Node, to: &mut Node) -> usize {
        // First sync b from a, applying the "a is always right" merge rule.
        let a2 = from.clone();
        let a_tree = from.page_ranges();

        let mut to2 = to.clone();
        let want = diff(to2.page_ranges(), a_tree);

        let mut count = 0;
        for range in want {
            for (k, v) in a2.key_range_iter(range.start()..=range.end()) {
                to.upsert(k.clone(), *v);
                count += 1;
            }
        }

        count
    }
}
