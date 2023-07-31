//! Tree difference calculation algorithm & associated types.

mod diff_builder;
mod range_list;

use std::{
    fmt::{Debug, Display},
    iter::Peekable,
};

use crate::{diff::diff_builder::DiffListBuilder, digest::PageDigest, Page};

/// A serialised representation of the range of keys contained within the
/// sub-tree rooted at a given [`Page`], and the associated [`PageDigest`].
#[derive(Debug, PartialEq)]
pub struct PageRange<'a, K> {
    /// The inclusive start & end key bounds of this range.
    start: &'a K,
    end: &'a K,

    /// The hash of this page, and the sub-tree rooted at it.
    hash: PageDigest,
}

impl<'a, K> Display for PageRange<'a, K>
where
    K: Display,
{
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_fmt(format_args!("({}, {})", self.start, self.end))
    }
}

impl<'a, K> Clone for PageRange<'a, K> {
    fn clone(&self) -> Self {
        Self {
            start: self.start,
            end: self.end,
            hash: self.hash.clone(),
        }
    }
}

impl<'a, const N: usize, K> From<&'a Page<N, K>> for PageRange<'a, K> {
    fn from(page: &'a Page<N, K>) -> Self {
        PageRange {
            start: page.min_key(),
            end: page
                .high_page()
                .map(|v| v.max_key())
                .unwrap_or_else(|| page.max_key()),
            hash: page
                .hash()
                .expect("page visitor requires prior hash regeneration")
                .clone(),
        }
    }
}

impl<'a, K> PageRange<'a, K> {
    /// Construct a [`PageRange`] for the given key interval and [`PageDigest`].
    pub fn new(start: &'a K, end: &'a K, hash: PageDigest) -> Self {
        Self { start, end, hash }
    }

    /// Returns the inclusive start of this [`PageRange`].
    pub fn start(&self) -> &'a K {
        self.start
    }

    /// Returns the inclusive end of this [`PageRange`]
    pub fn end(&self) -> &'a K {
        self.end
    }

    /// Returns true if the range within `self` overlaps any portion of the
    /// range within `p`.
    pub fn overlaps(&self, p: &Self) -> bool
    where
        K: PartialOrd,
    {
        //   0 1 2 3 4 5 6 7 8 9
        // A |       |
        // B       |   |
        let leading_edge = self.start <= p.start && self.end >= p.start;
        let trailing_edge = p.start <= self.end && p.end >= self.end;
        leading_edge || trailing_edge
    }

    /// Returns true if `self` is a superset of `other` (not a strict superset -
    /// equal ranges are treated as supersets of each other).
    pub fn is_superset_of(&self, other: &Self) -> bool
    where
        K: PartialOrd,
    {
        self.start <= other.start && self.end >= other.end
    }

    /// Returns the [`PageDigest`] of this page, representing the content of the
    /// page and all pages within the sub-tree rooted at it.
    pub fn hash(&self) -> &PageDigest {
        &self.hash
    }
}

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
            start: self.start.clone(),
            end: self.end.clone(),
        }
    }
}

impl<'a, K> DiffRange<'a, K> {
    /// Returns true if `self` is a superset of `other` (not a strict superset -
    /// equal ranges are treated as supersets of each other).
    pub fn is_superset_of(&self, other: &PageRange<'a, K>) -> bool
    where
        K: PartialOrd,
    {
        self.start <= other.start && self.end >= other.end
    }

    /// Returns true if the range within `self` overlaps any portion of the
    /// range within `p`.
    pub fn overlaps(&self, p: &Self) -> bool
    where
        K: PartialOrd,
    {
        //   0 1 2 3 4 5 6 7 8 9
        // A |       |
        // B       |   |
        let leading_edge = self.start <= p.start && self.end >= p.start;
        let trailing_edge = p.start <= self.end && p.end >= self.end;
        leading_edge || trailing_edge
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

/// Compute the difference between `local` and `peer`, returning the
/// [`DiffRange`] covering the inconsistent key ranges found in `peer`.
///
/// # State Convergence
///
/// To converge the state of the two trees, the returned key ranges should be
/// requested from `peer` and used to update the state of `local`.
///
/// If `local` contains all the keys in `peer`, or the two trees are identical,
/// no [`DiffRange`] intervals are returned.
///
/// # Optimistic Page Bounds Fetching
///
/// When a page exists in `peer` has a key range that is a strict superset of
/// the key range of the same page in `local`, it is guaranteed to be
/// inconsistent. When this occurs, only the difference / missing keys are
/// returned in that page's [`DiffRange`].
///
/// This optimistically assumes the intersection of keys between the two pages
/// are consistent, minimising the number of keys fetched when this assumption
/// holds true. If false, the page will be marked fully inconsistent (inclusive
/// of the newly fetched keys) in the next [`diff()`] call.
///
/// This optimises for monotonic keys, recommended to minimise tree page
/// inconsistencies / keys fetched when new keys are inserted into the tree.
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
    T: IntoIterator<Item = &'a PageRange<'a, K>>,
    U: IntoIterator<Item = &'p PageRange<'p, K>>,
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
        Some(v) => v,
        None => return vec![],
    };

    recurse_diff(root, &mut peer, &mut local, &mut diff_builder);

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
    T: Iterator<Item = &'a PageRange<'a, K>>,
    U: Iterator<Item = &'p PageRange<'p, K>>,
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
        diff_builder.inconsistent(p.start, p.end);
    }

    assert!(peer
        .peek()
        .map(|v| !subtree_root.is_superset_of(v))
        .unwrap_or(true));

    true
}

#[cfg_attr(
    any(test, feature = "tracing"),
    tracing::instrument(skip(peer, local),)
)]
fn recurse_diff<'p, 'a: 'p, T, U, K>(
    subtree_root: &PageRange<'p, K>,
    peer: &mut Peekable<U>,
    local: &mut Peekable<T>,
    diff_builder: &mut DiffListBuilder<'p, K>,
) where
    T: Iterator<Item = &'a PageRange<'a, K>>,
    U: Iterator<Item = &'p PageRange<'p, K>>,
    K: PartialOrd + Ord + Debug + 'p + 'a,
{
    // The last visited peer page, if any.
    let mut last_p: Option<&PageRange<'_, K>> = None;

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

        let mut l = match maybe_advance_within(p, local) {
            Some(v) => v,
            None => {
                // If there's no matching local page that overlaps with p, then
                // there must be be one or more keys to be synced from the peer
                // to populate the missing local pages.
                //
                // Request the range starting from the end of the last checked p
                // (last_p), or the start of the subtree_root if none.
                let start = last_p.as_ref().map(|v| v.end).unwrap_or(subtree_root.start);
                // And end at the next local page key, or the page end.
                //
                // Any pages missing between p.end and the end of this subtree
                // will be added by the caller (recurse_subtree).
                let end = local.peek().map(|v| v.start.min(p.end)).unwrap_or(p.end);
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

        last_p = Some(p);

        // Never escape the subtree rooted at p_parent.
        assert!(subtree_root.is_superset_of(p));

        trace!(
            peer_page=?p,
            local_page=?l,
            "visit page"
        );

        // Advance the local cursor to minimise the comparable range, in turn
        // minimising the sync range.
        while let Some(v) = local.next_if(|v| v.is_superset_of(p)) {
            trace!(
                peer_page=?p,
                skip_local_page=?l,
                local_page=?v,
                "shrink local diff range"
            );
            l = v;
        }

        // If the bounds don't match, fetch the missing parts from the peer and
        // move on to the next page.
        if p.start < l.start {
            trace!(
                peer_page=?p,
                local_page=?l,
                "request missing page start range from peer"
            );
            // If a parent was missing a leaf node, it's guaranteed all
            // children pages on the left-most edge will be missing a node
            // too (and therefore are inconsistent) until they reach that
            // leaf node.
            //
            // This would cause the same range to be requested by this check
            // as the left-most edge is descended, so de-duplicate the
            // requests.
            diff_builder.inconsistent(p.start, l.start); // exclusive end range

            // Ignore any potential inconsistency within the intersection
            // between pages when fetching a range bounds mismatch.
            //
            // This may cause more round trips to sync this page, but optimises
            // for the "leading edge" case, fetching only the range bounds and
            // assuming it'll make the page consistent instead of fetching the
            // whole page for what may be a single new (monotonic) key.
            diff_builder.consistent(l.start.max(p.start), l.end.min(p.end));
        }

        if p.end > l.end {
            trace!(
                peer_page=?p,
                local_page=?l,
                "request missing page end range from peer"
            );
            // As above for the less-than side, dedupe end ranges for the
            // right-most edge.
            diff_builder.inconsistent(l.end, p.end); // inclusive end range

            // Ignore any potential inconsistency within the intersection
            // between pages when fetching a range bounds mismatch - see above.
            diff_builder.consistent(l.start.max(p.start), l.end.min(p.end));
        }

        // If the page bounds do not match, it is guaranteed this page is
        // inconsistent.
        //
        // The missing range has been requested above - begin visiting child
        // pages without marking this entire page range as inconsistent this
        // round.
        //
        // Once the full range of keys for this page is obtained, a subsequent
        // diff will cause a proper consistency check of this page and fetch
        // only the keys/child ranges that actually differ.
        if p.start != l.start || p.end != l.end {
            debug!(
                peer_page=?p,
                local_page=?l,
                "page inconsistent due to range mismatch"
            );

            // Skip hash evaluation (they're definitely not equal) and avoid
            // adding the full peer range as a consistent/inconsistent range -
            // prefer instead to optimistically fetch only the range diff.
            recurse_subtree(p, peer, local, diff_builder);
            continue;
        }

        if l.hash == p.hash {
            debug!(
                peer_page=?p,
                local_page=?l,
                "hash match - consistent page"
            );

            // Record this page as fully consistent.
            diff_builder.consistent(p.start, p.end);
        } else {
            debug!(
                peer_page=?p,
                local_page=?l,
                "hash mismatch"
            );

            diff_builder.inconsistent(p.start, p.end);
        }

        // Evaluate the sub-tree, causing all the (consistent) child ranges to
        // be added to the consistent list to, shrink this inconsistent range
        // (or simply advancing through the subtree if this page is consistent).
        recurse_subtree(p, peer, local, diff_builder);
    }
}

/// Return the next [`PageRange`] if it is part of the sub-tree rooted at
/// `parent`.
fn maybe_advance_within<'a, 'p, K, T>(
    parent: &PageRange<'p, K>,
    cursor: &mut Peekable<T>,
) -> Option<&'a PageRange<'a, K>>
where
    T: Iterator<Item = &'a PageRange<'a, K>>,
    K: PartialOrd + 'a,
{
    if cursor
        .peek()
        .map(|p| !parent.overlaps(p))
        .unwrap_or_default()
    {
        return None;
    }

    cursor.next()
}

#[cfg(test)]
mod tests {
    use std::collections::HashSet;

    use assert_matches::assert_matches;
    use proptest::prelude::*;

    use super::*;
    use crate::{
        digest::Digest,
        test_util::{IntKey, Node},
    };

    const fn new_digest(lsb: u8) -> PageDigest {
        PageDigest::new(Digest::new([
            0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, lsb,
        ]))
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
                    let a = PageRange {
                        start: &$a_start,
                        end: $a_end,
                        hash: new_digest(42),
                    };
                    let b = PageRange {
                        start: &$b_start,
                        end: $b_end,
                        hash: new_digest(42),
                    };

                    assert!(a.is_superset_of(&b) == $want);

                    // All pages that are a superset, also overlap.
                    if a.is_superset_of(&b) {
                        assert!(a.overlaps(&b));
                        assert!(b.overlaps(&a));
                    }
                }
            }
        };
    }

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
            PageRange {
                start: &2,
                end: &15,
                hash: new_digest(1),
            },
            PageRange {
                start: &2,
                end: &6,
                hash: new_digest(2),
            },
            PageRange {
                start: &2,
                end: &2,
                hash: new_digest(3),
            },
            PageRange {
                start: &5,
                end: &5,
                hash: new_digest(4),
            },
            PageRange {
                start: &15,
                end: &15,
                hash: new_digest(5),
            },
        ];

        let peer = local.clone();

        assert_matches!(diff(&local, &peer).as_slice(), []);
    }

    #[test]
    fn test_diff_peer_missing_last_page() {
        enable_logging!();

        let local = vec![
            PageRange {
                start: &2,
                end: &15,
                hash: new_digest(1),
            },
            PageRange {
                start: &2,
                end: &6,
                hash: new_digest(2),
            },
            PageRange {
                start: &2,
                end: &2,
                hash: new_digest(3),
            },
            PageRange {
                start: &5,
                end: &5,
                hash: new_digest(4),
            },
            PageRange {
                start: &15,
                end: &15,
                hash: new_digest(5),
            },
        ];

        let mut peer = local.clone();

        // Remove the last page
        let _ = peer.pop().unwrap();

        // Invalidate the root/parent
        peer[0].hash = new_digest(42);

        // Update the peer root range to reflect the missing last page
        peer[0].end = &11;

        // Nothing to ask for - the peer is behind
        assert_matches!(diff(&local, &peer).as_slice(), []);
    }

    #[test]
    fn test_diff_local_missing_last_page() {
        enable_logging!();

        let mut local = vec![
            PageRange {
                start: &2,
                end: &15,
                hash: new_digest(1),
            },
            PageRange {
                start: &2,
                end: &6,
                hash: new_digest(2),
            },
            PageRange {
                start: &2,
                end: &2,
                hash: new_digest(3),
            },
            PageRange {
                start: &5,
                end: &5,
                hash: new_digest(4),
            },
            PageRange {
                start: &15,
                end: &15,
                hash: new_digest(5),
            },
        ];

        let peer = local.clone();

        // Remove the last page
        let _ = local.pop().unwrap();

        // Invalidate the root/parent
        local[0].hash = new_digest(42);

        // Update the local root range to reflect the missing last page
        local[0].end = &11;

        assert_matches!(
            diff(&local, &peer).as_slice(),
            [DiffRange { start: 11, end: 15 }]
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
            PageRange {
                start: &2,
                end: &15,
                hash: new_digest(1),
            },
            PageRange {
                start: &2,
                end: &6,
                hash: new_digest(2),
            },
            PageRange {
                start: &2,
                end: &2,
                hash: new_digest(3),
            },
            PageRange {
                start: &5,
                end: &5,
                hash: new_digest(4),
            },
            PageRange {
                start: &15,
                end: &15,
                hash: new_digest(5),
            },
        ];

        let peer = vec![
            PageRange {
                start: &3, // Differs
                end: &15,
                hash: new_digest(42), // Differs
            },
            PageRange {
                start: &3, // Differs
                end: &6,
                hash: new_digest(43), // Differs
            },
            //
            // No page containing 2 at level 0
            PageRange {
                start: &5,
                end: &5,
                hash: new_digest(4),
            },
            PageRange {
                start: &15,
                end: &15,
                hash: new_digest(5),
            },
        ];

        assert_matches!(diff(&local, &peer).as_slice(), []);
    }

    #[test]
    fn test_diff_local_missing_leaf_page() {
        enable_logging!();

        let local = vec![
            PageRange {
                start: &3, // Differs
                end: &15,
                hash: new_digest(42), // Differs
            },
            PageRange {
                start: &3, // Differs
                end: &6,
                hash: new_digest(43), // Differs
            },
            //
            // No page containing 2 at level 0
            PageRange {
                start: &5,
                end: &5,
                hash: new_digest(4),
            },
            PageRange {
                start: &15,
                end: &15,
                hash: new_digest(5),
            },
        ];

        let peer = vec![
            PageRange {
                start: &2,
                end: &15,
                hash: new_digest(1),
            },
            PageRange {
                start: &2,
                end: &6,
                hash: new_digest(2),
            },
            PageRange {
                start: &2,
                end: &2,
                hash: new_digest(3),
            },
            PageRange {
                start: &5,
                end: &5,
                hash: new_digest(4),
            },
            PageRange {
                start: &15,
                end: &15,
                hash: new_digest(5),
            },
        ];

        assert_matches!(
            diff(&local, &peer).as_slice(),
            [DiffRange { start: 2, end: 3 }]
        );
    }

    #[test]
    fn test_diff_local_missing_subtree() {
        enable_logging!();

        let local = vec![
            PageRange {
                start: &3,
                end: &15,
                hash: new_digest(42), // Differs
            },
            PageRange {
                start: &15,
                end: &15,
                hash: new_digest(5),
            },
        ];

        let peer = vec![
            PageRange {
                start: &2,
                end: &15,
                hash: new_digest(1),
            },
            PageRange {
                start: &2,
                end: &6,
                hash: new_digest(2),
            },
            PageRange {
                start: &2,
                end: &2,
                hash: new_digest(3),
            },
            PageRange {
                start: &5,
                end: &5,
                hash: new_digest(4),
            },
            PageRange {
                start: &15,
                end: &15,
                hash: new_digest(5),
            },
        ];

        assert_matches!(
            diff(&local, &peer).as_slice(),
            [DiffRange { start: 2, end: 6 }]
        );
    }

    #[test]
    fn test_diff_peer_missing_subtree() {
        enable_logging!();

        let local = vec![
            PageRange {
                start: &2,
                end: &15,
                hash: new_digest(1),
            },
            PageRange {
                start: &2,
                end: &6,
                hash: new_digest(2),
            },
            PageRange {
                start: &2,
                end: &2,
                hash: new_digest(3),
            },
            PageRange {
                start: &5,
                end: &5,
                hash: new_digest(4),
            },
            PageRange {
                start: &15,
                end: &15,
                hash: new_digest(5),
            },
        ];

        let peer = vec![
            PageRange {
                start: &3,
                end: &15,
                hash: new_digest(42), // Differs
            },
            PageRange {
                start: &15,
                end: &15,
                hash: new_digest(5),
            },
        ];

        assert_matches!(diff(&local, &peer).as_slice(), []);
    }

    #[test]
    fn test_diff_leaf_page_hash() {
        enable_logging!();

        let peer = vec![
            PageRange {
                start: &2,
                end: &15,
                hash: new_digest(42), // Differs
            },
            PageRange {
                start: &2,
                end: &6,
                hash: new_digest(42), // Differs
            },
            PageRange {
                start: &2,
                end: &2,
                hash: new_digest(3),
            },
            PageRange {
                start: &5,
                end: &5,
                hash: new_digest(4),
            },
            PageRange {
                start: &15,
                end: &15,
                hash: new_digest(5),
            },
        ];

        let local = vec![
            PageRange {
                start: &2,
                end: &15,
                hash: new_digest(1),
            },
            PageRange {
                start: &2,
                end: &6,
                hash: new_digest(2),
            },
            PageRange {
                start: &2,
                end: &2,
                hash: new_digest(3),
            },
            PageRange {
                start: &5,
                end: &5,
                hash: new_digest(4),
            },
            PageRange {
                start: &15,
                end: &15,
                hash: new_digest(5),
            },
        ];

        assert_matches!(
            diff(&local, &peer).as_slice(),
            // Range (3,6) is optimal, but this gets the job done.
            [DiffRange { start: 2, end: 15 }]
        );
    }

    #[test]
    fn test_diff_peer_extra_key_last_page() {
        enable_logging!();

        let local = vec![
            PageRange {
                start: &2,
                end: &15,
                hash: new_digest(1),
            },
            PageRange {
                start: &2,
                end: &6,
                hash: new_digest(2),
            },
            PageRange {
                start: &2,
                end: &2,
                hash: new_digest(3),
            },
            PageRange {
                start: &5,
                end: &5,
                hash: new_digest(4),
            },
            PageRange {
                start: &15,
                end: &15,
                hash: new_digest(5),
            },
        ];

        let mut peer = local.clone();
        let end = peer.last_mut().unwrap();
        end.end = &16;
        end.hash = new_digest(42);

        // Root hash differs to reflect differing child
        peer[0].end = &16;
        peer[0].hash = new_digest(42);

        assert_matches!(
            diff(&local, &peer).as_slice(),
            [DiffRange { start: 15, end: 16 }]
        );
    }

    #[test]
    fn test_diff_root_page_hash() {
        enable_logging!();

        let local = vec![
            PageRange {
                start: &2,
                end: &15,
                hash: new_digest(1),
            },
            PageRange {
                start: &2,
                end: &6,
                hash: new_digest(2),
            },
            PageRange {
                start: &2,
                end: &2,
                hash: new_digest(3),
            },
            PageRange {
                start: &5,
                end: &5,
                hash: new_digest(4),
            },
            PageRange {
                start: &15,
                end: &15,
                hash: new_digest(5),
            },
        ];

        let mut peer = local.clone();

        // Root hash differs due to added key 8
        peer[0].hash = new_digest(42);

        // Without the reduce_sync_range optimisation, this root inconsistency
        // would cause a fetch against the whole tree (start: 2, end: 15).
        //
        // Instead, the known-good sub-tree pages can be removed from the sync
        // range.
        assert_matches!(
            diff(&local, &peer).as_slice(),
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
            PageRange {
                start: &2,
                end: &15,
                hash: new_digest(1),
            },
            PageRange {
                start: &2,
                end: &6,
                hash: new_digest(2),
            },
            PageRange {
                start: &2,
                end: &2,
                hash: new_digest(3),
            },
            PageRange {
                start: &5,
                end: &5,
                hash: new_digest(4),
            },
            PageRange {
                start: &15,
                end: &15,
                hash: new_digest(5),
            },
        ];

        let mut peer = local.clone();

        // Root hash differs due to added key 8
        peer[1].hash = new_digest(42);
        peer[1].end = &7;

        peer[0].hash = new_digest(42);

        assert_matches!(
            diff(&local, &peer).as_slice(),
            [DiffRange { start: 6, end: 15 }]
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
        //
        // This checks if discrepancies in children are still discovered, even
        // when bounds of parents differ. Ideally all discrepancies would be
        // discovered the first time round, but in order to optimise for
        // "leading edge" key additions and optimistically minimise sync ranges,
        // this is not the case - instead the range diff is resolved first, and
        // after, the page inconsistency for 2 is resolved via a second sync.

        let local = vec![
            PageRange {
                start: &2,
                end: &15,
                hash: new_digest(1),
            },
            PageRange {
                start: &2,
                end: &6,
                hash: new_digest(2),
            },
            PageRange {
                start: &2,
                end: &2,
                hash: new_digest(3),
            },
            PageRange {
                start: &5,
                end: &5,
                hash: new_digest(4),
            },
            PageRange {
                start: &15,
                end: &15,
                hash: new_digest(5),
            },
        ];

        let mut peer = local.clone();

        // Extend key range of 1st child to 2-6 to 2-7
        peer[1].hash = new_digest(42);
        peer[1].end = &7;

        // Key 2 value change
        peer[2].hash = new_digest(42);

        // Root hash
        peer[0].hash = new_digest(42);

        assert_matches!(
            diff(&local, &peer.clone()).as_slice(),
            [DiffRange { start: 6, end: 15 }]
        );

        let mut local = peer.clone();

        // Only 2 should remain different - reset the hash.
        local[2].hash = new_digest(3);
        peer[1].hash = new_digest(2);
        peer[0].hash = new_digest(1);

        // 2, 15 because the root page is inconsistent and there's no consistent
        // pages that shrink the range.
        assert_matches!(
            diff(&local, &peer).as_slice(),
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
            PageRange {
                start: &0,
                end: &17995215864353464453_usize,
                hash: new_digest(1),
            },
            PageRange {
                start: &0,
                end: &1331283967702353742,
                hash: new_digest(2),
            },
            PageRange {
                start: &2425302987964992968,
                end: &3632803506728089373, // Larger key range than peer
                hash: new_digest(3),
            },
            PageRange {
                start: &4706903583207578752, // Shorter key range than peer (missing first key)
                end: &4707132771120484774,
                hash: new_digest(4),
            },
            PageRange {
                start: &17995215864353464453,
                end: &17995215864353464453,
                hash: new_digest(5),
            },
        ];
        let peer = vec![
            PageRange {
                start: &0,
                end: &17995215864353464453_usize,
                hash: new_digest(11), // Differs
            },
            PageRange {
                start: &0,
                end: &1331283967702353742,
                hash: new_digest(2),
            },
            PageRange {
                start: &2425302987964992968,
                end: &3541571342636567061,
                hash: new_digest(13), // Differs
            },
            PageRange {
                start: &3632803506728089373,
                end: &4707132771120484774,
                hash: new_digest(14), // Differs
            },
            PageRange {
                start: &17995215864353464453,
                end: &17995215864353464453,
                hash: new_digest(5),
            },
        ];

        assert_matches!(
            diff(&local, &peer).as_slice(),
            [
                DiffRange {
                    start: 1331283967702353742,
                    end: 4706903583207578752
                },
                DiffRange {
                    start: 4707132771120484774,
                    end: 17995215864353464453
                }
            ]
        );
    }

    // If the bounds of the peer page exceed that of the local page on both
    // sides, make sure both sides are requested to minimise round trips.
    #[test]
    fn test_diff_peer_bounds_larger_both_sides() {
        enable_logging!();

        let local = vec![PageRange {
            start: &2,
            end: &15,
            hash: new_digest(1),
        }];

        let peer = vec![PageRange {
            start: &1,
            end: &42,
            hash: new_digest(1),
        }];

        assert_matches!(
            diff(&local, &peer).as_slice(),
            [
                DiffRange { start: 1, end: 2 },
                DiffRange { start: 15, end: 42 },
            ]
        );
    }

    #[test]
    fn test_diff_empty_peer() {
        enable_logging!();

        let peer = vec![];
        let local = vec![PageRange {
            start: &1,
            end: &42,
            hash: new_digest(1),
        }];

        assert_matches!(diff(&local, &peer).as_slice(), []);
    }

    #[test]
    fn test_diff_empty_local() {
        enable_logging!();

        let local = vec![];
        let peer = vec![PageRange {
            start: &1,
            end: &42,
            hash: new_digest(1),
        }];

        assert_matches!(
            diff(&local, &peer).as_slice(),
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

    /// Ensure only the "leading edge" missing keys are fetched - the common
    /// case for new monotonic keys added to a tree.
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

        assert_eq!(sync_round(&mut a, &mut b), 5, "a => b run 1");
        assert_eq!(sync_round(&mut b, &mut a), 0, "b => a run 1");

        assert_eq!(sync_round(&mut a, &mut b), 0, "a => b run 2");
        assert_eq!(sync_round(&mut b, &mut a), 0, "b => a run 2");

        assert_eq!(a, b);
    }

    #[test]
    fn test_prop_fail() {
        enable_logging!();

        let mut a = Node::default();
        a.upsert(IntKey::new(6416642709185293041), 0);
        a.upsert(IntKey::new(6823694781896678135), 0);
        a.upsert(IntKey::new(6823727308570268642), 0);
        a.upsert(IntKey::new(16590198516108651936), 0);

        let mut b = Node::default();
        b.upsert(IntKey::new(0), 0);
        b.upsert(IntKey::new(10417693944069773430), 0);

        assert_eq!(sync_round(&mut a, &mut b), 0, "a => b run 1");
        assert_eq!(sync_round(&mut b, &mut a), 1, "b => a run 1");

        assert_eq!(sync_round(&mut a, &mut b), 1, "a => b run 2");
        assert_eq!(sync_round(&mut b, &mut a), 3, "b => a run 2");

        assert_eq!(sync_round(&mut a, &mut b), 6, "a => b run 3");
        assert_eq!(sync_round(&mut b, &mut a), 0, "b => a run 3");

        assert_eq!(sync_round(&mut a, &mut b), 0, "a => b run 4");
        assert_eq!(sync_round(&mut b, &mut a), 0, "b => a run 4");

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
    }

    /// Perform a single sync round, pulling differences from a into b.
    ///
    /// Returns the number of fetched pages.
    fn sync_round(from: &mut Node, to: &mut Node) -> usize {
        // First sync b from a, applying the "a is always right" merge rule.
        let a2 = from.clone();
        let a_tree = from.page_ranges();

        let mut to2 = to.clone();
        let to_tree = to2.page_ranges();
        let want = diff(&to_tree, &a_tree);

        let mut count = 0;
        for range in want {
            for (k, v) in a2.key_range_iter(range.start..=range.end) {
                to.upsert(k.clone(), *v);
                count += 1;
            }
        }

        count
    }
}
