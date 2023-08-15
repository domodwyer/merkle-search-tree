use std::fmt::Display;

use crate::{digest::PageDigest, Page};

/// A serialised representation of the range of keys contained within the
/// sub-tree rooted at a given [`Page`], and the associated [`PageDigest`].
///
/// A [`PageRange`] contains all the information needed to perform a tree
/// difference calculation, used as the input to the [`diff()`] function.
///
/// The contents of this type can be serialised and transmitted over the
/// network, and reconstructed by the receiver by calling [`PageRange::new()`]
/// with the serialised values.
///
/// # Exchanging Between Peers
///
/// Exchange the ordered sets of [`PageRange`] between peers by serialising
/// their content, accessed through the accessor methods:
///
/// ```rust
/// # use std::ops::Deref;
/// # use merkle_search_tree::{*, diff::PageRange};
/// #
/// /// A network wire representation used by the application.
/// struct NetworkPage {
///     start_bounds: String,
///     end_bounds: String,
///     hash: [u8; 16],
/// }
///
/// let mut t = MerkleSearchTree::default();
/// t.upsert("bananas".to_string(), &"platanos".to_string());
/// t.root_hash();
///
/// let network_request: Vec<NetworkPage> = t
///     .serialise_page_ranges()
///     .unwrap()
///     .into_iter()
///     .map(|page| NetworkPage {
///         start_bounds: page.start().clone(),
///         end_bounds: page.end().clone(),
///         hash: *page.hash().as_bytes(),
///     })
///     .collect();
///
/// // Send network_request to a peer over the network
/// ```
///
/// And reconstruct the [`PageRange`] on the receiver:
///
/// ```rust
/// # use merkle_search_tree::diff::PageRange;
/// # use merkle_search_tree::digest::*;
/// #
/// # struct NetworkPage {
/// #     start_bounds: String,
/// #     end_bounds: String,
/// #     hash: [u8; 16],
/// # }
/// #
/// # let network_request: Vec<NetworkPage> = vec![];
/// // Receive network_request from a peer over the network
///
/// // PageRange construction is zero-copy for the page keys, borrowing the keys
/// // from the underlying network request.
/// let page_refs = network_request
///     .iter()
///     .map(|p| {
///         // If this request is coming from an untrusted source, validate that
///         // start <= end to avoid the PageRange constructor panic.
///         PageRange::new(&p.start_bounds, &p.end_bounds, PageDigest::new(p.hash))
///     })
///     .collect::<Vec<_>>();
///
/// // Feed page_refs into diff()
/// ```
///
/// # Borrowed vs. Owned
///
/// A [`PageRange`] borrows the keys from the tree to avoid unnecessary clones,
/// retaining an immutable reference to the tree.
///
/// If an owned / long-lived set of [`PageRange`] is desired (avoiding the
/// immutable reference to the tree), generate a [`PageRangeSnapshot`] from the
/// set of [`PageRange`].
///
/// [`diff()`]: crate::diff::diff
/// [`PageRangeSnapshot`]: crate::diff::PageRangeSnapshot
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
    #[inline(always)]
    fn from(page: &'a Page<N, K>) -> Self {
        PageRange {
            start: page.min_subtree_key(),
            end: page.max_subtree_key(),
            hash: page
                .hash()
                .expect("page visitor requires prior hash regeneration")
                .clone(),
        }
    }
}

impl<'a, K> PageRange<'a, K> {
    /// Construct a [`PageRange`] for the given key interval and [`PageDigest`].
    ///
    /// # Panics
    ///
    /// If `start` is greater than `end`, this method panics.
    pub fn new(start: &'a K, end: &'a K, hash: PageDigest) -> Self
    where
        K: PartialOrd,
    {
        assert!(start <= end);
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
    pub(crate) fn overlaps(&self, p: &Self) -> bool
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
    pub(crate) fn is_superset_of(&self, other: &Self) -> bool
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

    /// Consume this [`PageRange`], returning the [`PageDigest`] that covers the
    /// subtree rooted at this page.
    pub fn into_hash(self) -> PageDigest {
        self.hash
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{digest::Digest, MerkleSearchTree};

    /// Ensure the public API allows for serialisation & deserialisation of
    /// [`PageRange`].
    #[test]
    fn test_round_trip_api() {
        struct NetworkPage {
            start_bounds: String,
            end_bounds: String,
            hash: [u8; 16],
        }

        let mut t = MerkleSearchTree::default();
        t.upsert("bananas".to_string(), &"platanos".to_string());
        t.root_hash();

        let page_ranges = t.serialise_page_ranges().unwrap();

        // Serialise
        let network_pages: Vec<NetworkPage> = page_ranges
            .iter()
            .map(|v| NetworkPage {
                start_bounds: v.start().clone(),
                end_bounds: v.end().clone(),
                hash: *v.hash().as_bytes(),
            })
            .collect();

        // Deserialise
        let got: Vec<PageRange<'_, String>> = network_pages
            .iter()
            .map(|v| PageRange::new(&v.start_bounds, &v.end_bounds, PageDigest::new(v.hash)))
            .collect();

        assert_eq!(page_ranges, got);
    }

    #[test]
    #[should_panic(expected = "start <= end")]
    fn test_start_gt_end_panic() {
        let _p = PageRange::new(
            &42,
            &24,
            PageDigest::from(Digest::new([
                1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16,
            ])),
        );
    }
}
