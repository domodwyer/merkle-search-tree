use super::PageRange;
use crate::digest::PageDigest;

/// An owned point-in-time snapshot of the [`PageRange`] returned from a call to
/// [`MerkleSearchTree::serialise_page_ranges()`].
///
/// Generating a [`PageRangeSnapshot`] from a set of [`PageRange`] instances
/// clones all the bounding keys in each [`PageRange`], and therefore can only
/// be generated if the key type `K` implements [`Clone`].
///
/// ```
/// # use merkle_search_tree::{*, diff::*};
/// #
/// let mut t = MerkleSearchTree::default();
/// t.upsert("bananas", &42);
///
/// // Rehash the tree before generating the page ranges
/// let _ = t.root_hash();
///
/// // Generate the hashes & page ranges, immutably borrowing the tree
/// let ranges = t.serialise_page_ranges().unwrap();
///
/// // Obtain an owned PageRangeSnapshot from the borrowed PageRange, in turn
/// // releasing the immutable reference to the tree.
/// let snap = PageRangeSnapshot::from(ranges);
///
/// // The tree is now mutable again.
/// t.upsert("platanos", &42);
/// ```
///
/// A [`PageRangeSnapshot`] can also be generated from owned key values using
/// the [`OwnedPageRange`] type to eliminate clones where unnecessary.
///
/// [`MerkleSearchTree::serialise_page_ranges()`]:
///     crate::MerkleSearchTree::serialise_page_ranges
#[derive(Debug, Clone, PartialEq)]
pub struct PageRangeSnapshot<K>(Vec<OwnedPageRange<K>>);

impl<K> PageRangeSnapshot<K> {
    /// Return an iterator of [`PageRange`] from the snapshot content.
    pub fn iter(&self) -> impl ExactSizeIterator<Item = PageRange<'_, K>>
    where
        K: PartialOrd,
    {
        self.0
            .iter()
            .map(|v| PageRange::new(&v.start, &v.end, v.hash.clone()))
    }
}

impl<'a, K> From<Vec<PageRange<'a, K>>> for PageRangeSnapshot<K>
where
    K: Clone,
{
    fn from(value: Vec<PageRange<'a, K>>) -> Self {
        value.into_iter().collect()
    }
}

impl<'a, K> FromIterator<PageRange<'a, K>> for PageRangeSnapshot<K>
where
    K: Clone + 'a,
{
    fn from_iter<T: IntoIterator<Item = PageRange<'a, K>>>(iter: T) -> Self {
        Self(iter.into_iter().map(OwnedPageRange::from).collect())
    }
}

impl<K> From<Vec<OwnedPageRange<K>>> for PageRangeSnapshot<K> {
    fn from(value: Vec<OwnedPageRange<K>>) -> Self {
        value.into_iter().collect()
    }
}

impl<K> FromIterator<OwnedPageRange<K>> for PageRangeSnapshot<K> {
    fn from_iter<T: IntoIterator<Item = OwnedPageRange<K>>>(iter: T) -> Self {
        Self(iter.into_iter().collect())
    }
}

/// An owned representation of a [`PageRange`] containing an owned key interval
/// & page hash.
///
/// This type can be used to construct a [`PageRangeSnapshot`] from owned values
/// (eliminating key/hash clones).
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct OwnedPageRange<K> {
    start: K,
    end: K,
    hash: PageDigest,
}

impl<K> OwnedPageRange<K>
where
    K: PartialOrd,
{
    /// Initialise a new [`OwnedPageRange`] for the given inclusive key
    /// interval, and page hash covering the key range.
    ///
    /// # Panics
    ///
    /// If `start` is greater than `end`, this method panics.
    pub fn new(start: K, end: K, hash: PageDigest) -> Self {
        assert!(start <= end);
        Self { start, end, hash }
    }
}

impl<'a, K> From<PageRange<'a, K>> for OwnedPageRange<K>
where
    K: Clone,
{
    fn from(v: PageRange<'a, K>) -> Self {
        Self {
            start: v.start().clone(),
            end: v.end().clone(),
            hash: v.into_hash(),
        }
    }
}

#[cfg(test)]
mod tests {
    use assert_matches::assert_matches;

    use super::*;
    use crate::{diff::diff, MerkleSearchTree};

    #[test]
    fn test_owned_usage() {
        let mut a = MerkleSearchTree::default();
        let mut b = MerkleSearchTree::default();

        a.upsert("bananas", &42);
        b.upsert("bananas", &24);

        // Rehash the tree
        let _ = a.root_hash();
        let _ = b.root_hash();

        // Generate owned snapshots from the borrowed page ranges
        let snap_a = PageRangeSnapshot::from(a.serialise_page_ranges().unwrap());
        let snap_b = PageRangeSnapshot::from(b.serialise_page_ranges().unwrap());

        // Tree should be mutable whilst snapshots are in scope
        a.upsert("bananas", &13);
        b.upsert("bananas", &13);

        // Which should be usable for diff generation (and not reflect the
        // updated state since the trees were mutated).
        assert_matches!(diff(snap_a.iter(), snap_b.iter()).as_slice(), [range] => {
            assert_eq!(range.start(), &"bananas");
            assert_eq!(range.end(), &"bananas");
        });
    }

    #[test]
    fn test_collect_equivalence_refs() {
        let a1 = vec![
            PageRange::new(
                &"a",
                &"b",
                PageDigest::new([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]),
            ),
            PageRange::new(
                &"c",
                &"d",
                PageDigest::new([2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]),
            ),
        ];

        let a2 = a1.clone().into_iter().collect::<PageRangeSnapshot<_>>();
        let a1 = PageRangeSnapshot::from(a1);

        assert_eq!(a1, a2)
    }

    #[test]
    fn test_collect_equivalence_owned() {
        let a1 = vec![
            OwnedPageRange::new(
                "a",
                "b",
                PageDigest::new([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]),
            ),
            OwnedPageRange::new(
                "c",
                "d",
                PageDigest::new([2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]),
            ),
        ];

        let a2 = a1.clone().into_iter().collect::<PageRangeSnapshot<_>>();
        let a1 = PageRangeSnapshot::from(a1);

        assert_eq!(a1, a2)
    }

    #[test]
    fn test_owned_ref_page_equivalence() {
        let ref_pages = [
            PageRange::new(
                &"a",
                &"b",
                PageDigest::new([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]),
            ),
            PageRange::new(
                &"c",
                &"d",
                PageDigest::new([2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]),
            ),
        ];

        let owned_pages = [
            OwnedPageRange::new(
                "a",
                "b",
                PageDigest::new([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]),
            ),
            OwnedPageRange::new(
                "c",
                "d",
                PageDigest::new([2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]),
            ),
        ];

        let ref_pages = ref_pages.into_iter().collect::<PageRangeSnapshot<_>>();
        let owned_pages = owned_pages.into_iter().collect::<PageRangeSnapshot<_>>();

        assert_eq!(ref_pages, owned_pages);
    }

    #[test]
    fn test_exact_size_iter() {
        let pages = [
            PageRange::new(
                &"a",
                &"b",
                PageDigest::new([1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1]),
            ),
            PageRange::new(
                &"c",
                &"d",
                PageDigest::new([2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2]),
            ),
        ];

        let pages = pages.into_iter().collect::<PageRangeSnapshot<_>>();
        assert_eq!(pages.iter().len(), 2);
    }
}
