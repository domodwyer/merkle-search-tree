mod diff_builder;
mod range_list;

use std::fmt::Display;

use crate::{digest::PageDigest, Page};

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
