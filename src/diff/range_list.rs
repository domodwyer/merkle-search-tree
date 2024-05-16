use std::fmt::Debug;

use super::DiffRange;

/// Helper to construct an ordered list of non-overlapping [`DiffRange`]
/// intervals.
#[derive(Debug)]
pub(crate) struct RangeList<'a, K> {
    sync_ranges: Vec<DiffRange<'a, K>>,
}

impl<'a, K> Default for RangeList<'a, K> {
    fn default() -> Self {
        Self {
            sync_ranges: Default::default(),
        }
    }
}

impl<'a, K> RangeList<'a, K>
where
    K: Ord,
{
    /// Insert the inclusive interval `[start, end]` into the list.
    pub(crate) fn insert(&mut self, start: &'a K, end: &'a K) {
        assert!(start <= end);
        self.sync_ranges.push(DiffRange { start, end });
    }

    /// Consume self and return the deduplicated/merged list of intervals
    /// ordered by range start.
    pub(crate) fn into_vec(mut self) -> Vec<DiffRange<'a, K>> {
        self.sync_ranges.sort_by_key(|v| v.start);
        merge_overlapping(&mut self.sync_ranges);

        // Check invariants in debug builds.
        #[cfg(debug_assertions)]
        {
            for v in self.sync_ranges.windows(2) {
                // Invariant: non-overlapping ranges
                assert!(!v[0].overlaps(&v[1]));
                // Invariant: end bound is always gte than start bound
                assert!(
                    v[0].start <= v[0].end,
                    "diff range contains inverted bounds"
                );
                assert!(
                    v[1].start <= v[1].end,
                    "diff range contains inverted bounds"
                );
            }
        }

        self.sync_ranges
    }
}

/// Perform an in-place merge and deduplication of overlapping intervals.
///
/// Assumes the intervals within `source` are sorted by the start value.
pub(super) fn merge_overlapping<K>(source: &mut Vec<DiffRange<'_, K>>)
where
    K: PartialOrd,
{
    let n_ranges = source.len();
    let mut range_iter = std::mem::take(source).into_iter();

    // Pre-allocate the ranges vec to hold all the elements, pessimistically
    // expecting them to not contain overlapping regions.
    source.reserve(n_ranges);

    // Place the first range into the merged output array.
    match range_iter.next() {
        Some(v) => source.push(v),
        None => return,
    }

    for range in range_iter {
        let last = source.last_mut().unwrap();

        // Invariant: ranges are sorted by range start.
        debug_assert!(range.start >= last.start);

        // Check if this range falls entirely within the existing range.
        if range.end <= last.end {
            // Skip this range that is a subset of the existing range.
            continue;
        }

        // Check for overlap across the end ranges (inclusive).
        if range.start <= last.end {
            // These two ranges overlap - extend the range in "last" to cover
            // both.
            last.end = range.end;
        } else {
            source.push(range);
        }
    }
}

#[cfg(test)]
mod tests {
    use proptest::prelude::*;

    use super::*;

    macro_rules! test_range_list_dedupe {
		(
			$name:ident,
			insert = [$($insert:expr),+],
			want = $want:expr
		) => {
			paste::paste! {
				#[test]
				fn [<test_range_list_dedupe_ $name>]() {
					let mut l = RangeList::default();

					$(
						l.insert(&$insert.0, &$insert.1);
					)+

					assert_eq!(l.into_vec().as_slice(), $want);
				}
			}
		}
	}

    test_range_list_dedupe!(
        single_overlapping_start,
        insert = [(1, 5), (2, 5)],
        want = [DiffRange { start: &1, end: &5 }]
    );

    test_range_list_dedupe!(
        single_overlapping_start_reversed,
        insert = [(2, 5), (1, 5)],
        want = [DiffRange { start: &1, end: &5 }]
    );

    test_range_list_dedupe!(
        single_overlapping_end,
        insert = [(2, 5), (2, 8)],
        want = [DiffRange { start: &2, end: &8 }]
    );

    test_range_list_dedupe!(
        single_overlapping_end_reversed,
        insert = [(2, 8), (2, 5)],
        want = [DiffRange { start: &2, end: &8 }]
    );

    test_range_list_dedupe!(
        superset,
        insert = [(2, 8), (1, 10)],
        want = [DiffRange {
            start: &1,
            end: &10
        }]
    );

    test_range_list_dedupe!(
        subset,
        insert = [(2, 8), (3, 4)],
        want = [DiffRange { start: &2, end: &8 }]
    );

    test_range_list_dedupe!(
        shifted_right,
        insert = [(2, 8), (3, 9)],
        want = [DiffRange { start: &2, end: &9 }]
    );

    test_range_list_dedupe!(
        shifted_left,
        insert = [(2, 8), (1, 7)],
        want = [DiffRange { start: &1, end: &8 }]
    );

    test_range_list_dedupe!(
        consecutive,
        insert = [(0, 2), (2, 42)],
        want = [DiffRange {
            start: &0,
            end: &42
        }]
    );

    test_range_list_dedupe!(
        iterative,
        insert = [(0, 1), (2, 4), (0, 3)],
        want = [DiffRange { start: &0, end: &4 }]
    );

    test_range_list_dedupe!(
        iterative_inclusive_bounds,
        insert = [(0, 1), (2, 4), (0, 2)],
        want = [DiffRange { start: &0, end: &4 }]
    );

    test_range_list_dedupe!(
        disjoint,
        insert = [(1, 2), (15, 42)],
        want = [
            DiffRange { start: &1, end: &2 },
            DiffRange {
                start: &15,
                end: &42
            }
        ]
    );

    test_range_list_dedupe!(
        look_back,
        insert = [(0, 0), (4_usize, 4_usize), (1, 4_usize)],
        want = [
            DiffRange { start: &0, end: &0 },
            DiffRange { start: &1, end: &4 }
        ]
    );

    test_range_list_dedupe!(
        prop_fail,
        insert = [
            (0, 2011493307964271930_usize),
            (3767576750200716450_usize, 3767576750200719913_usize),
            (2011500329124980022_usize, 3767576750200716450_usize),
            (3767576750200716450_usize, 3767576750200719913_usize)
        ],
        want = [
            DiffRange {
                start: &0,
                end: &2011493307964271930
            },
            DiffRange {
                start: &2011500329124980022,
                end: &3767576750200719913
            }
        ]
    );

    test_range_list_dedupe!(
        merge_identical_bounds,
        insert = [(2, 15), (2, 6), (2, 6)],
        want = [DiffRange {
            start: &2,
            end: &15
        }]
    );

    proptest! {
        #[test]
        fn prop_no_overlaps(pairs in prop::collection::vec(any::<(usize, usize)>(), 2..100)) {
            let mut list = RangeList::default();

            for (start, end) in &pairs {
                let mut start = start;
                let mut end = end;

                // Swap them around if start is bigger than end
                if start > end {
                    std::mem::swap(&mut start, &mut end);
                }

                list.insert(start, end);
            }

            list.into_vec();
        }
    }
}
