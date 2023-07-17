use std::fmt::Debug;

use super::{
    range_list::{merge_overlapping, RangeList},
    DiffRange,
};

/// Helper to construct an ordered, minimal list of non-overlapping
/// [`DiffRange`] from a set of inconsistent intervals, and a set of consistent
/// intervals.
///
/// Range bounds are always inclusive.
///
/// Precedence is given towards the consistent list - if a single identical
/// range is marked both inconsistent and consistent, is is treated as a
/// consistent range.
#[derive(Debug)]
pub(crate) struct DiffListBuilder<'a, K> {
    inconsistent: RangeList<'a, K>,
    consistent: RangeList<'a, K>,
}

impl<'a, K> Default for DiffListBuilder<'a, K> {
    fn default() -> Self {
        Self {
            inconsistent: Default::default(),
            consistent: Default::default(),
        }
    }
}

impl<'a, K> DiffListBuilder<'a, K>
where
    K: Ord + Debug,
{
    /// Mark the inclusive range from `[start, end]` as inconsistent.
    pub(crate) fn inconsistent(&mut self, start: &'a K, end: &'a K) {
        debug!(?start, ?end, "marking range inconsistent");
        self.inconsistent.insert(start, end);
    }

    /// Mark the inclusive range from `[start, end]` as consistent.
    pub(crate) fn consistent(&mut self, start: &'a K, end: &'a K) {
        debug!(?start, ?end, "marking range as consistent");
        self.consistent.insert(start, end);
    }

    /// Consume this builder and return the deduplicated, minimised list of
    /// inconsistent ranges.
    pub(crate) fn into_diff_vec(self) -> Vec<DiffRange<'a, K>> {
        reduce_sync_range(self.inconsistent.into_vec(), self.consistent.into_vec())
    }
}

pub(crate) fn reduce_sync_range<'a, K>(
    mut bad_ranges: Vec<DiffRange<'a, K>>,
    consistent_ranges: Vec<DiffRange<'a, K>>,
) -> Vec<DiffRange<'a, K>>
where
    K: PartialOrd + Debug,
{
    // The output array of ranges that require syncing.
    //
    // This array should never contain any overlapping (before this call).

    for good in consistent_ranges {
        bad_ranges = bad_ranges
            .into_iter()
            .flat_map(|bad| {
                if !good.overlaps(&bad) {
                    return vec![bad];
                }

                let mut out = Vec::new();

                if bad.start < good.start {
                    out.push(DiffRange {
                        start: bad.start,
                        end: good.start,
                    });
                }

                if bad.end > good.end {
                    out.push(DiffRange {
                        start: good.end,
                        end: bad.end,
                    });
                }

                out
            })
            .collect();
    }

    // Merge overlapping ranges in the newly hole-punched ranges
    merge_overlapping(&mut bad_ranges);

    // Invariant: the output ranges contain no overlapping entries
    #[cfg(debug_assertions)]
    {
        for v in bad_ranges.windows(2) {
            assert!(!&v[0].overlaps(&v[1]));
        }
    }

    bad_ranges
}

#[cfg(test)]
mod tests {
    use super::*;

    use assert_matches::assert_matches;

    #[test]
    fn test_convergence_identical_bounds() {
        let mut list: DiffListBuilder<'_, usize> = DiffListBuilder::default();

        list.inconsistent(&2, &15);
        list.inconsistent(&2, &6);
        list.consistent(&2, &2);
        list.consistent(&5, &5);
        list.inconsistent(&2, &6);
        list.consistent(&15, &15);

        let list = list.into_diff_vec();
        assert_eq!(
            list,
            [DiffRange {
                start: &2,
                end: &15
            }]
        );
    }

    macro_rules! test_reduce_sync_range {
        (
            $name:ident,
            diff = $diff:expr,
            consistent_ranges = $consistent_ranges:expr,
            want = $($want:tt)+
        ) => {
            paste::paste! {
                #[test]
                fn [<test_reduce_sync_range_ $name>]() {
                    let got = reduce_sync_range($diff, $consistent_ranges);
                    assert_matches!(
                        got.as_slice(),
                        $($want)+
                    );
                }
            }
        }
    }

    test_reduce_sync_range!(
        middle,
        diff = vec![DiffRange {
            start: &4,
            end: &10,
        }],
        consistent_ranges = vec![DiffRange { start: &5, end: &8 }],
        want = [
            DiffRange { start: 4, end: 5 },
            DiffRange { start: 8, end: 10 },
        ]
    );

    test_reduce_sync_range!(
        right_edge,
        diff = vec![DiffRange {
            start: &4,
            end: &10,
        }],
        consistent_ranges = vec![DiffRange {
            start: &5,
            end: &10
        }],
        want = [DiffRange { start: 4, end: 5 }]
    );

    test_reduce_sync_range!(
        left_edge,
        diff = vec![DiffRange {
            start: &4,
            end: &10,
        }],
        consistent_ranges = vec![DiffRange { start: &4, end: &8 }],
        want = [DiffRange { start: 8, end: 10 }]
    );

    test_reduce_sync_range!(
        double_overlap,
        diff = vec![DiffRange {
            start: &4,
            end: &10,
        }],
        consistent_ranges = vec![
            DiffRange { start: &4, end: &6 },
            DiffRange { start: &6, end: &8 }
        ],
        want = [DiffRange { start: 8, end: 10 }]
    );

    test_reduce_sync_range!(
        complete_subtree_consistency,
        diff = vec![DiffRange {
            start: &4,
            end: &10,
        }],
        consistent_ranges = vec![
            DiffRange { start: &4, end: &6 },
            DiffRange {
                start: &6,
                end: &10
            }
        ],
        want = []
    );
}
