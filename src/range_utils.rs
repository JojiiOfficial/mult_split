use std::ops::Range;

/// Returns `true` if the ranges overlap.
#[inline]
pub fn ranges_overlap<O: Ord>(a: &Range<O>, b: &Range<O>) -> bool {
    a.start < b.end && a.end > b.start
}
