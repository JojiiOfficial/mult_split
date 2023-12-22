mod range_utils;

use std::collections::Bound;
use std::ops::{Range, RangeBounds};
use std::slice::{from_raw_parts, from_raw_parts_mut};

/// Allows safe multiple borrows of a given slice. This doesn't allow multiple mutable references of the same
/// area of the slice since this is UB.
pub struct MultiSplit<'a, T> {
    /// The slice to split into many parts.
    slice: &'a mut [T],

    /// Already borrowed ranges, so we don't borrow them again.
    borrows: Vec<Range<usize>>,
}

impl<'a, T> MultiSplit<'a, T> {
    /// Creates a new `MultiSplit` for the given slice.
    #[inline]
    pub fn new(slice: &'a mut [T]) -> Self {
        Self {
            slice,
            borrows: vec![],
        }
    }

    /// Tries to borrow `range` mutably.
    pub fn borrow_mut<R>(&mut self, range: R) -> Option<&'a mut [T]>
        where
            R: RangeBounds<usize>,
    {
        let range = self.resolve_range_bounds(&range);

        fn inner<'a, T>(ms: &mut MultiSplit<'a, T>, range: Range<usize>) -> Option<&'a mut [T]> {
            ms.can_borrow(&range).then_some(())?;
            ms.borrows.push(range.clone());

            // This is safe because we checked the range beforehand
            Some(unsafe { ms.borrow_mut_unchecked(&range) })
        }

        inner(self, range)
    }
    /// Tries to borrow `range` mutably.
    pub fn borrow<R>(&mut self, range: R) -> Option<&'a [T]>
        where
            R: RangeBounds<usize>,
    {
        let range = self.resolve_range_bounds(&range);

        fn inner<'a, T>(ms: &mut MultiSplit<'a, T>, range: Range<usize>) -> Option<&'a [T]> {
            ms.can_borrow(&range).then_some(())?;
            ms.borrows.push(range.clone());

            // This is safe because we checked the range beforehand
            Some(unsafe { ms.borrow_unchecked(&range) })
        }

        inner(self, range)
    }

    /// Returns `true` if the given range of the slice can be borrowed mutably.
    #[inline]
    pub fn can_borrow(&self, range: &Range<usize>) -> bool {
        self.in_bounds(range) && !self.already_borrowed(range)
    }

    /// Returns `true` if the given range is already (partly) borrowed. In that case the given range can't be used
    /// to borrow from the slice mutably.
    #[inline]
    pub fn already_borrowed(&self, range: &Range<usize>) -> bool {
        self.borrows
            .iter()
            .any(|i| range_utils::ranges_overlap(i, range))
    }

    /// Returns `true` if there is at least one borrow of the slice.
    #[inline]
    pub fn has_borrows(&self) -> bool {
        !self.borrows.is_empty()
    }

    /// Borrows the given range mutable without any checks.
    ///
    /// Safety:
    /// The caller must ensure that:
    ///   - the given range hasn't been borrowed already.
    ///   - the given range is within bounds of the slice.
    #[inline]
    unsafe fn borrow_mut_unchecked(&mut self, range: &Range<usize>) -> &'a mut [T] {
        assert!(range.start <= (isize::MAX as usize));
        let ptr = self.slice.as_mut_ptr().add(range.start);
        from_raw_parts_mut(ptr, range.len())
    }

    /// Borrows the given range without any checks.
    ///
    /// Safety:
    /// The caller must ensure that:
    ///   - the given range hasn't been borrowed already.
    ///   - the given range is within bounds of the slice.
    #[inline]
    unsafe fn borrow_unchecked(&mut self, range: &Range<usize>) -> &'a [T] {
        assert!(range.start <= (isize::MAX as usize));
        let ptr = self.slice.as_mut_ptr().add(range.start);
        from_raw_parts(ptr, range.len())
    }

    /// Returns `true` if `range` is within the bounds of the slice.
    #[inline]
    fn in_bounds(&self, range: &Range<usize>) -> bool {
        range.end <= self.slice.len() && range.start <= range.end
    }

    /// Resolves a given RangeBounds<usize> to a range within the slice.
    fn resolve_range_bounds<R: RangeBounds<usize>>(&self, range: &R) -> Range<usize> {
        let start = match range.start_bound() {
            Bound::Included(i) => *i,
            Bound::Excluded(i) => *i + 1,
            Bound::Unbounded => 0,
        };

        let end = match range.end_bound() {
            Bound::Included(i) => *i + 1,
            Bound::Excluded(i) => *i,
            Bound::Unbounded => self.slice.len(),
        };

        start..end
    }
}

impl<'a, T> From<&'a mut [T]> for MultiSplit<'a, T> {
    #[inline]
    fn from(value: &'a mut [T]) -> Self {
        Self::new(value)
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn split() {
        let data: &mut [u32] = &mut [1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
        let ndata = data.to_vec();

        let mut ms = MultiSplit::new(data);

        assert_eq!(ms.borrow(0..5), Some(&ndata[0..5]));

        // Second borrow of that range returns `None`!
        assert_eq!(ms.borrow(0..5), None);

        assert_eq!(ms.borrow(5..6), Some(&ndata[5..6]));

        assert_eq!(ms.borrow(6..), Some(&ndata[6..]));
    }

    #[test]
    fn full() {
        let data: &mut [u32] = &mut [1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
        let odata = data.to_vec();

        let mut ms = MultiSplit::new(data);
        assert_eq!(ms.borrow(..), Some(odata.as_slice()));
    }

    #[test]
    fn mutate() {
        let original = vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10];

        let mut data1 = original.clone();
        let data1: &mut [u32] = &mut data1;

        let mut data2 = original.clone();
        let data2: &mut [u32] = &mut data2;

        let ms1 = MultiSplit::new(data1);
        let ms2 = MultiSplit::from(data2);

        assert_eq!(ms1.slice, ms2.slice);
    }

    #[test]
    fn has_borrowed() {
        let data: &mut [u32] = &mut [1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
        let mut ms = MultiSplit::new(data);
        assert!(!ms.has_borrows());
        let b = ms.borrow_mut(0..=3).unwrap().to_vec();
        assert!(ms.has_borrows());
        assert_eq!(b, &data[0..=3]);
    }

    #[test]
    fn exclude_first() {
        let data: &mut [u32] = &mut [1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
        let odata = data.to_vec();
        let mut ms = MultiSplit::new(data);

        let r = (Bound::Excluded(1), Bound::Excluded(odata.len()));
        let sub = ms.borrow(r);
        assert_eq!(sub, Some(&odata[2..]))
    }
}
