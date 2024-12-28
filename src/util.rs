//! Miscellaneous utilities.

/// Convert our index to a native-endian one.
///
/// This indexes from the least-significant element, or for
/// big-endian, this means indexing from the right end, and little-
/// endian from the left.
#[inline(always)]
pub(crate) const fn to_ne_index(index: usize, n: usize) -> usize {
    if cfg!(target_endian = "big") {
        n - 1 - index
    } else {
        index
    }
}

/// Get a value at the index, assuming the native endian order.
///
/// This indexes from the least-significant element, or for
/// big-endian, this means indexing from the right end, and little-
/// endian from the left.
#[inline(always)]
pub(crate) const fn ne_index<T: Copy, const N: usize>(array: &[T; N], index: usize) -> T {
    array[to_ne_index(index, N)]
}
