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

/// Index a value, using native indexing.
#[doc(hidden)]
#[macro_export]
macro_rules! ne_index {
    ($array:ident[$index:expr]) => {
        $array[$crate::util::to_ne_index($index, $array.len())]
    };

    ($array:ident[$index:expr] = $value:expr) => {
        $array[$crate::util::to_ne_index($index, $array.len())] = $value
    };
}
