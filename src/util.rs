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

/// Swap the order of limbs, useful for re-arranging for BE/LE order.
#[doc(hidden)]
#[macro_export]
macro_rules! swap_array {
    ($value:expr) => {{
        let value = $value;
        let mut res = value;
        let mut i = 0;
        while i < value.len() {
            res[i] = value[value.len() - i - 1];
            i += 1;
        }
        res
    }};
}
