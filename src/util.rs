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
    ($array:ident $(.$sub:ident)* [$index:expr]) => {
        $array $(.$sub)* [$crate::util::to_ne_index($index, $array $(.$sub)* .len())]
    };

    ($array:ident $(.$sub:ident)* [$index:expr] = $value:expr) => {
        $array $(.$sub)* [$crate::util::to_ne_index($index, $array $(.$sub)* .len())] = $value
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

/// Conditionally implement a function correctly based on the types.
///
/// Note this also supports wide API methods, with the same overloads.
#[doc(hidden)]
#[macro_export]
macro_rules! limb_function {
    ($name:ident, $bit64:ident, $bit32:ident, $t1:ty, $t2:ty, ret => $ret:ty) => {
        #[inline(always)]
        pub const fn $name<const N: usize>(x: $t1, y: $t2) -> $ret {
            #[cfg(all(not(feature = "limb32"), target_pointer_width = "64"))]
            let result = $bit64(x, y);

            #[cfg(any(feature = "limb32", not(target_pointer_width = "64")))]
            let result = $bit32(x, y);

            result
        }
    };

    ($name:ident, $bit64:ident, $bit32:ident, $t:ty, ret => $ret:ty) => {
        limb_function!($name, $bit64, $bit32, $t, $t, ret => $ret);
    };
}
