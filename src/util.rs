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

    (mn $name:ident, $bit64:ident, $bit32:ident, $t1:ty, $t2:ty, ret => $ret:ty) => {
        #[inline(always)]
        pub const fn $name<const M: usize, const N: usize>(x: $t1, y: $t2) -> $ret {
            #[cfg(all(not(feature = "limb32"), target_pointer_width = "64"))]
            let result = $bit64(x, y);

            #[cfg(any(feature = "limb32", not(target_pointer_width = "64")))]
            let result = $bit32(x, y);

            result
        }
    };

    (mn $name:ident, $bit64:ident, $bit32:ident, $t:ty, ret => $ret:ty) => {
        limb_function!(mn $name, $bit64, $bit32, $t, $t, ret => $ret);
    };
}

/// No-op, this is meant for 32-bit ISAs.
#[inline(always)]
#[cfg(feature = "stdint")]
#[cfg(all(not(feature = "limb32"), target_pointer_width = "64"))]
pub(crate) const fn u128_to_limb(value: u128) -> [u64; 2] {
    _ = value;
    unimplemented!();
}

/// Simple, safe transmute to ensure we transmute the value to native order.
#[inline(always)]
#[cfg(feature = "stdint")]
#[allow(clippy::assertions_on_constants)]
#[cfg(any(feature = "limb32", not(target_pointer_width = "64")))]
pub(crate) const fn u128_to_limb(value: u128) -> [u32; 4] {
    assert!(crate::ULimb::BITS == 32);

    let bytes = value.to_ne_bytes();
    // SAFETY: Safe since plain old data
    unsafe { core::mem::transmute::<[u8; 16], [u32; 4]>(bytes) }
}

/// No-op, this is meant for 32-bit ISAs.
#[inline(always)]
#[cfg(feature = "stdint")]
#[cfg(all(not(feature = "limb32"), target_pointer_width = "64"))]
pub(crate) const fn u128_to_limb_n<const N: usize>(value: u128) -> [u64; N] {
    _ = value;
    unimplemented!();
}

/// Simple, safe transmute to ensure we transmute the value to native order
/// at a fixed with.
#[inline(always)]
#[cfg(feature = "stdint")]
#[allow(clippy::assertions_on_constants)]
#[cfg(any(feature = "limb32", not(target_pointer_width = "64")))]
pub(crate) const fn u128_to_limb_n<const N: usize>(value: u128) -> [u32; N] {
    assert!(crate::ULimb::BITS == 32);
    assert!(N > 4);

    let mut result = [0; N];
    ne_index!(result[0] = value as u32);
    ne_index!(result[1] = (value >> 96) as u32);
    ne_index!(result[2] = (value >> 64) as u32);
    ne_index!(result[3] = (value >> 32) as u32);

    result
}

/// No-op, this is meant for 32-bit ISAs.
#[inline(always)]
#[cfg(feature = "stdint")]
#[cfg(all(not(feature = "limb32"), target_pointer_width = "64"))]
pub(crate) const fn i128_to_limb_n<const N: usize>(value: i128) -> [u64; N] {
    _ = value;
    unimplemented!();
}

/// Simple, safe transmute to ensure we transmute the value to native order
/// at a fixed with.
#[inline(always)]
#[cfg(feature = "stdint")]
#[allow(clippy::assertions_on_constants)]
#[cfg(any(feature = "limb32", not(target_pointer_width = "64")))]
pub(crate) const fn i128_to_limb_n<const N: usize>(value: i128) -> [u32; N] {
    assert!(crate::ULimb::BITS == 32);
    assert!(N > 4);

    let sign_bit = u32::MIN.wrapping_sub(value.is_negative() as u32);
    let value = value as u128;
    let mut result = [sign_bit; N];
    ne_index!(result[0] = value as u32);
    ne_index!(result[1] = (value >> 96) as u32);
    ne_index!(result[2] = (value >> 64) as u32);
    ne_index!(result[3] = (value >> 32) as u32);

    result
}
