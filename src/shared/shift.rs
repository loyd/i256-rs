//! Defines all our overloads for our bitshift operators.

macro_rules! define {
    (primitive => $base:ty, impl => $($t:ty)*) => ($(
        impl core::ops::Shl<$t> for $base {
            type Output = Self;

            #[inline(always)]
            #[allow(unused_comparisons)]
            #[allow(clippy::suspicious_arithmetic_impl)]
            fn shl(self, other: $t) -> Self::Output {
                if cfg!(have_overflow_checks) {
                    assert!(other < Self::BITS as $t && other >= 0, "attempt to shift left with overflow");
                }
                self.wrapping_shl(other as u32)
            }
        }

        impl core::ops::Shr<$t> for $base {
            type Output = Self;

            #[inline(always)]
            #[allow(unused_comparisons)]
            #[allow(clippy::suspicious_arithmetic_impl)]
            fn shr(self, other: $t) -> Self::Output {
                if cfg!(have_overflow_checks) {
                    assert!(other < Self::BITS as $t && other >= 0, "attempt to shift right with overflow");
                }
                self.wrapping_shr(other as u32)
            }
        }
    )*);

    (big => $base:ty, impl => $($t:ty)*) => ($(
        impl core::ops::Shl<$t> for $base {
            type Output = Self;

            #[inline(always)]
            #[allow(clippy::suspicious_arithmetic_impl)]
            fn shl(self, other: $t) -> Self::Output {
                if cfg!(have_overflow_checks) {
                    let is_above = other.ge_const(<$t>::from_u32(Self::BITS));
                    let is_below = other.lt_const(<$t>::from_u32(0));
                    let is_overflow = is_above || is_below;
                    assert!(!is_overflow, "attempt to shift left with overflow");
                }
                self.wrapping_shl(other.as_u32())
            }
        }

        impl core::ops::Shr<$t> for $base {
            type Output = Self;

            #[inline(always)]
            #[allow(clippy::suspicious_arithmetic_impl)]
            fn shr(self, other: $t) -> Self::Output {
                if cfg!(have_overflow_checks) {
                    let is_above = other.ge_const(<$t>::from_u32(Self::BITS));
                    let is_below = other.lt_const(<$t>::from_u32(0));
                    let is_overflow = is_above || is_below;
                    assert!(!is_overflow, "attempt to shift right with overflow");
                }
                self.wrapping_shr(other.as_u32())
            }
        }
    )*);

    (reference => $base:ty, impl => $($t:ty)*) => ($(
        impl core::ops::Shl<&$t> for $base {
            type Output = <Self as core::ops::Shl>::Output;

            #[inline(always)]
            #[allow(unused_imports)]
            fn shl(self, other: &$t) -> Self::Output {
                use core::ops::Shl;
                self.shl(*other)
            }
        }

        impl core::ops::ShlAssign<$t> for $base {
            #[inline(always)]
            #[allow(unused_imports)]
            fn shl_assign(&mut self, other: $t) {
                use core::ops::Shl;
                *self = self.shl(other);
            }
        }

        impl core::ops::ShlAssign<&$t> for $base {
            #[inline(always)]
            #[allow(unused_imports)]
            fn shl_assign(&mut self, other: &$t) {
                use core::ops::Shl;
                *self = self.shl(other);
            }
        }

        impl core::ops::Shr<&$t> for $base {
            type Output = <Self as core::ops::Shr>::Output;

            #[inline(always)]
            #[allow(unused_imports)]
            fn shr(self, other: &$t) -> Self::Output {
                use core::ops::Shr;
                self.shr(*other)
            }
        }

        impl core::ops::ShrAssign<$t> for $base {
            #[inline(always)]
            #[allow(unused_imports)]
            fn shr_assign(&mut self, other: $t) {
                use core::ops::Shr;
                *self = self.shr(other);
            }
        }

        impl core::ops::ShrAssign<&$t> for $base {
            #[inline(always)]
            #[allow(unused_imports)]
            fn shr_assign(&mut self, other: &$t) {
                use core::ops::Shr;
                *self = self.shr(other);
            }
        }
    )*);
}

pub(crate) use define;
