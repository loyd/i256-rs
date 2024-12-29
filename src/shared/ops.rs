//! Defines high-level operations, which respect overflow checks.

/// Define a generic op. This isn't exposed to the crate just so it's done
/// internally. This is intended to be used within the crate so the `*_signed`,
/// `*_unsigned` variants can be added.
///
/// This requires the `wrapping_*` and `overflowing_*` variants to be defined,
/// as well as `div_euclid` and `rem_euclid` to be defined.
#[rustfmt::skip]
macro_rules! define {
    (type => $t:ty,wide_type => $wide_t:ty) => {
        /// Raises self to the power of `exp`, using exponentiation by squaring.
        ///
        #[doc = concat!("See [`", stringify!($wide_t), "::pow`].")]
        #[inline]
        pub const fn pow(self, exp: u32) -> Self {
            if cfg!(not(have_overflow_checks)) {
                self.wrapping_pow(exp)
            } else {
                self.strict_pow(exp)
            }
        }

        /// Get the quotient and remainder of our big integer division.
        ///
        /// This allows storing of both the quotient and remainder without
        /// making repeated calls.
        ///
        /// # Panics
        ///
        /// This panics if the divisor is 0.
        #[inline(always)]
        pub fn div_rem(self, n: Self) -> (Self, Self) {
            if cfg!(not(have_overflow_checks)) {
                self.wrapping_div_rem(n)
            } else {
                match self.checked_div_rem(n) {
                    Some(v) => v,
                    _ => core::panic!("attempt to divide with overflow"),
                }
            }
        }
    };
}

pub(crate) use define;

macro_rules! traits {
    ($t:ty) => {
        impl Add for $t {
            type Output = Self;

            #[inline(always)]
            fn add(self, rhs: Self) -> Self::Output {
                if cfg!(not(have_overflow_checks)) {
                    self.wrapping_add(rhs)
                } else {
                    match self.checked_add(rhs) {
                        Some(v) => v,
                        _ => core::panic!("attempt to add with overflow"),
                    }
                }
            }
        }

        impl Div for $t {
            type Output = Self;

            #[inline(always)]
            fn div(self, rhs: Self) -> Self::Output {
                if cfg!(not(have_overflow_checks)) {
                    self.wrapping_div(rhs)
                } else {
                    match self.checked_div(rhs) {
                        Some(v) => v,
                        _ => core::panic!("attempt to divide with overflow"),
                    }
                }
            }
        }

        impl Mul for $t {
            type Output = $t;

            #[inline(always)]
            fn mul(self, rhs: Self) -> Self::Output {
                if cfg!(not(have_overflow_checks)) {
                    self.wrapping_mul(rhs)
                } else {
                    match self.checked_mul(rhs) {
                        Some(v) => v,
                        _ => core::panic!("attempt to multiply with overflow"),
                    }
                }
            }
        }

        impl Rem for $t {
            type Output = $t;

            #[inline(always)]
            fn rem(self, rhs: Self) -> Self::Output {
                if cfg!(not(have_overflow_checks)) {
                    self.wrapping_rem(rhs)
                } else {
                    match self.checked_rem(rhs) {
                        Some(v) => v,
                        _ => core::panic!("attempt to divide with overflow"),
                    }
                }
            }
        }

        impl Sub for $t {
            type Output = $t;

            #[inline(always)]
            fn sub(self, rhs: Self) -> Self::Output {
                if cfg!(not(have_overflow_checks)) {
                    self.wrapping_sub(rhs)
                } else {
                    match self.checked_sub(rhs) {
                        Some(v) => v,
                        _ => core::panic!("attempt to subtract with overflow"),
                    }
                }
            }
        }

        $crate::shared::traits::define! {
            type => $t, impl => Add, op => add, assign => AddAssign, assign_op => add_assign,
            type => $t, impl => Div, op => div, assign => DivAssign, assign_op => div_assign,
            type => $t, impl => Mul, op => mul, assign => MulAssign, assign_op => mul_assign,
            type => $t, impl => Rem, op => rem, assign => RemAssign, assign_op => rem_assign,
            type => $t, impl => Sub, op => sub, assign => SubAssign, assign_op => sub_assign,
        }

        impl Not for $t {
            type Output = $t;

            #[inline(always)]
            fn not(self) -> Self::Output {
                self.not_const()
            }
        }

        impl Shl for $t {
            type Output = Self;

            #[inline(always)]
            #[allow(clippy::suspicious_arithmetic_impl)]
            fn shl(self, other: Self) -> Self::Output {
                let shift = other.least_significant_limb() as u32 & u32::MAX;
                self.wrapping_shl(shift)
            }
        }

        impl Shr for $t {
            type Output = Self;

            #[inline(always)]
            #[allow(clippy::suspicious_arithmetic_impl)]
            fn shr(self, other: Self) -> Self::Output {
                let shift = other.least_significant_limb() as u32 & u32::MAX;
                self.wrapping_shr(shift)
            }
        }

        $crate::shared::traits::define! {
            ref => $t, impl => Not, op => not,
            ref => $t, impl => Shl, op => shl, args => other: &$t, ;
            ref => $t, impl => Shr, op => shr, args => other: &$t, ;
        }

        $crate::shared::traits::define! {
            type => $t, impl => Shl, op => shl,
            type => $t, impl => Shr, op => shr,
        }
    };
}

pub(crate) use traits;
