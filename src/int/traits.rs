//! Helpers and logic for working with traits.

macro_rules! define {
    (
        type => $t:ident,
        unsigned_type => $u_t:ty $(,)?
    ) => {
        $crate::shared::traits::define!(impl => $t);
        $crate::shared::shift::define! { big => $t, impl => $u_t }
        $crate::shared::shift::define! { reference => $t, impl => $u_t }

        impl core::ops::Neg for $t {
            type Output = Self;

            #[inline(always)]
            fn neg(self) -> Self::Output {
                if cfg!(not(have_overflow_checks)) {
                    self.wrapping_neg()
                } else {
                    match self.checked_neg() {
                        Some(v) => v,
                        _ => core::panic!("attempt to negate with overflow"),
                    }
                }
            }
        }

        $crate::shared::traits::define!(ref => $t, impl => core::ops::Neg, op => neg,);

        impl core::str::FromStr for $t {
            type Err = $crate::ParseIntError;

            /// Parses a string s to return a value of this type.
            ///
            /// This is not optimized, since all optimization is done in
            /// theimplementation.
            #[inline]
            fn from_str(src: &str) -> Result<Self, $crate::ParseIntError> {
                // up to 39 digits can be stored in a `u128`, so less is always valid
                // meanwhile, 78 is good for all 256-bit integers. 32-bit architectures
                // on average have poor support for 128-bit operations so we try to use `u64`.
                if (cfg!(target_pointer_width = "16") || cfg!(target_pointer_width = "32"))
                    && src.len() < 19
                {
                    Ok(Self::from_i64(i64::from_str(src)?))
                } else if src.len() < 39 {
                    Ok(Self::from_i128(i128::from_str(src)?))
                } else {
                    Self::from_str_radix(src, 10)
                }
            }
        }

        impl core::fmt::Binary for $t {
            #[inline(always)]
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
                // NOTE: Binary for negative numbers uses wrapping formats.
                core::fmt::Binary::fmt(&self.as_unsigned(), f)
            }
        }

        impl core::fmt::Display for $t {
            #[inline]
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
                if self.is_negative() {
                    write!(f, "-")?;
                } else if f.sign_plus() {
                    write!(f, "+")?;
                }
                core::fmt::Display::fmt(&self.unsigned_abs(), f)
            }
        }

        impl core::fmt::LowerExp for $t {
            #[inline]
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
                if self.is_negative() {
                    write!(f, "-")?;
                } else if f.sign_plus() {
                    write!(f, "+")?;
                }
                core::fmt::LowerExp::fmt(&self.unsigned_abs(), f)
            }
        }

        impl core::fmt::LowerHex for $t {
            #[inline(always)]
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
                // NOTE: LowerHex for negative numbers uses wrapping formats.
                core::fmt::LowerHex::fmt(&self.as_unsigned(), f)
            }
        }

        impl core::fmt::Octal for $t {
            #[inline(always)]
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
                // NOTE: Octal for negative numbers uses wrapping formats.
                core::fmt::Octal::fmt(&self.as_unsigned(), f)
            }
        }

        impl core::fmt::UpperExp for $t {
            #[inline(always)]
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
                if self.is_negative() {
                    write!(f, "-")?;
                } else if f.sign_plus() {
                    write!(f, "+")?;
                }
                core::fmt::UpperExp::fmt(&self.unsigned_abs(), f)
            }
        }

        impl core::fmt::UpperHex for $t {
            #[inline(always)]
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
                // NOTE: UpperHex for negative numbers uses wrapping formats.
                core::fmt::UpperHex::fmt(&self.as_unsigned(), f)
            }
        }

        $crate::shared::traits::define! {
            to => $t, from => i8, op => from_i8,
            to => $t, from => i16, op => from_i16,
            to => $t, from => i32, op => from_i32,
            to => $t, from => i64, op => from_i64,
            to => $t, from => i128, op => from_i128,
        }

        impl TryFrom<$u_t> for $t {
            type Error = $crate::TryFromIntError;

            #[inline(always)]
            fn try_from(u: $u_t) -> Result<Self, $crate::TryFromIntError> {
                if u < Self::MAX.as_unsigned() {
                    Ok(u.as_signed())
                } else {
                    Err($crate::TryFromIntError {})
                }
            }
        }
    };
}

pub(crate) use define;
