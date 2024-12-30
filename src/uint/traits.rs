//! Helpers and logic for working with traits.

macro_rules! define {
    (type => $t:ident,signed_type => $s_t:ty) => {
        $crate::shared::traits::define!(impl => $t);
        $crate::shared::shift::define! { big => $t, impl => $s_t }
        $crate::shared::shift::define! { reference => $t, impl => $s_t }

        impl core::fmt::Binary for $t {
            #[inline]
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
                let mut buffer = [0u8; Self::BITS as usize];
                let bytes = self.to_str_radix(&mut buffer, 2);
                let formatted = core::str::from_utf8(bytes).or_else(|_| Err(core::fmt::Error))?;
                if f.alternate() {
                    f.write_str("0b")?;
                }
                if let Some(width) = f.width() {
                    let c = f.fill();
                    let pad = width.saturating_sub(bytes.len());
                    for _ in 0..pad {
                        write!(f, "{c}")?;
                    }
                }
                core::write!(f, "{}", formatted)
            }
        }

        impl core::fmt::Display for $t {
            #[inline]
            #[allow(clippy::bind_instead_of_map)]
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
                let mut buffer = [0u8; Self::BITS as usize];
                let bytes = self.to_str_radix(&mut buffer, 10);
                let formatted = core::str::from_utf8(bytes).or_else(|_| Err(core::fmt::Error))?;
                core::write!(f, "{}", formatted)
            }
        }

        impl core::fmt::LowerHex for $t {
            #[inline]
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
                let mut buffer = [0u8; Self::BITS as usize];
                let count = self.to_str_radix(&mut buffer, 16).len();
                let lower = buffer.map(|x| x.to_ascii_lowercase());
                let bytes = &lower[buffer.len() - count..];
                let formatted = core::str::from_utf8(bytes).or_else(|_| Err(core::fmt::Error))?;
                if f.alternate() {
                    f.write_str("0x")?;
                }
                if let Some(width) = f.width() {
                    let c = f.fill();
                    let pad = width.saturating_sub(count);
                    for _ in 0..pad {
                        write!(f, "{c}")?;
                    }
                }
                f.write_str(formatted)
            }
        }

        impl core::fmt::UpperHex for $t {
            #[inline]
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
                let mut buffer = [0u8; Self::BITS as usize];
                let count = self.to_str_radix(&mut buffer, 16).len();
                let upper = buffer.map(|x| x.to_ascii_uppercase());
                let bytes = &upper[buffer.len() - count..];
                let formatted = core::str::from_utf8(bytes).or_else(|_| Err(core::fmt::Error))?;
                if f.alternate() {
                    f.write_str("0x")?;
                }
                if let Some(width) = f.width() {
                    let c = f.fill();
                    let pad = width.saturating_sub(count);
                    for _ in 0..pad {
                        write!(f, "{c}")?;
                    }
                }
                f.write_str(formatted)
            }
        }

        impl core::fmt::LowerExp for $t {
            #[inline]
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
                let mut buffer = [0u8; Self::BITS as usize];
                let bytes = self.to_str_radix(&mut buffer, 10);
                let formatted = core::str::from_utf8(&bytes[1..]);
                let formatted = formatted.or_else(|_| Err(core::fmt::Error))?;
                core::write!(f, "{}.{}e{}", bytes[0] as char, formatted, bytes.len() - 1)
            }
        }

        impl core::fmt::UpperExp for $t {
            #[inline]
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
                let mut buffer = [0u8; Self::BITS as usize];
                let bytes = self.to_str_radix(&mut buffer, 10);
                let formatted = core::str::from_utf8(&bytes[1..]);
                let formatted = formatted.or_else(|_| Err(core::fmt::Error))?;
                core::write!(f, "{}.{}E{}", bytes[0] as char, formatted, bytes.len() - 1)
            }
        }

        impl core::fmt::Octal for $t {
            #[inline]
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
                let mut buffer = [0u8; Self::BITS as usize];
                let bytes = self.to_str_radix(&mut buffer, 8);
                let formatted = core::str::from_utf8(bytes).or_else(|_| Err(core::fmt::Error))?;
                if f.alternate() {
                    f.write_str("0o")?;
                }
                if let Some(width) = f.width() {
                    let c = f.fill();
                    let pad = width.saturating_sub(bytes.len());
                    for _ in 0..pad {
                        write!(f, "{c}")?;
                    }
                }
                core::write!(f, "{}", formatted)
            }
        }

        impl core::str::FromStr for $t {
            type Err = $crate::ParseIntError;

            /// Parses a string s to return a value of this type.
            ///
            /// This is not optimized, since all optimization is done in
            /// the lexical implementation.
            #[inline]
            fn from_str(src: &str) -> Result<Self, $crate::ParseIntError> {
                // up to 39 digits can be stored in a `u128`, so less is always valid
                // meanwhile, 78 is good for all 256-bit integers. 32-bit architectures
                // on average have poor support for 128-bit operations so we try to use `u64`.
                if (cfg!(target_pointer_width = "16") || cfg!(target_pointer_width = "32"))
                    && src.len() < 20
                {
                    Ok(Self::from_u64(u64::from_str(src)?))
                } else if src.len() < 39 {
                    Ok(Self::from_u128(u128::from_str(src)?))
                } else {
                    Self::from_str_radix(src, 10)
                }
            }
        }

        $crate::shared::traits::define! {
            to => $t, tryfrom => i8, op => from_i8,
            to => $t, tryfrom => i16, op => from_i16,
            to => $t, tryfrom => i32, op => from_i32,
            to => $t, tryfrom => i64, op => from_i64,
            to => $t, tryfrom => i128, op => from_i128,
        }

        impl TryFrom<$s_t> for $t {
            type Error = $crate::TryFromIntError;

            #[inline(always)]
            fn try_from(u: $s_t) -> Result<Self, $crate::TryFromIntError> {
                if !u.is_negative() {
                    Ok(u.as_unsigned())
                } else {
                    Err($crate::TryFromIntError {})
                }
            }
        }
    };
}

pub(crate) use define;
