//! Shared macros for parsing arbitrary-precision integers.

/// Get the maximum number of digits before the slice will overflow.
///
/// This is effectively the floor(log(2**BITS-1, radix)), but we can
/// try to go a bit lower without worrying too much.
#[inline(always)]
pub(crate) const fn overflow_digits<T>(radix: u32, is_signed: bool) -> usize {
    // this is heavily optimized for base10 and it's a way under estimate
    // that said, it's fast and works.
    if radix <= 16 {
        core::mem::size_of::<T>() * 2 - is_signed as usize
    } else {
        // way under approximation but always works and is fast
        core::mem::size_of::<T>()
    }
}

/// Convert a character to a digit.
#[inline(always)]
pub(crate) const fn char_to_digit(c: u8, radix: u32) -> Option<u32> {
    let digit = if radix <= 10 {
        // Optimize for small radixes.
        (c.wrapping_sub(b'0')) as u32
    } else {
        // Fallback, still decently fast.
        let digit = match c {
            b'0'..=b'9' => c - b'0',
            b'A'..=b'Z' => c - b'A' + 10,
            b'a'..=b'z' => c - b'a' + 10,
            _ => 0xFF,
        };
        digit as u32
    };
    if digit < radix {
        Some(digit)
    } else {
        None
    }
}

// cannot overflow the buffer, no overflow checking
#[macro_export]
macro_rules! unchecked_loop {
    ($t:ty, $digits:ident, $radix:ident, $index:ident, $add_op:ident) => {{
        use $crate::parse::char_to_digit;
        use $crate::{IntErrorKind, ParseIntError, ULimb, UWide};

        let digits = $digits;
        let radix = $radix;
        let mut res = <$t>::from_u8(0);
        let mut index = $index;

        while index < digits.len() {
            let digit = match char_to_digit(digits[index], radix) {
                Some(v) => v,
                None => return Err(ParseIntError::new(IntErrorKind::InvalidDigit)),
            };
            res = res.wrapping_mul_ulimb(radix as ULimb).$add_op(digit as UWide);
            index += 1;
        }

        Ok(res)
    }};
}

// can overflow the buffer, uses overflow checking
#[macro_export]
macro_rules! checked_loop {
    ($t:ty, $digits:ident, $radix:ident, $index:ident, $overflow:ident, $add_op:ident) => {{
        use $crate::parse::char_to_digit;
        use $crate::{IntErrorKind, ParseIntError, ULimb, UWide};

        let digits = $digits;
        let radix = $radix;
        let mut res = <$t>::from_u8(0);
        let mut index = $index;

        while index < digits.len() {
            let digit = match char_to_digit(digits[index], radix) {
                Some(v) => v,
                None => return Err(ParseIntError::new(IntErrorKind::InvalidDigit)),
            };
            let value = match res.checked_mul_ulimb(radix as ULimb) {
                Some(v) => v,
                None => return Err(ParseIntError::new(IntErrorKind::$overflow)),
            };
            res = match value.$add_op(digit as UWide) {
                Some(v) => v,
                None => return Err(ParseIntError::new(IntErrorKind::$overflow)),
            };
            index += 1;
        }

        Ok(res)
    }};
}

#[macro_export]
macro_rules! from_str_radix_define {
    ($is_signed:expr) => {
        /// Converts a string slice in a given base to an integer.
        ///
        /// The string is expected to be an optional `+`
        /// sign followed by only digits. Leading and trailing non-digit characters
        /// (including whitespace) represent an error. Underscores (which are
        /// accepted in rust literals) also represent an error.
        ///
        /// Digits are a subset of these characters, depending on `radix`:
        /// * `0-9`
        /// * `a-z`
        /// * `A-Z`
        ///
        /// This only has rudimentary optimizations.
        ///
        /// # Panics
        ///
        /// This function panics if `radix` is not in the range from 2 to 36.
        #[inline]
        pub const fn from_str_radix(
            src: &str,
            radix: u32,
        ) -> Result<Self, $crate::error::ParseIntError> {
            use $crate::error::{IntErrorKind, ParseIntError};
            use $crate::parse::overflow_digits;
            use $crate::{checked_loop, unchecked_loop};

            if radix < 2 || radix > 36 {
                panic!("from_str_radix_int: must lie in the range `[2, 36]`");
            }
            if src.is_empty() {
                return Err(ParseIntError::new(IntErrorKind::Empty));
            }

            // NOTE: Can't use for loops in const functions
            let digits = src.as_bytes();
            let mut index = 0;
            let is_negative = match digits.first() {
                Some(&b'+') => {
                    index += 1;
                    false
                },
                Some(&b'-') if $is_signed => {
                    index += 1;
                    true
                },
                Some(&b'-') => return Err(ParseIntError::new(IntErrorKind::NegOverflow)),
                _ => false,
            };
            let overflow_digits = overflow_digits::<Self>(radix, $is_signed);
            let cannot_overflow = (digits.len() - index) <= overflow_digits;

            if cannot_overflow && is_negative {
                unchecked_loop!(Self, digits, radix, index, wrapping_sub_uwide)
            } else if cannot_overflow {
                unchecked_loop!(Self, digits, radix, index, wrapping_add_uwide)
            } else if is_negative {
                checked_loop!(Self, digits, radix, index, NegOverflow, checked_sub_uwide)
            } else {
                checked_loop!(Self, digits, radix, index, PosOverflow, checked_add_uwide)
            }
        }
    };
}

pub(crate) use from_str_radix_define;
