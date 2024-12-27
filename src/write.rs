//! Shared macros for writing arbitrary-precision integers.

/// Convert a digit to a character.
#[inline(always)]
pub(crate) const fn digit_to_char(digit: u32, radix: u32) -> u8 {
    if radix <= 10 || digit < 10 {
        // Can short-circuit if we know the radix is small at compile time.
        digit as u8 + b'0'
    } else {
        digit as u8 + b'A' - 10
    }
}

#[doc(hidden)]
#[macro_export]
macro_rules! to_str_radix_define {
    ($is_signed:expr) => {
        /// Write the integer to bytes for the given integer.
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
        /// This function panics if `radix` is not in the range from 2 to 36,
        /// or the buffer isn't large enough to hold the significant digits.
        #[inline]
        pub fn to_str_radix(mut self, buffer: &mut [u8], radix: u32) -> &[u8] {
            if !(2..=36).contains(&radix) {
                core::panic!("from_str_radix_int: must lie in the range `[2, 36]`");
            }
            if buffer.len() < Self::BITS as usize + $is_signed as usize {
                core::panic!(
                    "must provide at least Self::BITS (+1 if signed) bytes to the buffer."
                );
            }

            // get the start of our buffer
            let is_negative = $is_signed && self.lt_const(Self::from_u8(0));
            let start_index = if is_negative {
                2
            } else {
                1
            };

            // This isn't optimized at all.
            let mut rem: u64;
            let mut index = buffer.len();
            let limit = Self::from_u32(radix);
            while self.ge_const(limit) && index > start_index {
                index -= 1;
                (self, rem) = self.div_rem_ulimb(radix as ULimb);
                buffer[index] = $crate::write::digit_to_char(rem as u32, radix);
            }

            // always have one trailing digit
            index -= 1;
            buffer[index] = $crate::write::digit_to_char(self.get_limb(0) as u32, radix);

            // write our negative sign, if required
            if is_negative {
                index -= 1;
                buffer[index] = b'-';
            }

            &buffer[index..]
        }
    };
}
