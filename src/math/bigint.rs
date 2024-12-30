//! Helpers analogous to the bigint features.
//!
//! These aim to be drop-in replacements for `bigint_helper_methods`.

// FIXME: Move to the Rust core implementation once stable.
macro_rules! define {
    (
        type =>
        $t:ty,wide =>
        $w:ty,add =>
        $add:ident,sub =>
        $sub:ident,mul =>
        $mul:ident,mac =>
        $mac:ident,signed => false
        $(,)?
    ) => {
        /// Calculates `self` + `rhs` + `carry` and checks for overflow.
        #[must_use]
        #[inline(always)]
        pub const fn $add(lhs: $t, rhs: $t, carry: bool) -> ($t, bool) {
            let (v, c0) = lhs.overflowing_add(rhs);
            let (v, c1) = v.overflowing_add(carry as $t);
            (v, c0 | c1)
        }

        /// Calculates `self` &minus; `rhs` &minus; `borrow` and checks for
        /// overflow.
        #[must_use]
        #[inline(always)]
        pub const fn $sub(lhs: $t, rhs: $t, borrow: bool) -> ($t, bool) {
            let (v, b0) = lhs.overflowing_sub(rhs);
            let (v, b1) = v.overflowing_sub(borrow as $t);
            (v, b0 | b1)
        }

        /// Calculates the "full multiplication" `self * rhs + carry`
        /// without the possibility to overflow.
        #[must_use]
        #[inline(always)]
        pub const fn $mul(lhs: $t, rhs: $t, carry: $t) -> ($t, $t) {
            let value = (lhs as $w) * (rhs as $w) + (carry as $w);
            (value as $t, (value >> <$t>::BITS) as $t)
        }

        /// Multiply/add/carry, or `a + (b * c) + carry`.
        #[must_use]
        #[inline(always)]
        pub const fn $mac(a: $t, b: $t, c: $t, carry: $t) -> ($t, $t) {
            let value = (a as $w) + (b as $w) * (c as $w) + (carry as $w);
            (value as $t, (value >> <$t>::BITS) as $t)
        }
    };

    (type => $t:ty,add => $add:ident,sub => $sub:ident,signed => true $(,)?) => {
        /// Calculates `self` + `rhs` + `carry` and checks for overflow.
        #[must_use]
        #[inline(always)]
        pub const fn $add(lhs: $t, rhs: $t, carry: bool) -> ($t, bool) {
            let (v, c0) = lhs.overflowing_add(rhs);
            let (v, c1) = v.overflowing_add(carry as $t);
            (v, c0 ^ c1)
        }

        /// Calculates `self` &minus; `rhs` &minus; `borrow` and checks for
        /// overflow.
        #[must_use]
        #[inline(always)]
        pub const fn $sub(lhs: $t, rhs: $t, borrow: bool) -> ($t, bool) {
            let (v, b0) = lhs.overflowing_sub(rhs);
            let (v, b1) = v.overflowing_sub(borrow as $t);
            (v, b0 ^ b1)
        }
    };
}

define!(
    type => u32,
    wide => u64,
    add => carrying_add_u32,
    sub => borrowing_sub_u32,
    mul => carrying_mul_u32,
    mac => mac_u32,
    signed => false,
);
define!(
    type => u64,
    wide => u128,
    add => carrying_add_u64,
    sub => borrowing_sub_u64,
    mul => carrying_mul_u64,
    mac => mac_u64,
    signed => false,
);
define!(
    type => i32,
    add => carrying_add_i32,
    sub => borrowing_sub_i32,
    signed => true,
);
define!(
    type => i64,
    add => carrying_add_i64,
    sub => borrowing_sub_i64,
    signed => true,
);
