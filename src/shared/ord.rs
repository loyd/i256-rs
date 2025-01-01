//! Partial and total ordering.

// Due to wide comparison optimizations, this can be done in 1
// comparison on `x86_64` with the `u128` type, so we can
// optimize this quite nicely.
macro_rules! define {
    (
        @ord
        $lhs:ident,
        $rhs:ident,
        low_type => $lo_t:ty,
        high_type => $hi_t:ty,
        op1 => $op1:tt ,
        op2 => $op2:tt $(,)?
    ) => {{
        // The implied methods that are identical between short and non-circuiting options.
        let lhs = $lhs.to_ne_wide();
        let rhs = $rhs.to_ne_wide();

        let mut i = Self::WIDE - 1;
        let lhs_0 = ne_index!(lhs[i]) as $hi_t;
        let rhs_0 = ne_index!(rhs[i]) as $hi_t;
        let mut is_ord = lhs_0 $op1 rhs_0;
        let mut is_eq = lhs_0 == rhs_0;

        while i > 0 && !is_ord && is_eq {
            i -= 1;
            let lhs_i = ne_index!(lhs[i]) as $lo_t;
            let rhs_i = ne_index!(rhs[i]) as $lo_t;
            // NOTE: `<=/>=` OP only should be done in the last loop
            is_ord = if i == 0 {
                lhs_i $op2 rhs_i
            } else {
                lhs_i $op1 rhs_i
            };
            is_eq = lhs_i == rhs_i;
        }
        is_ord
    }};

    (
        low_type => $lo_t:ty,
        high_type => $hi_t:ty $(,)?
    ) => {
        /// Non-short circuiting const implementation of [`Eq`].
        #[inline(always)]
        const fn eq_branchless(self, rhs: Self) -> bool {
            let lhs = self.to_ne_wide();
            let rhs = rhs.to_ne_wide();
            let mut is_eq = true;
            let mut i = 0;
            while i < Self::WIDE {
                // NOTE: This can be in any order
                is_eq &= (lhs[i] == rhs[i]);
                i += 1;
            }
            is_eq
        }

        /// Short-circuiting const implementation of [`Eq`].
        #[inline(always)]
        pub const fn eq_branched(self, rhs: Self) -> bool {
            let lhs = self.to_ne_wide();
            let rhs = rhs.to_ne_wide();
            let mut is_eq = true;
            let mut i = 0;
            while i < Self::WIDE && is_eq {
                is_eq &= (lhs[i] == rhs[i]);
                i += 1;
            }
            is_eq
        }

        /// Non-short circuiting const implementation of [`Eq`].
        #[inline(always)]
        pub const fn eq_const(self, rhs: Self) -> bool {
            if Self::BITS < 4096 {
                self.eq_branchless(rhs)
            } else {
                self.eq_branched(rhs)
            }
        }

        // NOTE: Because of two's complement, these comparisons are always normal.
        // This can always be implemented in terms of the highest wide bit, then the
        // rest as low.

        /// Non-short circuiting const implementation of [`PartialOrd::lt`].
        #[inline(always)]
        #[must_use]
        pub const fn lt_const(self, rhs: Self) -> bool {
            $crate::shared::ord::define!(
                @ord
                self,
                rhs,
                low_type => $lo_t,
                high_type => $hi_t,
                op1 => <,
                op2 => <,
            )
        }

        /// Non-short circuiting const implementation of [`PartialOrd::le`].
        #[must_use]
        #[inline(always)]
        pub const fn le_const(self, rhs: Self) -> bool {
            $crate::shared::ord::define!(
                @ord
                self,
                rhs,
                low_type => $lo_t,
                high_type => $hi_t,
                op1 => <,
                op2 => <=,
            )
        }

        /// Non-short circuiting const implementation of [`PartialOrd::gt`].
        #[inline(always)]
        pub const fn gt_const(self, rhs: Self) -> bool {
            !self.le_const(rhs)
        }

        /// Non-short circuiting const implementation of [`PartialOrd::ge`].
        #[inline(always)]
        pub const fn ge_const(self, rhs: Self) -> bool {
            !self.lt_const(rhs)
        }

        /// Non-short circuiting const implementation of [`Ord::cmp`].
        #[inline(always)]
        pub const fn cmp_const(self, rhs: Self) -> core::cmp::Ordering {
            let lhs = self.to_ne_wide();
            let rhs = rhs.to_ne_wide();

            let mut i = Self::WIDE - 1;
            let lhs_0 = ne_index!(lhs[i]) as $hi_t;
            let rhs_0 = ne_index!(rhs[i]) as $hi_t;
            let mut is_eq = lhs_0 == rhs_0;
            let mut is_lt = lhs_0 < rhs_0;
            let mut is_gt = lhs_0 > rhs_0;

            while i > 0 && !is_lt && !is_gt && is_eq {
                i -= 1;
                let lhs_i = ne_index!(lhs[i]) as $lo_t;
                let rhs_i = ne_index!(rhs[i]) as $lo_t;
                is_eq = lhs_i == rhs_i;
                is_lt = lhs_i < rhs_i;
                is_gt = lhs_i > rhs_i;
            }

            if is_lt {
                core::cmp::Ordering::Less
            } else if is_gt {
                core::cmp::Ordering::Greater
            } else {
                core::cmp::Ordering::Equal
            }
        }
    };
}

pub(crate) use define;

macro_rules! traits {
    ($t:ty $(,)?) => {
        impl core::cmp::Ord for $t {
            #[inline(always)]
            fn cmp(&self, other: &Self) -> core::cmp::Ordering {
                self.cmp_const(*other)
            }
        }

        impl core::cmp::PartialOrd for $t {
            #[inline(always)]
            fn partial_cmp(&self, other: &Self) -> Option<core::cmp::Ordering> {
                Some(self.cmp(other))
            }

            #[inline(always)]
            fn lt(&self, other: &Self) -> bool {
                self.lt_const(*other)
            }

            #[inline(always)]
            fn le(&self, other: &Self) -> bool {
                self.le_const(*other)
            }

            #[inline(always)]
            fn gt(&self, other: &Self) -> bool {
                self.gt_const(*other)
            }

            #[inline(always)]
            fn ge(&self, other: &Self) -> bool {
                self.ge_const(*other)
            }
        }
    };
}

pub(crate) use traits;
