#[macro_use]
mod util;

use quickcheck::quickcheck;

quickcheck! {
    fn u256_wrapping_add_quickcheck(x0: u128, x1: u128, y0: u128, y1: u128) -> bool {
        unsigned_op_equal!(wrap x0, x1, y0, y1, wrapping_add)
    }

    fn u256_wrapping_sub_quickcheck(x0: u128, x1: u128, y0: u128, y1: u128) -> bool {
        unsigned_op_equal!(wrap x0, x1, y0, y1, wrapping_sub)
    }

    fn u256_wrapping_mul_quickcheck(x0: u128, x1: u128, y0: u128, y1: u128) -> bool {
        unsigned_op_equal!(wrap x0, x1, y0, y1, wrapping_mul)
    }

    fn u256_abs_diff_quickcheck(x0: u128, x1: u128, y0: u128, y1: u128) -> bool {
        unsigned_op_equal!(wrap x0, x1, y0, y1, abs_diff)
    }

    fn u256_wrapping_div_quickcheck(x0: u128, x1: u128, y0: u128, y1: u128) -> bool {
        if y0 != 0 && y1 != 0 {
            unsigned_op_equal!(wrap x0, x1, y0, y1, wrapping_div)
        } else {
            true
        }
    }

    fn u256_wrapping_rem_quickcheck(x0: u128, x1: u128, y0: u128, y1: u128) -> bool {
        if y0 != 0 && y1 != 0 {
            unsigned_op_equal!(wrap x0, x1, y0, y1, wrapping_rem)
        } else {
            true
        }
    }

    fn u256_div_floor_quickcheck(x0: u128, x1: u128, y0: u128, y1: u128) -> bool {
        if y0 != 0 && y1 != 0 {
            unsigned_op_equal!(wrap x0, x1, y0, y1, div_floor)
        } else {
            true
        }
    }

    fn u256_div_ceil_quickcheck(x0: u128, x1: u128, y0: u128, y1: u128) -> bool {
        if y0 != 0 && y1 != 0 {
            unsigned_op_equal!(wrap x0, x1, y0, y1, div_ceil)
        } else {
            true
        }
    }

    fn u256_overflowing_add_quickcheck(x0: u128, x1: u128, y0: u128, y1: u128) -> bool {
        unsigned_op_equal!(over x0, x1, y0, y1, overflowing_add)
    }

    fn u256_overflowing_sub_quickcheck(x0: u128, x1: u128, y0: u128, y1: u128) -> bool {
        unsigned_op_equal!(over x0, x1, y0, y1, overflowing_sub)
    }

    fn u256_overflowing_mul_quickcheck(x0: u128, x1: u128, y0: u128, y1: u128) -> bool {
        unsigned_op_equal!(over x0, x1, y0, y1, overflowing_mul)
    }

    fn u256_overflowing_div_quickcheck(x0: u128, x1: u128, y0: u128, y1: u128) -> bool {
        if y0 != 0 && y1 != 0 {
            unsigned_op_equal!(over x0, x1, y0, y1, overflowing_div)
        } else {
            true
        }
    }

    fn u256_overflowing_rem_quickcheck(x0: u128, x1: u128, y0: u128, y1: u128) -> bool {
        if y0 != 0 && y1 != 0 {
            unsigned_op_equal!(over x0, x1, y0, y1, overflowing_rem)
        } else {
            true
        }
    }

    fn u256_overflowing_div_euclid_quickcheck(x0: u128, x1: u128, y0: u128, y1: u128) -> bool {
        if y0 != 0 && y1 != 0 {
            unsigned_op_equal!(over x0, x1, y0, y1, overflowing_div_euclid)
        } else {
            true
        }
    }

    fn u256_overflowing_rem_euclid_quickcheck(x0: u128, x1: u128, y0: u128, y1: u128) -> bool {
        if y0 != 0 && y1 != 0 {
            unsigned_op_equal!(over x0, x1, y0, y1, overflowing_rem_euclid)
        } else {
            true
        }
    }

    fn u256_checked_add_quickcheck(x0: u128, x1: u128, y0: u128, y1: u128) -> bool {
        unsigned_op_equal!(check x0, x1, y0, y1, checked_add)
    }

    fn u256_checked_sub_quickcheck(x0: u128, x1: u128, y0: u128, y1: u128) -> bool {
        unsigned_op_equal!(check x0, x1, y0, y1, checked_sub)
    }

    fn u256_checked_mul_quickcheck(x0: u128, x1: u128, y0: u128, y1: u128) -> bool {
        unsigned_op_equal!(check x0, x1, y0, y1, checked_mul)
    }

    fn u256_saturating_add_quickcheck(x0: u128, x1: u128, y0: u128, y1: u128) -> bool {
        unsigned_op_equal!(wrap x0, x1, y0, y1, saturating_add)
    }

    fn u256_saturating_sub_quickcheck(x0: u128, x1: u128, y0: u128, y1: u128) -> bool {
        unsigned_op_equal!(wrap x0, x1, y0, y1, saturating_sub)
    }

    fn u256_saturating_mul_quickcheck(x0: u128, x1: u128, y0: u128, y1: u128) -> bool {
        unsigned_op_equal!(wrap x0, x1, y0, y1, saturating_mul)
    }

    fn u256_checked_next_multiple_of_quickcheck(x0: u128, x1: u128, y0: u128, y1: u128) -> bool {
        if y0 != 0 && y1 != 0 {
            unsigned_op_equal!(check x0, x1, y0, y1, checked_next_multiple_of)
        } else {
            true
        }
    }

    fn u256_checked_div_quickcheck(x0: u128, x1: u128, y0: u128, y1: u128) -> bool {
        if y0 != 0 && y1 != 0 {
            unsigned_op_equal!(check x0, x1, y0, y1, checked_div)
        } else {
            true
        }
    }

    fn u256_checked_rem_quickcheck(x0: u128, x1: u128, y0: u128, y1: u128) -> bool {
        if y0 != 0 && y1 != 0 {
            unsigned_op_equal!(check x0, x1, y0, y1, checked_rem)
        } else {
            true
        }
    }

    fn u256_checked_shl_quickcheck(x0: u128, x1: u128, y: u32) -> bool {
        unsigned_op_equal!(check x0, x1, y, checked_shl)
    }

    fn u256_checked_shr_quickcheck(x0: u128, x1: u128, y: u32) -> bool {
        unsigned_op_equal!(check x0, x1, y, checked_shr)
    }

    fn u256_wrapping_shl_quickcheck(x0: u128, x1: u128, y: u32) -> bool {
        unsigned_op_equal!(wrap x0, x1, y, wrapping_shl)
    }

    fn u256_wrapping_shr_quickcheck(x0: u128, x1: u128, y: u32) -> bool {
        unsigned_op_equal!(wrap x0, x1, y, wrapping_shr)
    }

    fn u256_checked_pow_quickcheck(x0: u128, x1: u128, y: u32) -> bool {
        unsigned_op_equal!(check x0, x1, y, checked_pow)
    }

    fn u256_count_ones_quickcheck(x0: u128, x1: u128) -> bool {
        unsigned_op_equal!(scalar x0, x1, count_ones)
    }

    fn u256_count_zeros_quickcheck(x0: u128, x1: u128) -> bool {
        unsigned_op_equal!(scalar x0, x1, count_zeros)
    }

    fn u256_leading_zeros_quickcheck(x0: u128, x1: u128) -> bool {
        unsigned_op_equal!(scalar x0, x1, leading_zeros)
    }

    fn u256_leading_ones_quickcheck(x0: u128, x1: u128) -> bool {
        unsigned_op_equal!(scalar x0, x1, leading_ones)
    }

    fn u256_trailing_zeros_quickcheck(x0: u128, x1: u128) -> bool {
        unsigned_op_equal!(scalar x0, x1, trailing_zeros)
    }

    fn u256_trailing_ones_quickcheck(x0: u128, x1: u128) -> bool {
        unsigned_op_equal!(scalar x0, x1, trailing_ones)
    }

    fn u256_swap_bytes_quickcheck(x0: u128, x1: u128) -> bool {
        unsigned_op_equal!(wrap x0, x1, swap_bytes)
    }

    fn u256_reverse_bits_quickcheck(x0: u128, x1: u128) -> bool {
        unsigned_op_equal!(wrap x0, x1, reverse_bits)
    }

    fn u256_wrapping_neg_quickcheck(x0: u128, x1: u128) -> bool {
        unsigned_op_equal!(wrap x0, x1, wrapping_neg)
    }

    fn u256_rotate_left_quickcheck(x0: u128, x1: u128, y: u32) -> bool {
        unsigned_op_equal!(wrap x0, x1, y, rotate_left)
    }

    fn u256_rotate_right_quickcheck(x0: u128, x1: u128, y: u32) -> bool {
        unsigned_op_equal!(wrap x0, x1, y, rotate_right)
    }

    fn u256_cast_signed_quickcheck(x0: u128, x1: u128) -> bool {
        unsigned_op_equal!(x0, x1, cast_signed, |x: util::Bi256, y: i256::i256| x.to_le_bytes() == y.to_le_bytes())
    }

    fn u256_ilog2_quickcheck(x0: u128, x1: u128) -> bool {
        let x1 = x1.max(1);
        unsigned_op_equal!(scalar x0, x1, ilog2)
    }

    fn u256_is_power_of_two_quickcheck(x0: u128, x1: u128) -> bool {
        unsigned_op_equal!(scalar x0, x1, is_power_of_two)
    }

    fn u256_wrapping_next_power_of_two_quickcheck(x0: u128, x1: u128) -> bool {
        unsigned_op_equal!(wrap x0, x1, wrapping_next_power_of_two)
    }

    fn u256_checked_next_power_of_two_quickcheck(x0: u128, x1: u128) -> bool {
        unsigned_op_equal!(check x0, x1, checked_next_power_of_two)
    }

    fn u256_wrapping_add_ulimb_quickcheck(x0: u128, x1: u128, y: i256::ULimb) -> bool {
        unsigned_limb_op_equal!(wrap x0, x1, y, wrapping_add, wrapping_add_ulimb)
    }

    fn u256_wrapping_add_uwide_quickcheck(x0: u128, x1: u128, y: i256::UWide) -> bool {
        unsigned_limb_op_equal!(wrap x0, x1, y, wrapping_add, wrapping_add_uwide)
    }

    fn u256_wrapping_sub_ulimb_quickcheck(x0: u128, x1: u128, y: i256::ULimb) -> bool {
        unsigned_limb_op_equal!(wrap x0, x1, y, wrapping_sub, wrapping_sub_ulimb)
    }

    fn u256_wrapping_sub_uwide_quickcheck(x0: u128, x1: u128, y: i256::UWide) -> bool {
        unsigned_limb_op_equal!(wrap x0, x1, y, wrapping_sub, wrapping_sub_uwide)
    }

    fn u256_wrapping_mul_ulimb_quickcheck(x0: u128, x1: u128, y: i256::ULimb) -> bool {
        unsigned_limb_op_equal!(wrap x0, x1, y, wrapping_mul, wrapping_mul_ulimb)
    }

    fn u256_wrapping_mul_uwide_quickcheck(x0: u128, x1: u128, y: i256::UWide) -> bool {
        unsigned_limb_op_equal!(wrap x0, x1, y, wrapping_mul, wrapping_mul_uwide)
    }

    fn u256_wrapping_div_ulimb_quickcheck(x0: u128, x1: u128, y: i256::ULimb) -> bool {
        if y != 0 {
            unsigned_limb_op_equal!(wrap x0, x1, y, wrapping_div, wrapping_div_ulimb)
        } else {
            true
        }
    }

    fn u256_wrapping_rem_ulimb_quickcheck(x0: u128, x1: u128, y: i256::ULimb) -> bool {
        if y != 0 {
            unsigned_limb_op_equal!(x0, x1, y, wrapping_rem, wrapping_rem_ulimb, |x, y| {
                x == i256::u256::from(y)
            })
        } else {
            true
        }
    }

    fn u256_wrapping_div_uwide_quickcheck(x0: u128, x1: u128, y: i256::UWide) -> bool {
        if y != 0 {
            unsigned_limb_op_equal!(wrap x0, x1, y, wrapping_div, wrapping_div_uwide)
        } else {
            true
        }
    }

    fn u256_wrapping_rem_uwide_quickcheck(x0: u128, x1: u128, y: i256::UWide) -> bool {
        if y != 0 {
            unsigned_limb_op_equal!(x0, x1, y, wrapping_rem, wrapping_rem_uwide, |x, y| {
                x == i256::u256::from(y)
            })
        } else {
            true
        }
    }

    fn u256_overflowing_add_ulimb_quickcheck(x0: u128, x1: u128, y: i256::ULimb) -> bool {
        unsigned_limb_op_equal!(over x0, x1, y, overflowing_add, overflowing_add_ulimb)
    }

    fn u256_overflowing_add_uwide_quickcheck(x0: u128, x1: u128, y: i256::UWide) -> bool {
        unsigned_limb_op_equal!(over x0, x1, y, overflowing_add, overflowing_add_uwide)
    }

    fn u256_overflowing_sub_ulimb_quickcheck(x0: u128, x1: u128, y: i256::ULimb) -> bool {
        unsigned_limb_op_equal!(over x0, x1, y, overflowing_sub, overflowing_sub_ulimb)
    }

    fn u256_overflowing_sub_uwide_quickcheck(x0: u128, x1: u128, y: i256::UWide) -> bool {
        unsigned_limb_op_equal!(over x0, x1, y, overflowing_sub, overflowing_sub_uwide)
    }

    fn u256_overflowing_mul_ulimb_quickcheck(x0: u128, x1: u128, y: i256::ULimb) -> bool {
        unsigned_limb_op_equal!(over x0, x1, y, overflowing_mul, overflowing_mul_ulimb)
    }

    fn u256_overflowing_mul_uwide_quickcheck(x0: u128, x1: u128, y: i256::UWide) -> bool {
        unsigned_limb_op_equal!(over x0, x1, y, overflowing_mul, overflowing_mul_uwide)
    }

    fn u256_overflowing_div_ulimb_quickcheck(x0: u128, x1: u128, y: i256::ULimb) -> bool {
        if y != 0 {
            unsigned_limb_op_equal!(over x0, x1, y, overflowing_div, overflowing_div_ulimb)
        } else {
            true
        }
    }

    fn u256_overflowing_rem_ulimb_quickcheck(x0: u128, x1: u128, y: i256::ULimb) -> bool {
        if y != 0 {
            unsigned_limb_op_equal!(x0, x1, y, overflowing_rem, overflowing_rem_ulimb, |x: (i256::u256, bool), y: (i256::ULimb, bool)| {
                x.0 == i256::u256::from(y.0) && x.1 == y.1
            })
        } else {
            true
        }
    }

    fn u256_overflowing_div_uwide_quickcheck(x0: u128, x1: u128, y: i256::UWide) -> bool {
        if y != 0 {
            unsigned_limb_op_equal!(over x0, x1, y, overflowing_div, overflowing_div_uwide)
        } else {
            true
        }
    }

    fn u256_overflowing_rem_uwide_quickcheck(x0: u128, x1: u128, y: i256::UWide) -> bool {
        if y != 0 {
            unsigned_limb_op_equal!(x0, x1, y, overflowing_rem, overflowing_rem_uwide, |x: (i256::u256, bool), y: (i256::UWide, bool)| {
                x.0 == i256::u256::from(y.0) && x.1 == y.1
            })
        } else {
            true
        }
    }

    fn u256_checked_add_ulimb_quickcheck(x0: u128, x1: u128, y: i256::ULimb) -> bool {
        unsigned_limb_op_equal!(check x0, x1, y, checked_add, checked_add_ulimb)
    }

    fn u256_checked_add_uwide_quickcheck(x0: u128, x1: u128, y: i256::UWide) -> bool {
        unsigned_limb_op_equal!(check x0, x1, y, checked_add, checked_add_uwide)
    }

    fn u256_checked_sub_ulimb_quickcheck(x0: u128, x1: u128, y: i256::ULimb) -> bool {
        unsigned_limb_op_equal!(check x0, x1, y, checked_sub, checked_sub_ulimb)
    }

    fn u256_checked_sub_uwide_quickcheck(x0: u128, x1: u128, y: i256::UWide) -> bool {
        unsigned_limb_op_equal!(check x0, x1, y, checked_sub, checked_sub_uwide)
    }

    fn u256_checked_mul_ulimb_quickcheck(x0: u128, x1: u128, y: i256::ULimb) -> bool {
        unsigned_limb_op_equal!(check x0, x1, y, checked_mul, checked_mul_ulimb)
    }

    fn u256_checked_mul_uwide_quickcheck(x0: u128, x1: u128, y: i256::UWide) -> bool {
        unsigned_limb_op_equal!(check x0, x1, y, checked_mul, checked_mul_uwide)
    }

    fn u256_checked_div_ulimb_quickcheck(x0: u128, x1: u128, y: i256::ULimb) -> bool {
        if y != 0 {
            unsigned_limb_op_equal!(check x0, x1, y, checked_div, checked_div_ulimb)
        } else {
            true
        }
    }

    fn u256_checked_rem_ulimb_quickcheck(x0: u128, x1: u128, y: i256::ULimb) -> bool {
        if y != 0 {
            unsigned_limb_op_equal!(x0, x1, y, checked_rem, checked_rem_ulimb, |x: Option<i256::u256>, y: Option<i256::ULimb>| {
                x.map(|v| v.to_le_bytes()) == y.map(|v| i256::u256::from(v).to_le_bytes())
            })
        } else {
            true
        }
    }

    fn u256_checked_div_uwide_quickcheck(x0: u128, x1: u128, y: i256::UWide) -> bool {
        if y != 0 {
            unsigned_limb_op_equal!(check x0, x1, y, checked_div, checked_div_uwide)
        } else {
            true
        }
    }

    fn u256_checked_rem_uwide_quickcheck(x0: u128, x1: u128, y: i256::UWide) -> bool {
        if y != 0 {
            unsigned_limb_op_equal!(x0, x1, y, checked_rem, checked_rem_uwide, |x: Option<i256::u256>, y: Option<i256::UWide>| {
                x.map(|v| v.to_le_bytes()) == y.map(|v| i256::u256::from(v).to_le_bytes())
            })
        } else {
            true
        }
    }

    fn u256_low_quickcheck(x0: u128, x1: u128) -> bool {
        util::to_u256(x0, x1).low().as_u128() == x0
    }

    fn u256_high_quickcheck(x0: u128, x1: u128) -> bool {
        util::to_u256(x0, x1).high().as_u128() == x1
    }

    fn u256_high_mul_quickcheck(x0: u128, x1: u128, y0: u128, y1: u128) -> bool {
        let x = util::to_u256(x0, x1);
        let y = util::to_u256(y0, y1);
        let expected = x.widening_mul(y).1;
        let actual = x.high_mul(y);
        expected == actual
    }

    fn i256_wrapping_add_quickcheck(x0: u128, x1: i128, y0: u128, y1: i128) -> bool {
        signed_op_equal!(wrap x0, x1, y0, y1, wrapping_add)
    }

    fn i256_wrapping_sub_quickcheck(x0: u128, x1: i128, y0: u128, y1: i128) -> bool {
        signed_op_equal!(wrap x0, x1, y0, y1, wrapping_sub)
    }

    fn i256_saturating_sub_quickcheck(x0: u128, x1: i128, y0: u128, y1: i128) -> bool {
        signed_op_equal!(wrap x0, x1, y0, y1, saturating_sub)
    }

    fn i256_wrapping_mul_quickcheck(x0: u128, x1: i128, y0: u128, y1: i128) -> bool {
        signed_op_equal!(wrap x0, x1, y0, y1, wrapping_mul)
    }

    fn i256_saturating_mul_quickcheck(x0: u128, x1: i128, y0: u128, y1: i128) -> bool {
        signed_op_equal!(wrap x0, x1, y0, y1, saturating_mul)
    }

    fn i256_wrapping_div_quickcheck(x0: u128, x1: i128, y0: u128, y1: i128) -> bool {
        if y0 != 0 && y1 != 0 {
            signed_op_equal!(wrap x0, x1, y0, y1, wrapping_div)
        } else {
            true
        }
    }

    fn i256_saturating_div_quickcheck(x0: u128, x1: i128, y0: u128, y1: i128) -> bool {
        if y0 != 0 && y1 != 0 {
            signed_op_equal!(wrap x0, x1, y0, y1, saturating_div)
        } else {
            true
        }
    }

    fn i256_overflowing_add_quickcheck(x0: u128, x1: i128, y0: u128, y1: i128) -> bool {
        signed_op_equal!(over x0, x1, y0, y1, overflowing_add)
    }

    fn i256_overflowing_sub_quickcheck(x0: u128, x1: i128, y0: u128, y1: i128) -> bool {
        signed_op_equal!(over x0, x1, y0, y1, overflowing_sub)
    }

    fn i256_overflowing_mul_quickcheck(x0: u128, x1: i128, y0: u128, y1: i128) -> bool {
        signed_op_equal!(over x0, x1, y0, y1, overflowing_mul)
    }

    fn i256_checked_shl_quickcheck(x0: u128, x1: i128, y: u32) -> bool {
        signed_op_equal!(check x0, x1, y, checked_shl)
    }

    fn i256_checked_shr_quickcheck(x0: u128, x1: i128, y: u32) -> bool {
        signed_op_equal!(check x0, x1, y, checked_shr)
    }

    fn i256_overflowing_div_quickcheck(x0: u128, x1: i128, y0: u128, y1: i128) -> bool {
        if y0 != 0 && y1 != 0 {
            signed_op_equal!(over x0, x1, y0, y1, overflowing_div)
        } else {
            true
        }
    }

    fn i256_checked_add_quickcheck(x0: u128, x1: i128, y0: u128, y1: i128) -> bool {
        signed_op_equal!(check x0, x1, y0, y1, checked_add)
    }

    fn i256_checked_sub_quickcheck(x0: u128, x1: i128, y0: u128, y1: i128) -> bool {
        signed_op_equal!(check x0, x1, y0, y1, checked_sub)
    }

    fn i256_checked_mul_quickcheck(x0: u128, x1: i128, y0: u128, y1: i128) -> bool {
        signed_op_equal!(check x0, x1, y0, y1, checked_mul)
    }

    fn i256_checked_div_quickcheck(x0: u128, x1: i128, y0: u128, y1: i128) -> bool {
        if y0 != 0 && y1 != 0 {
            signed_op_equal!(check x0, x1, y0, y1, checked_div)
        } else {
            true
        }
    }

    fn i256_checked_rem_quickcheck(x0: u128, x1: i128, y0: u128, y1: i128) -> bool {
        if y0 != 0 && y1 != 0 {
            signed_op_equal!(check x0, x1, y0, y1, checked_rem)
        } else {
            true
        }
    }

    fn i256_checked_div_euclid_quickcheck(x0: u128, x1: i128, y0: u128, y1: i128) -> bool {
        if y0 != 0 && y1 != 0 {
            signed_op_equal!(check x0, x1, y0, y1, checked_div_euclid)
        } else {
            true
        }
    }

    fn i256_checked_rem_euclid_quickcheck(x0: u128, x1: i128, y0: u128, y1: i128) -> bool {
        if y0 != 0 && y1 != 0 {
            signed_op_equal!(check x0, x1, y0, y1, checked_rem_euclid)
        } else {
            true
        }
    }

    fn i256_rotate_left_quickcheck(x0: u128, x1: i128, y: u32) -> bool {
        signed_op_equal!(wrap x0, x1, y, rotate_left)
    }

    fn i256_rotate_right_quickcheck(x0: u128, x1: i128, y: u32) -> bool {
        signed_op_equal!(wrap x0, x1, y, rotate_right)
    }

    fn i256_count_ones_quickcheck(x0: u128, x1: i128) -> bool {
        signed_op_equal!(scalar x0, x1, count_ones)
    }

    fn i256_count_zeros_quickcheck(x0: u128, x1: i128) -> bool {
        signed_op_equal!(scalar x0, x1, count_zeros)
    }

    fn i256_leading_zeros_quickcheck(x0: u128, x1: i128) -> bool {
        signed_op_equal!(scalar x0, x1, leading_zeros)
    }

    fn i256_leading_ones_quickcheck(x0: u128, x1: i128) -> bool {
        signed_op_equal!(scalar x0, x1, leading_ones)
    }

    fn i256_trailing_zeros_quickcheck(x0: u128, x1: i128) -> bool {
        signed_op_equal!(scalar x0, x1, trailing_zeros)
    }

    fn i256_trailing_ones_quickcheck(x0: u128, x1: i128) -> bool {
        signed_op_equal!(scalar x0, x1, trailing_ones)
    }

    fn i256_swap_bytes_quickcheck(x0: u128, x1: i128) -> bool {
        signed_op_equal!(wrap x0, x1, swap_bytes)
    }

    fn i256_reverse_bits_quickcheck(x0: u128, x1: i128) -> bool {
        signed_op_equal!(wrap x0, x1, reverse_bits)
    }

    fn i256_wrapping_neg_quickcheck(x0: u128, x1: i128) -> bool {
        signed_op_equal!(wrap x0, x1, wrapping_neg)
    }

    fn i256_cast_unsigned_quickcheck(x0: u128, x1: i128) -> bool {
        signed_op_equal!(x0, x1, cast_unsigned, |x: util::Bu256, y: i256::u256| {
            x.to_le_bytes() == y.to_le_bytes()
        })
    }

    fn i256_ilog2_quickcheck(x0: u128, x1: u128) -> bool {
        // NOTE: cannot be negative
        let x1 = x1.min(i128::MAX as u128) as i128;
        let x1 = x1.max(1);
        signed_op_equal!(scalar x0, x1, ilog2)
    }

    fn i256_checked_ilog2_quickcheck(x0: u128, x1: i128) -> bool {
        signed_op_equal!(x0, x1, checked_ilog2, |x, y| x == y)
    }

    fn i256_saturating_neg_quickcheck(x0: u128, x1: i128) -> bool {
        signed_op_equal!(wrap x0, x1, saturating_neg)
    }

    fn i256_saturating_abs_quickcheck(x0: u128, x1: i128) -> bool {
        signed_op_equal!(wrap x0, x1, saturating_abs)
    }

    fn i256_wrapping_abs_quickcheck(x0: u128, x1: i128) -> bool {
        signed_op_equal!(wrap x0, x1, wrapping_abs)
    }

    fn i256_unsigned_abs_quickcheck(x0: u128, x1: i128) -> bool {
        signed_op_equal!(x0, x1, unsigned_abs, |x: util::Bu256, y: i256::u256| {
            x.to_le_bytes() == y.to_le_bytes()
        })
    }

    fn i256_abs_quickcheck(x0: u128, x1: i128) -> bool {
        if x0 != u128::MAX && x1 != i128::MIN {
            signed_op_equal!(wrap x0, x1, abs)
        } else {
            signed_op_equal!(wrap x0, x1, wrapping_abs)
        }
    }

    fn i256_signum_quickcheck(x0: u128, x1: i128) -> bool {
        signed_op_equal!(wrap x0, x1, signum)
    }

    fn i256_is_positive_quickcheck(x0: u128, x1: i128) -> bool {
        signed_op_equal!(scalar x0, x1, is_positive)
    }

    fn i256_is_negative_quickcheck(x0: u128, x1: i128) -> bool {
        signed_op_equal!(scalar x0, x1, is_negative)
    }

    fn i256_checked_abs_quickcheck(x0: u128, x1: i128) -> bool {
        signed_op_equal!(check x0, x1, checked_abs)
    }

    fn i256_checked_pow_quickcheck(x0: u128, x1: i128, y: u32) -> bool {
        signed_op_equal!(check x0, x1, y, checked_pow)
    }

    fn i256_saturating_pow_quickcheck(x0: u128, x1: i128, y: u32) -> bool {
        signed_op_equal!(wrap x0, x1, y, saturating_pow)
    }

    fn i256_wrapping_pow_quickcheck(x0: u128, x1: i128, y: u32) -> bool {
        signed_op_equal!(wrap x0, x1, y, wrapping_pow)
    }

    fn i256_wrapping_shl_quickcheck(x0: u128, x1: i128, y: u32) -> bool {
        signed_op_equal!(wrap x0, x1, y, wrapping_shl)
    }

    fn i256_wrapping_shr_quickcheck(x0: u128, x1: i128, y: u32) -> bool {
        signed_op_equal!(wrap x0, x1, y, wrapping_shr)
    }

    fn i256_saturating_add_quickcheck(x0: u128, x1: i128, y0: u128, y1: i128) -> bool {
        signed_op_equal!(wrap x0, x1, y0, y1, saturating_add)
    }

    fn i256_div_floor_quickcheck(x0: u128, x1: i128, y0: u128, y1: i128) -> bool {
        if y0 != 0 && y1 != 0 {
            signed_op_equal!(wrap x0, x1, y0, y1, div_floor)
        } else {
            true
        }
    }

    fn i256_div_ceil_quickcheck(x0: u128, x1: i128, y0: u128, y1: i128) -> bool {
        if y0 != 0 && y1 != 0 {
            signed_op_equal!(wrap x0, x1, y0, y1, div_ceil)
        } else {
            true
        }
    }

    fn i256_abs_diff_quickcheck(x0: u128, x1: i128, y0: u128, y1: i128) -> bool {
        signed_op_equal!(x0, x1, y0, y1, abs_diff, |x: util::Bu256, y: i256::u256| {
            x.to_le_bytes() == y.to_le_bytes()
        })
    }

    // NOTE: We check all the div/rem ones below because they have to match **FLOOR**
    // division and not the Rust standard behavior.

    fn i256_wrapping_add_ulimb_quickcheck(x0: u128, x1: i128, y: i256::ULimb) -> bool {
        signed_limb_op_equal!(wrap x0, x1, y, wrapping_add, wrapping_add_ulimb)
    }

    fn i256_wrapping_add_uwide_quickcheck(x0: u128, x1: i128, y: i256::UWide) -> bool {
        signed_limb_op_equal!(wrap x0, x1, y, wrapping_add, wrapping_add_uwide)
    }

    fn i256_wrapping_sub_ulimb_quickcheck(x0: u128, x1: i128, y: i256::ULimb) -> bool {
        signed_limb_op_equal!(wrap x0, x1, y, wrapping_sub, wrapping_sub_ulimb)
    }

    fn i256_wrapping_sub_uwide_quickcheck(x0: u128, x1: i128, y: i256::UWide) -> bool {
        signed_limb_op_equal!(wrap x0, x1, y, wrapping_sub, wrapping_sub_uwide)
    }

    fn i256_wrapping_mul_ulimb_quickcheck(x0: u128, x1: i128, y: i256::ULimb) -> bool {
        signed_limb_op_equal!(wrap x0, x1, y, wrapping_mul, wrapping_mul_ulimb)
    }

    fn i256_wrapping_mul_uwide_quickcheck(x0: u128, x1: i128, y: i256::UWide) -> bool {
        signed_limb_op_equal!(wrap x0, x1, y, wrapping_mul, wrapping_mul_uwide)
    }

    fn i256_overflowing_add_ulimb_quickcheck(x0: u128, x1: i128, y: i256::ULimb) -> bool {
        signed_limb_op_equal!(over x0, x1, y, overflowing_add, overflowing_add_ulimb)
    }

    fn i256_overflowing_add_uwide_quickcheck(x0: u128, x1: i128, y: i256::UWide) -> bool {
        signed_limb_op_equal!(over x0, x1, y, overflowing_add, overflowing_add_uwide)
    }

    fn i256_overflowing_sub_ulimb_quickcheck(x0: u128, x1: i128, y: i256::ULimb) -> bool {
        signed_limb_op_equal!(over x0, x1, y, overflowing_sub, overflowing_sub_ulimb)
    }

    fn i256_overflowing_sub_uwide_quickcheck(x0: u128, x1: i128, y: i256::UWide) -> bool {
        signed_limb_op_equal!(over x0, x1, y, overflowing_sub, overflowing_sub_uwide)
    }

    fn i256_overflowing_mul_ulimb_quickcheck(x0: u128, x1: i128, y: i256::ULimb) -> bool {
        signed_limb_op_equal!(over x0, x1, y, overflowing_mul, overflowing_mul_ulimb)
    }

    fn i256_overflowing_mul_uwide_quickcheck(x0: u128, x1: i128, y: i256::UWide) -> bool {
        signed_limb_op_equal!(over x0, x1, y, overflowing_mul, overflowing_mul_uwide)
    }

    fn i256_checked_add_ulimb_quickcheck(x0: u128, x1: i128, y: i256::ULimb) -> bool {
        signed_limb_op_equal!(check x0, x1, y, checked_add, checked_add_ulimb)
    }

    fn i256_checked_add_uwide_quickcheck(x0: u128, x1: i128, y: i256::UWide) -> bool {
        signed_limb_op_equal!(check x0, x1, y, checked_add, checked_add_uwide)
    }

    fn i256_checked_sub_ulimb_quickcheck(x0: u128, x1: i128, y: i256::ULimb) -> bool {
        signed_limb_op_equal!(check x0, x1, y, checked_sub, checked_sub_ulimb)
    }

    fn i256_checked_sub_uwide_quickcheck(x0: u128, x1: i128, y: i256::UWide) -> bool {
        signed_limb_op_equal!(check x0, x1, y, checked_sub, checked_sub_uwide)
    }

    fn i256_checked_mul_ulimb_quickcheck(x0: u128, x1: i128, y: i256::ULimb) -> bool {
        signed_limb_op_equal!(check x0, x1, y, checked_mul, checked_mul_ulimb)
    }

    fn i256_checked_mul_uwide_quickcheck(x0: u128, x1: i128, y: i256::UWide) -> bool {
        signed_limb_op_equal!(check x0, x1, y, checked_mul, checked_mul_uwide)
    }

    fn i256_wrapping_add_ilimb_quickcheck(x0: u128, x1: i128, y: i256::ILimb) -> bool {
        signed_limb_op_equal!(wrap x0, x1, y, wrapping_add, wrapping_add_ilimb)
    }

    fn i256_wrapping_add_iwide_quickcheck(x0: u128, x1: i128, y: i256::IWide) -> bool {
        signed_limb_op_equal!(wrap x0, x1, y, wrapping_add, wrapping_add_iwide)
    }

    fn i256_wrapping_sub_ilimb_quickcheck(x0: u128, x1: i128, y: i256::ILimb) -> bool {
        signed_limb_op_equal!(wrap x0, x1, y, wrapping_sub, wrapping_sub_ilimb)
    }

    fn i256_wrapping_sub_iwide_quickcheck(x0: u128, x1: i128, y: i256::IWide) -> bool {
        signed_limb_op_equal!(wrap x0, x1, y, wrapping_sub, wrapping_sub_iwide)
    }

    fn i256_wrapping_mul_iwide_quickcheck(x0: u128, x1: i128, y: i256::IWide) -> bool {
        signed_limb_op_equal!(wrap x0, x1, y, wrapping_mul, wrapping_mul_iwide)
    }

    fn i256_wrapping_mul_ilimb_quickcheck(x0: u128, x1: i128, y: i256::ILimb) -> bool {
        signed_limb_op_equal!(wrap x0, x1, y, wrapping_mul, wrapping_mul_ilimb)
    }

    fn i256_wrapping_div_ilimb_quickcheck(x0: u128, x1: i128, y: i256::ILimb) -> bool {
        if y == 0 || (y != -1 && x0 == 0 && x1 == i128::MIN) {
            true
        } else {
            signed_limb_op_equal!(wrap x0, x1, y, wrapping_div, wrapping_div_ilimb)
        }
    }

    fn i256_wrapping_rem_ilimb_quickcheck(x0: u128, x1: i128, y: i256::ILimb) -> bool {
        if y == 0 || (y != -1 && x0 == 0 && x1 == i128::MIN) {
            true
        } else {
            signed_limb_op_equal!(x0, x1, y, wrapping_rem, wrapping_rem_ilimb, |x, y| {
                x == i256::i256::from(y)
            })
        }
    }

    fn i256_wrapping_div_iwide_quickcheck(x0: u128, x1: i128, y: i256::IWide) -> bool {
        if y == 0 || (y != -1 && x0 == 0 && x1 == i128::MIN) {
            true
        } else {
            signed_limb_op_equal!(wrap x0, x1, y, wrapping_div, wrapping_div_iwide)
        }
    }

    fn i256_wrapping_rem_iwide_quickcheck(x0: u128, x1: i128, y: i256::IWide) -> bool {
        if y == 0 || (y != -1 && x0 == 0 && x1 == i128::MIN) {
            true
        } else {
            signed_limb_op_equal!(x0, x1, y, wrapping_rem, wrapping_rem_iwide, |x, y| {
                x == i256::i256::from_iwide(y)
            })
        }
    }

    fn i256_overflowing_add_ilimb_quickcheck(x0: u128, x1: i128, y: i256::ILimb) -> bool {
        signed_limb_op_equal!(over x0, x1, y, overflowing_add, overflowing_add_ilimb)
    }

    fn i256_overflowing_add_iwide_quickcheck(x0: u128, x1: i128, y: i256::IWide) -> bool {
        signed_limb_op_equal!(over x0, x1, y, overflowing_add, overflowing_add_iwide)
    }

    fn i256_overflowing_sub_ilimb_quickcheck(x0: u128, x1: i128, y: i256::ILimb) -> bool {
        signed_limb_op_equal!(over x0, x1, y, overflowing_sub, overflowing_sub_ilimb)
    }

    fn i256_overflowing_sub_iwide_quickcheck(x0: u128, x1: i128, y: i256::IWide) -> bool {
        signed_limb_op_equal!(over x0, x1, y, overflowing_sub, overflowing_sub_iwide)
    }

    fn i256_overflowing_mul_ilimb_quickcheck(x0: u128, x1: i128, y: i256::ILimb) -> bool {
        signed_limb_op_equal!(over x0, x1, y, overflowing_mul, overflowing_mul_ilimb)
    }

    fn i256_overflowing_mul_iwide_quickcheck(x0: u128, x1: i128, y: i256::IWide) -> bool {
        signed_limb_op_equal!(over x0, x1, y, overflowing_mul, overflowing_mul_iwide)
    }

    fn i256_overflowing_div_ilimb_quickcheck(x0: u128, x1: i128, y: i256::ILimb) -> bool {
        if y == 0 || (y != -1 && x0 == 0 && x1 == i128::MIN) {
            true
        } else {
            signed_limb_op_equal!(over x0, x1, y, overflowing_div, overflowing_div_ilimb)
        }
    }

    fn i256_overflowing_rem_ilimb_quickcheck(x0: u128, x1: i128, y: i256::ILimb) -> bool {
        if y == 0 || (y != -1 && x0 == 0 && x1 == i128::MIN) {
            true
        } else {
            signed_limb_op_equal!(x0, x1, y, overflowing_rem, overflowing_rem_ilimb, |x: (i256::i256, bool), y: (i256::ILimb, bool)| {
                x.0 == i256::i256::from(y.0) && x.1 == y.1
            })
        }
    }

    fn i256_overflowing_div_iwide_quickcheck(x0: u128, x1: i128, y: i256::IWide) -> bool {
        if y == 0 || (y != -1 && x0 == 0 && x1 == i128::MIN) {
            true
        } else {
            signed_limb_op_equal!(over x0, x1, y, overflowing_div, overflowing_div_iwide)
        }
    }

    fn i256_overflowing_rem_iwide_quickcheck(x0: u128, x1: i128, y: i256::IWide) -> bool {
        if y == 0 || (y != -1 && x0 == 0 && x1 == i128::MIN) {
            true
        } else {
            signed_limb_op_equal!(x0, x1, y, overflowing_rem, overflowing_rem_iwide, |x: (i256::i256, bool), y: (i256::IWide, bool)| {
                x.0 == i256::i256::from(y.0) && x.1 == y.1
            })
        }
    }

    fn i256_checked_add_ilimb_quickcheck(x0: u128, x1: i128, y: i256::ILimb) -> bool {
        signed_limb_op_equal!(check x0, x1, y, checked_add, checked_add_ilimb)
    }

    fn i256_checked_add_iwide_quickcheck(x0: u128, x1: i128, y: i256::IWide) -> bool {
        signed_limb_op_equal!(check x0, x1, y, checked_add, checked_add_iwide)
    }

    fn i256_checked_sub_ilimb_quickcheck(x0: u128, x1: i128, y: i256::ILimb) -> bool {
        signed_limb_op_equal!(check x0, x1, y, checked_sub, checked_sub_ilimb)
    }

    fn i256_checked_sub_iwide_quickcheck(x0: u128, x1: i128, y: i256::IWide) -> bool {
        signed_limb_op_equal!(check x0, x1, y, checked_sub, checked_sub_iwide)
    }

    fn i256_checked_mul_ilimb_quickcheck(x0: u128, x1: i128, y: i256::ILimb) -> bool {
        signed_limb_op_equal!(check x0, x1, y, checked_mul, checked_mul_ilimb)
    }

    fn i256_checked_mul_iwide_quickcheck(x0: u128, x1: i128, y: i256::IWide) -> bool {
        signed_limb_op_equal!(check x0, x1, y, checked_mul, checked_mul_iwide)
    }

    fn i256_checked_div_ilimb_quickcheck(x0: u128, x1: i128, y: i256::ILimb) -> bool {
        if y == 0 || (y != -1 && x0 == 0 && x1 == i128::MIN) {
            true
        } else {
            signed_limb_op_equal!(check x0, x1, y, checked_div, checked_div_ilimb)
        }
    }

    fn i256_checked_rem_ilimb_quickcheck(x0: u128, x1: i128, y: i256::ILimb) -> bool {
        if y == 0 || (y != -1 && x0 == 0 && x1 == i128::MIN) {
            true
        } else {
            signed_limb_op_equal!(x0, x1, y, checked_rem, checked_rem_ilimb, |x: Option<i256::i256>, y: Option<i256::ILimb>| {
                x.map(|v| v.to_le_bytes()) == y.map(|v| i256::i256::from(v).to_le_bytes())
            })
        }
    }

    fn i256_checked_div_iwide_quickcheck(x0: u128, x1: i128, y: i256::IWide) -> bool {
        if y == 0 || (y != -1 && x0 == 0 && x1 == i128::MIN) {
            true
        } else {
            signed_limb_op_equal!(check x0, x1, y, checked_div, checked_div_iwide)
        }
    }

    fn i256_checked_rem_iwide_quickcheck(x0: u128, x1: i128, y: i256::IWide) -> bool {
        if y == 0 || (y != -1 && x0 == 0 && x1 == i128::MIN) {
            true
        } else {
            signed_limb_op_equal!(x0, x1, y, checked_rem, checked_rem_iwide, |x: Option<i256::i256>, y: Option<i256::IWide>| {
                x.map(|v| v.to_le_bytes()) == y.map(|v| i256::i256::from(v).to_le_bytes())
            })
        }
    }

    // 32-bit scalars

    fn u256_wrapping_add_u32_quickcheck(x0: u128, x1: u128, y: u32) -> bool {
        unsigned_limb_op_equal!(wrap x0, x1, y, wrapping_add, wrapping_add_u32)
    }

    fn u256_wrapping_sub_u32_quickcheck(x0: u128, x1: u128, y: u32) -> bool {
        unsigned_limb_op_equal!(wrap x0, x1, y, wrapping_sub, wrapping_sub_u32)
    }

    fn u256_wrapping_mul_u32_quickcheck(x0: u128, x1: u128, y: u32) -> bool {
        unsigned_limb_op_equal!(wrap x0, x1, y, wrapping_mul, wrapping_mul_u32)
    }

    fn u256_wrapping_div_u32_quickcheck(x0: u128, x1: u128, y: u32) -> bool {
        if y != 0 {
            unsigned_limb_op_equal!(wrap x0, x1, y, wrapping_div, wrapping_div_u32)
        } else {
            true
        }
    }

    fn u256_wrapping_rem_u32_quickcheck(x0: u128, x1: u128, y: u32) -> bool {
        if y != 0 {
            unsigned_limb_op_equal!(x0, x1, y, wrapping_rem, wrapping_rem_u32, |x, y| {
                x == i256::u256::from(y)
            })
        } else {
            true
        }
    }

    fn u256_overflowing_add_u32_quickcheck(x0: u128, x1: u128, y: u32) -> bool {
        unsigned_limb_op_equal!(over x0, x1, y, overflowing_add, overflowing_add_u32)
    }

    fn u256_overflowing_sub_u32_quickcheck(x0: u128, x1: u128, y: u32) -> bool {
        unsigned_limb_op_equal!(over x0, x1, y, overflowing_sub, overflowing_sub_u32)
    }

    fn u256_overflowing_mul_u32_quickcheck(x0: u128, x1: u128, y: u32) -> bool {
        unsigned_limb_op_equal!(over x0, x1, y, overflowing_mul, overflowing_mul_u32)
    }

    fn u256_overflowing_div_u32_quickcheck(x0: u128, x1: u128, y: u32) -> bool {
        if y != 0 {
            unsigned_limb_op_equal!(over x0, x1, y, overflowing_div, overflowing_div_u32)
        } else {
            true
        }
    }

    fn u256_overflowing_rem_u32_quickcheck(x0: u128, x1: u128, y: u32) -> bool {
        if y != 0 {
            unsigned_limb_op_equal!(x0, x1, y, overflowing_rem, overflowing_rem_u32, |x: (i256::u256, bool), y: (u32, bool)| {
                x.0 == i256::u256::from(y.0) && x.1 == y.1
            })
        } else {
            true
        }
    }

    fn u256_checked_add_u32_quickcheck(x0: u128, x1: u128, y: u32) -> bool {
        unsigned_limb_op_equal!(check x0, x1, y, checked_add, checked_add_u32)
    }

    fn u256_checked_sub_u32_quickcheck(x0: u128, x1: u128, y: u32) -> bool {
        unsigned_limb_op_equal!(check x0, x1, y, checked_sub, checked_sub_u32)
    }

    fn u256_checked_mul_u32_quickcheck(x0: u128, x1: u128, y: u32) -> bool {
        unsigned_limb_op_equal!(check x0, x1, y, checked_mul, checked_mul_u32)
    }

    fn u256_checked_div_u32_quickcheck(x0: u128, x1: u128, y: u32) -> bool {
        if y != 0 {
            unsigned_limb_op_equal!(check x0, x1, y, checked_div, checked_div_u32)
        } else {
            true
        }
    }

    fn u256_checked_rem_u32_quickcheck(x0: u128, x1: u128, y: u32) -> bool {
        if y != 0 {
            unsigned_limb_op_equal!(x0, x1, y, checked_rem, checked_rem_u32, |x: Option<i256::u256>, y: Option<u32>| {
                x.map(|v| v.to_le_bytes()) == y.map(|v| i256::u256::from(v).to_le_bytes())
            })
        } else {
            true
        }
    }

    fn i256_wrapping_add_u32_quickcheck(x0: u128, x1: i128, y: u32) -> bool {
        signed_limb_op_equal!(wrap x0, x1, y, wrapping_add, wrapping_add_u32)
    }

    fn i256_wrapping_sub_u32_quickcheck(x0: u128, x1: i128, y: u32) -> bool {
        signed_limb_op_equal!(wrap x0, x1, y, wrapping_sub, wrapping_sub_u32)
    }

    fn i256_wrapping_mul_u32_quickcheck(x0: u128, x1: i128, y: u32) -> bool {
        signed_limb_op_equal!(wrap x0, x1, y, wrapping_mul, wrapping_mul_u32)
    }

    fn i256_overflowing_add_u32_quickcheck(x0: u128, x1: i128, y: u32) -> bool {
        signed_limb_op_equal!(over x0, x1, y, overflowing_add, overflowing_add_u32)
    }

    fn i256_overflowing_sub_u32_quickcheck(x0: u128, x1: i128, y: u32) -> bool {
        signed_limb_op_equal!(over x0, x1, y, overflowing_sub, overflowing_sub_u32)
    }

    fn i256_overflowing_mul_u32_quickcheck(x0: u128, x1: i128, y: u32) -> bool {
        signed_limb_op_equal!(over x0, x1, y, overflowing_mul, overflowing_mul_u32)
    }

    fn i256_checked_add_u32_quickcheck(x0: u128, x1: i128, y: u32) -> bool {
        signed_limb_op_equal!(check x0, x1, y, checked_add, checked_add_u32)
    }

    fn i256_checked_sub_u32_quickcheck(x0: u128, x1: i128, y: u32) -> bool {
        signed_limb_op_equal!(check x0, x1, y, checked_sub, checked_sub_u32)
    }

    fn i256_checked_mul_u32_quickcheck(x0: u128, x1: i128, y: u32) -> bool {
        signed_limb_op_equal!(check x0, x1, y, checked_mul, checked_mul_u32)
    }

    fn i256_wrapping_add_i32_quickcheck(x0: u128, x1: i128, y: i32) -> bool {
        signed_limb_op_equal!(wrap x0, x1, y, wrapping_add, wrapping_add_i32)
    }

    fn i256_wrapping_sub_i32_quickcheck(x0: u128, x1: i128, y: i32) -> bool {
        signed_limb_op_equal!(wrap x0, x1, y, wrapping_sub, wrapping_sub_i32)
    }

    fn i256_wrapping_mul_i32_quickcheck(x0: u128, x1: i128, y: i32) -> bool {
        signed_limb_op_equal!(wrap x0, x1, y, wrapping_mul, wrapping_mul_i32)
    }

    fn i256_wrapping_div_i32_quickcheck(x0: u128, x1: i128, y: i32) -> bool {
        if y == 0 || (y != -1 && x0 == 0 && x1 == i128::MIN) {
            true
        } else {
            signed_limb_op_equal!(wrap x0, x1, y, wrapping_div, wrapping_div_i32)
        }
    }

    fn i256_wrapping_rem_i32_quickcheck(x0: u128, x1: i128, y: i32) -> bool {
        if y == 0 || (y != -1 && x0 == 0 && x1 == i128::MIN) {
            true
        } else {
            signed_limb_op_equal!(x0, x1, y, wrapping_rem, wrapping_rem_i32, |x, y| {
                x == i256::i256::from_i32(y)
            })
        }
    }

    fn i256_overflowing_add_i32_quickcheck(x0: u128, x1: i128, y: i32) -> bool {
        signed_limb_op_equal!(over x0, x1, y, overflowing_add, overflowing_add_i32)
    }

    fn i256_overflowing_sub_i32_quickcheck(x0: u128, x1: i128, y: i32) -> bool {
        signed_limb_op_equal!(over x0, x1, y, overflowing_sub, overflowing_sub_i32)
    }

    fn i256_overflowing_mul_i32_quickcheck(x0: u128, x1: i128, y: i32) -> bool {
        signed_limb_op_equal!(over x0, x1, y, overflowing_mul, overflowing_mul_i32)
    }

    fn i256_overflowing_div_i32_quickcheck(x0: u128, x1: i128, y: i32) -> bool {
        if y == 0 || (y != -1 && x0 == 0 && x1 == i128::MIN) {
            true
        } else {
            signed_limb_op_equal!(over x0, x1, y, overflowing_div, overflowing_div_i32)
        }
    }

    fn i256_overflowing_rem_i32_quickcheck(x0: u128, x1: i128, y: i32) -> bool {
        if y == 0 || (y != -1 && x0 == 0 && x1 == i128::MIN) {
            true
        } else {
            signed_limb_op_equal!(x0, x1, y, overflowing_rem, overflowing_rem_i32, |x: (i256::i256, bool), y: (i32, bool)| {
                x.0 == i256::i256::from(y.0) && x.1 == y.1
            })
        }
    }

    fn i256_checked_add_i32_quickcheck(x0: u128, x1: i128, y: i32) -> bool {
        signed_limb_op_equal!(check x0, x1, y, checked_add, checked_add_i32)
    }

    fn i256_checked_sub_i32_quickcheck(x0: u128, x1: i128, y: i32) -> bool {
        signed_limb_op_equal!(check x0, x1, y, checked_sub, checked_sub_i32)
    }

    fn i256_checked_mul_i32_quickcheck(x0: u128, x1: i128, y: i32) -> bool {
        signed_limb_op_equal!(check x0, x1, y, checked_mul, checked_mul_i32)
    }

    fn i256_checked_div_i32_quickcheck(x0: u128, x1: i128, y: i32) -> bool {
        if y == 0 || (y != -1 && x0 == 0 && x1 == i128::MIN) {
            true
        } else {
            signed_limb_op_equal!(check x0, x1, y, checked_div, checked_div_i32)
        }
    }

    fn i256_checked_rem_i32_quickcheck(x0: u128, x1: i128, y: i32) -> bool {
        if y == 0 || (y != -1 && x0 == 0 && x1 == i128::MIN) {
            true
        } else {
            signed_limb_op_equal!(x0, x1, y, checked_rem, checked_rem_i32, |x: Option<i256::i256>, y: Option<i32>| {
                x.map(|v| v.to_le_bytes()) == y.map(|v| i256::i256::from(v).to_le_bytes())
            })
        }
    }
}

#[test]
fn overflowing_sub_tests() {
    let x0 = 0u128;
    let x1 = 0i128;
    let y0 = 0u128;
    let y1 = -0x80000000000000000000000000000000i128;

    assert!(signed_op_equal!(wrap x0, x1, y0, y1, wrapping_sub));
    assert!(signed_op_equal!(over x0, x1, y0, y1, overflowing_sub));
    assert!(signed_op_equal!(check x0, x1, y0, y1, checked_sub));

    let x = i256::i256::from_le_u64([0, 0, 0, 0]);
    let y = i256::i256::from_le_u64([1, 0, 0, i64::MIN as u64]);

    // NOTE: This is a specific edge-case where it wraps but then wraps
    // back to the correct value: the end value is what it should be.
    let (z, o) = x.overflowing_sub(y);
    assert!(!o, "should not have overflowed");
    assert_eq!(z.get_wide(1), i128::MAX as u128);
    assert_eq!(z.get_wide(0), u128::MAX);

    assert!(x.checked_sub(y).is_some());
}

#[test]
fn wrapping_neg_tests() {
    let x = i256::i256::from_le_u64([0, 0, 0, 0]);
    let neg = x.wrapping_neg();
    assert_eq!(neg.get_wide(0), 0);
    assert_eq!(neg.get_wide(1), 0);
}

#[test]
fn saturating_neg_tests() {
    let x = i256::i256::from_le_u64([0, 0, 0, 0]);
    let neg = x.saturating_neg();
    assert_eq!(neg.get_wide(0), 0);
    assert_eq!(neg.get_wide(1), 0);

    // 0, -1
    let x = i256::i256::from_le_u64([0, 0, u64::MAX, u64::MAX]);
    let neg = x.saturating_neg();
    assert_eq!(neg.get_wide(0), 0);
    assert_eq!(neg.get_wide(1), 1);

    let neg = x.checked_neg();
    assert!(neg.is_some());
    let neg = neg.unwrap();
    assert_eq!(neg.get_wide(0), 0);
    assert_eq!(neg.get_wide(1), 1);
}

#[test]
fn saturating_abs_tests() {
    let x = i256::i256::from_le_u64([0, 0, 0, 0]);
    let abs = x.saturating_abs();
    assert_eq!(abs.get_wide(0), 0);
    assert_eq!(abs.get_wide(1), 0);

    let x = i256::i256::from_le_u64([0, 0, u64::MAX, u64::MAX]);
    let abs = x.saturating_abs();
    assert_eq!(abs.get_wide(0), 0);
    assert_eq!(abs.get_wide(1), 1);

    let x = util::to_i256(u128::MAX, u128::MAX as i128);
    let abs = x.saturating_abs();
    assert_eq!(abs.get_wide(0), 1);
    assert_eq!(abs.get_wide(1), 0);
}

#[test]
fn abs_tests() {
    let x = i256::i256::from_le_u64([0, 0, 0, 0]);
    let abs = x.abs();
    assert_eq!(abs.get_wide(0), 0);
    assert_eq!(abs.get_wide(1), 0);

    let x = util::to_i256(0, i128::MIN);
    assert!(x.checked_abs().is_none());

    let x = util::to_i256(u128::MAX, u128::MAX as i128);
    assert!(x.checked_abs().is_some());
    let abs = x.checked_abs().unwrap();
    assert_eq!(abs.get_wide(0), 1);
    assert_eq!(abs.get_wide(1), 0);
}

#[test]
fn midpoint_tests() {
    let x = util::to_i256(3, 0);
    let y = i256::i256::from_le_u64([0, 0, u64::MAX, u64::MAX]);
    let midpoint = x.midpoint(y);
    // NOTE: Rust recently changed this behavior from `-Inf` to `0` for rounding.
    // bnum still uses the old behavior.
    // https://github.com/rust-lang-ci/rust/commit/9fa0146
    assert_eq!(midpoint.to_string(), "-170141183460469231731687303715884105726");
}

#[test]
fn next_power_of_two_tests() {
    let x = i256::u256::from_le_u64([0, 0, 0, 0]).wrapping_next_power_of_two();
    assert_eq!(x, util::to_u256(1, 0));

    let x = util::to_u256(1, 0).wrapping_next_power_of_two();
    assert_eq!(x, util::to_u256(1, 0));

    let x = util::to_u256(2, 0).wrapping_next_power_of_two();
    assert_eq!(x, util::to_u256(2, 0));

    let x = util::to_u256(3, 0).wrapping_next_power_of_two();
    assert_eq!(x, util::to_u256(4, 0));
}

#[test]
fn wrapping_add_ilimb_tests() {
    let x = i256::i256::from_le_u64([0, 0, 0, 0]).wrapping_add_ilimb(-1);
    assert_eq!(x, util::to_i256(u128::MAX, u128::MAX as i128));
}

#[test]
#[cfg(not(feature = "limb32"))]
fn wrapping_mul_ulimb_tests() {
    let x = util::to_i256(2, 0).wrapping_mul_ulimb(9223372036854775808);
    assert_eq!(x, util::to_i256(18446744073709551616, 0));
}

#[test]
fn wrapping_mul_ilimb_tests() {
    let x = util::to_i256(0, 1).wrapping_mul_ilimb(-1);
    assert_eq!(x, i256::i256::from_le_u64([0, 0, u64::MAX, u64::MAX]));
}

#[test]
fn checked_rem_tests() {
    let num = i256::i256::from_le_u64([0, 0, u64::MAX, u64::MAX]);
    let den = util::to_i256(1, 1);
    let (quo, rem) = num.wrapping_div_rem(den);
    assert_eq!(rem, i256::i256::from_le_u64([0, 0, u64::MAX, u64::MAX]));
    assert_eq!(quo, i256::i256::from_i8(0));
}

#[test]
#[cfg(not(feature = "limb32"))]
fn checked_rem_ulimb_tests() {
    // NOTE: With `ulimb` we have to have Python-like handling of the values,
    // rather than how Rust handles remainders.
    let num = i256::i256::from_le_u64([0, 0, u64::MAX, u64::MAX]);
    let den = u64::MAX;
    let (quo, rem) = num.wrapping_div_rem_ulimb(den);
    assert_eq!(rem, 18446744073709551614);
    assert_eq!(quo, i256::i256::from_i128(-18446744073709551618));
}

#[test]
fn widening_mul_tests() {
    let x = i256::u256::from_le_u64([0, 0, 1, 0]);
    let y = i256::u256::from_le_u64([1, 0, 0, 0]);
    let (lo, hi) = x.widening_mul(y);
    assert_eq!(lo, x.wrapping_mul(y));
    assert_eq!(lo.to_le_u64(), [0, 0, 1, 0]);
    assert_eq!(hi.to_le_u64(), [0, 0, 0, 0]);
    assert_eq!(hi, x.high_mul(y));
}
