use i256::math::*;
use quickcheck::quickcheck;

const fn split(x: u64) -> (u32, u32) {
    (x as u32, (x >> 32) as u32)
}

const fn unsplit(x0: u32, x1: u32) -> u64 {
    x0 as u64 + ((x1 as u64) << 32)
}

quickcheck! {
    fn wrapping_add_u32_quickcheck(x: u64, y: u64) -> bool {
        let (x0, x1) = split(x);
        let (y0, y1) = split(y);
        let result = add::wrapping_u32(&[x0, x1], &[y0, y1]);
        let expected = x.wrapping_add(y);
        let actual = unsplit(result[0], result[1]);
        expected == actual
    }

    fn overflowing_add_u32_quickcheck(x: u64, y: u64) -> bool {
        let (x0, x1) = split(x);
        let (y0, y1) = split(y);
        let (result, overflowed) = add::overflowing_u32(&[x0, x1], &[y0, y1]);
        let expected = x.overflowing_add(y);
        let actual = unsplit(result[0], result[1]);
        expected == (actual, overflowed)
    }

    fn wrapping_add_wide_u32_quickcheck(x: u64, y: u32) -> bool {
        let (x0, x1) = split(x);
        let result = add::wrapping_limb_u32(&[x0, x1], y);
        let expected = x.wrapping_add(y as u64);
        let actual = unsplit(result[0], result[1]);
        expected == actual
    }

    fn overflowing_add_wide_u32_quickcheck(x: u64, y: u32) -> bool {
        let (x0, x1) = split(x);
        let (result, overflowed) = add::overflowing_limb_u32(&[x0, x1], y);
        let expected = x.overflowing_add(y as u64);
        let actual = unsplit(result[0], result[1]);
        expected == (actual, overflowed)
    }

    fn overflowing_sub_u32_quickcheck(x: u64, y: u64) -> bool {
        let (x0, x1) = split(x);
        let (y0, y1) = split(y);
        let (result, overflowed) = sub::overflowing_u32(&[x0, x1], &[y0, y1]);
        let expected = x.overflowing_sub(y);
        let actual = unsplit(result[0], result[1]);
        expected == (actual, overflowed)
    }

    fn wrapping_sub_limb_u32_quickcheck(x: u64, y: u32) -> bool {
        let (x0, x1) = split(x);
        let result = sub::wrapping_limb_u32(&[x0, x1], y);
        let expected = x.wrapping_sub(y as u64);
        let actual = unsplit(result[0], result[1]);
        expected == actual
    }

    fn overflowing_sub_limb_u32_quickcheck(x: u64, y: u32) -> bool {
        let (x0, x1) = split(x);
        let (result, overflowed) = sub::overflowing_limb_u32(&[x0, x1], y);
        let expected = x.overflowing_sub(y as u64);
        let actual = unsplit(result[0], result[1]);
        expected == (actual, overflowed)
    }

    fn wrapping_mul_u32_quickcheck(x: u64, y: u64) -> bool {
        let (x0, x1) = split(x);
        let (y0, y1) = split(y);
        let result = mul::wrapping_u32(&[x0, x1], &[y0, y1]);
        let expected = x.wrapping_mul(y);
        let actual = unsplit(result[0], result[1]);
        expected == actual
    }

    fn overflowing_mul_u32_quickcheck(x: u64, y: u64) -> bool {
        let (x0, x1) = split(x);
        let (y0, y1) = split(y);
        let (result, overflowed) = mul::overflowing_u32(&[x0, x1], &[y0, y1]);
        let expected = x.overflowing_mul(y);
        let actual = unsplit(result[0], result[1]);
        expected == (actual, overflowed)
    }

    fn shl_u32_quickcheck(x: u64, n: u32) -> bool {
        let (x0, x1) = split(x);
        let n = (n % 64) as u32;
        let expected = x << n;
        let result = shift::left_u32([x0, x1], n);
        let actual = unsplit(result[0], result[1]);
        expected == actual
    }

    fn shr_u32_quickcheck(x: u64, n: u32) -> bool {
        let (x0, x1) = split(x);
        let n = (n % 64) as u32;
        let expected = x >> n;
        let result = shift::right_u32([x0, x1], n);
        let actual = unsplit(result[0], result[1]);
        expected == actual
    }

    fn rotate_left_u32_quickcheck(x: u64, n: u32) -> bool {
        let (x0, x1) = split(x);
        let expected = x.rotate_left(n);
        let result = rotate::left_u32([x0, x1], n);
        let actual = unsplit(result[0], result[1]);
        expected == actual
    }

    fn rotate_right_u32_quickcheck(x: u64, n: u32) -> bool {
        let (x0, x1) = split(x);
        let expected = x.rotate_right(n);
        let result = rotate::right_u32([x0, x1], n);
        let actual = unsplit(result[0], result[1]);
        expected == actual
    }

    fn wrapping_add_i32_quickcheck(x: i64, y: i64) -> bool {
        let (x0, x1) = split(x as u64);
        let (y0, y1) = split(y as u64);
        let result = add::wrapping_i32(&[x0, x1], &[y0, y1]);
        let expected = x.wrapping_add(y);
        let actual = unsplit(result[0], result[1]);
        expected == actual as i64
    }

    fn overflowing_add_i32_quickcheck(x: i64, y: i64) -> bool {
        let (x0, x1) = split(x as u64);
        let (y0, y1) = split(y as u64);
        let (result, overflowed) = add::overflowing_i32(&[x0, x1], &[y0, y1]);
        let expected = x.overflowing_add(y);
        let actual = unsplit(result[0], result[1]);
        expected == (actual as i64, overflowed)
    }

    fn wrapping_add_ulimb_i32_quickcheck(x: i64, y: u32) -> bool {
        let (x0, x1) = split(x as u64);
        let result = add::wrapping_ulimb_i32(&[x0, x1], y);
        let expected = x.wrapping_add(y as i64);
        let actual = unsplit(result[0], result[1]);
        expected == actual as i64
    }

    fn overflowing_add_ulimb_i32_quickcheck(x: i64, y: u32) -> bool {
        let (x0, x1) = split(x as u64);
        let (result, overflowed) = add::overflowing_ulimb_i32(&[x0, x1], y);
        let expected = x.overflowing_add(y as i64);
        let actual = unsplit(result[0], result[1]);
        expected == (actual as i64, overflowed)
    }

    fn wrapping_add_ilimb_i32_quickcheck(x: i64, y: i32) -> bool {
        let (x0, x1) = split(x as u64);
        let result = add::wrapping_ilimb_i32(&[x0, x1], y);
        let expected = x.wrapping_add(y as i64);
        let actual = unsplit(result[0], result[1]);
        expected == actual as i64
    }

    fn overflowing_add_ilimb_i32_quickcheck(x: i64, y: i32) -> bool {
        let (x0, x1) = split(x as u64);
        let (result, overflowed) = add::overflowing_ilimb_i32(&[x0, x1], y);
        let expected = x.overflowing_add(y as i64);
        let actual = unsplit(result[0], result[1]);
        expected == (actual as i64, overflowed)
    }

    fn wrapping_sub_i32_quickcheck(x: i64, y: i64) -> bool {
        let (x0, x1) = split(x as u64);
        let (y0, y1) = split(y as u64);
        let result = sub::wrapping_i32(&[x0, x1], &[y0, y1]);
        let expected = x.wrapping_sub(y);
        let actual = unsplit(result[0], result[1]);
        expected == actual as i64
    }

    fn overflowing_sub_i32_quickcheck(x: i64, y: i64) -> bool {
        let (x0, x1) = split(x as u64);
        let (y0, y1) = split(y as u64);
        let (result, overflowed) = sub::overflowing_i32(&[x0, x1], &[y0, y1]);
        let expected = x.overflowing_sub(y);
        let actual = unsplit(result[0], result[1]);
        expected == (actual as i64, overflowed)
    }

    fn wrapping_sub_ulimb_i32_quickcheck(x: i64, y: u32) -> bool {
        let (x0, x1) = split(x as u64);
        let result = sub::wrapping_ulimb_i32(&[x0, x1], y);
        let expected = x.wrapping_sub(y as i64);
        let actual = unsplit(result[0], result[1]);
        expected == actual as i64
    }

    fn overflowing_sub_ulimb_i32_quickcheck(x: i64, y: u32) -> bool {
        let (x0, x1) = split(x as u64);
        let (result, overflowed) = sub::overflowing_ulimb_i32(&[x0, x1], y);
        let expected = x.overflowing_sub(y as i64);
        let actual = unsplit(result[0], result[1]);
        expected == (actual as i64, overflowed)
    }

    fn wrapping_sub_ilimb_i32_quickcheck(x: i64, y: i32) -> bool {
        let (x0, x1) = split(x as u64);
        let result = sub::wrapping_ilimb_i32(&[x0, x1], y);
        let expected = x.wrapping_sub(y as i64);
        let actual = unsplit(result[0], result[1]);
        expected == actual as i64
    }

    fn overflowing_sub_ilimb_i32_quickcheck(x: i64, y: i32) -> bool {
        let (x0, x1) = split(x as u64);
        let (result, overflowed) = sub::overflowing_ilimb_i32(&[x0, x1], y);
        let expected = x.overflowing_sub(y as i64);
        let actual = unsplit(result[0], result[1]);
        expected == (actual as i64, overflowed)
    }

    fn wrapping_mul_i32_quickcheck(x: i64, y: i64) -> bool {
        let (x0, x1) = split(x as u64);
        let (y0, y1) = split(y as u64);
        let result = mul::wrapping_i32(&[x0, x1], &[y0, y1]);
        let expected = x.wrapping_mul(y);
        let actual = unsplit(result[0], result[1]);
        expected == actual as i64
    }

    fn overflowing_mul_i32_quickcheck(x: i64, y: i64) -> bool {
        let (x0, x1) = split(x as u64);
        let (y0, y1) = split(y as u64);
        let (result, overflowed) = mul::overflowing_i32(&[x0, x1], &[y0, y1]);
        let expected = x.overflowing_mul(y);
        let actual = unsplit(result[0], result[1]);
        expected == (actual as i64, overflowed)
    }

    fn wrapping_mul_ulimb_i32_quickcheck(x: i64, y: u32) -> bool {
        let (x0, x1) = split(x as u64);
        let result = mul::wrapping_ulimb_i32(&[x0, x1], y);
        let expected = x.wrapping_mul(y as i64);
        let actual = unsplit(result[0], result[1]);
        expected == actual as i64
    }

    fn overflowing_mul_ulimb_i32_quickcheck(x: i64, y: u32) -> bool {
        let (x0, x1) = split(x as u64);
        let (result, overflowed) = mul::overflowing_ulimb_i32(&[x0, x1], y);
        let expected = x.overflowing_mul(y as i64);
        let actual = unsplit(result[0], result[1]);
        expected == (actual as i64, overflowed)
    }

    fn wrapping_mul_ilimb_i32_quickcheck(x: i64, y: i32) -> bool {
        let (x0, x1) = split(x as u64);
        let result = mul::wrapping_ilimb_i32(&[x0, x1], y);
        let expected = x.wrapping_mul(y as i64);
        let actual = unsplit(result[0], result[1]);
        expected == actual as i64
    }

    fn overflowing_mul_ilimb_i32_quickcheck(x: i64, y: i32) -> bool {
        let (x0, x1) = split(x as u64);
        let (result, overflowed) = mul::overflowing_ilimb_i32(&[x0, x1], y);
        let expected = x.overflowing_mul(y as i64);
        let actual = unsplit(result[0], result[1]);
        expected == (actual as i64, overflowed)
    }

    fn shl_i32_quickcheck(x: i64, n: u32) -> bool {
        let (x0, x1) = split(x as u64);
        let n = (n % 64) as u32;
        let expected = x << n;
        let result = shift::left_i32([x0, x1], n);
        let actual = unsplit(result[0], result[1]);
        expected == actual as i64
    }

    fn shr_i32_quickcheck(x: i64, n: u32) -> bool {
        let (x0, x1) = split(x as u64);
        let n = (n % 64) as u32;
        let expected = x >> n;
        let result = shift::right_i32([x0, x1], n);
        let actual = unsplit(result[0], result[1]);
        expected == actual as i64
    }

    fn widening_mul_quickcheck(x: u64, y: u64) -> bool {
        let (x0, x1) = split(x as u64);
        let (y0, y1) = split(y as u64);
        let (lo, hi) = mul::widening_u32(&[x0, x1], &[y0, y1]);
        let expected = (x as u128) * (y as u128);
        let lo = unsplit(lo[0], lo[1]) as u128;
        let hi = unsplit(hi[0], hi[1]) as u128;
        expected == lo | (hi << 64)
    }
}
