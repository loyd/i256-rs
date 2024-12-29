#[macro_use]
mod util;

use i256::math::div;
use quickcheck::quickcheck;

fn uwide_div(num: i256::UWide, den: i256::UWide) -> (i256::UWide, i256::UWide) {
    let x0 = num as i256::ULimb;
    let x1 = (num >> i256::ULimb::BITS) as i256::ULimb;
    let y0 = den as i256::ULimb;
    let y1 = (den >> i256::ULimb::BITS) as i256::ULimb;

    let num = [x0, x1];
    let den = [y0, y1];
    let (div, rem) = div::full(&num, &den);

    let x0 = div[0] as i256::UWide;
    let x1 = div[1] as i256::UWide;
    let y0 = rem[0] as i256::UWide;
    let y1 = rem[1] as i256::UWide;

    (x0 | x1 << i256::ULimb::BITS, y0 | y1 << i256::ULimb::BITS)
}

fn uwide_div_wide(num: i256::UWide, den: i256::ULimb) -> (i256::UWide, i256::ULimb) {
    let x0 = num as i256::ULimb;
    let x1 = (num >> i256::ULimb::BITS) as i256::ULimb;

    let num = [x0, x1];
    let (div, rem) = div::wide(&num, den as i256::UWide);

    let x0 = div[0] as i256::UWide;
    let x1 = div[1] as i256::UWide;

    (x0 | x1 << i256::ULimb::BITS, rem as i256::ULimb)
}

fn uwide_div_limb(num: i256::UWide, den: i256::ULimb) -> (i256::UWide, i256::ULimb) {
    let x0 = num as i256::ULimb;
    let x1 = (num >> i256::ULimb::BITS) as i256::ULimb;

    let num = [x0, x1];
    let (div, rem) = div::limb(&num, den);

    let x0 = div[0] as i256::UWide;
    let x1 = div[1] as i256::UWide;

    (x0 | x1 << i256::ULimb::BITS, rem)
}

quickcheck! {
    fn uwide_div_quickcheck(num: i256::UWide, den: i256::UWide) -> bool {
        if den != 0 {
            let actual = uwide_div(num, den);
            let div = num / den;
            let rem = num % den;
            actual == (div, rem)
        } else {
            true
        }
    }

    fn uwide_div_wide_quickcheck(num: i256::UWide, den: i256::ULimb) -> bool {
        if den != 0 {
            let actual = uwide_div_wide(num, den);
            let div = num / (den as i256::UWide);
            let rem = num % (den as i256::UWide);
            actual == (div, rem as i256::ULimb)
        } else {
            true
        }
    }

    fn uwide_div_limb_quickcheck(num: i256::UWide, den: i256::ULimb) -> bool {
        if den != 0 {
            let actual = uwide_div_limb(num, den);
            let div = num / (den as i256::UWide);
            let rem = num % (den as i256::UWide);
            actual == (div, rem as i256::ULimb)
        } else {
            true
        }
    }

    fn u256_div_quickcheck(x0: u128, x1: u128, y0: u128, y1: u128) -> bool {
        if y0 != 0 && y1 != 0 {
            unsigned_op_equal!(wrap x0, x1, y0, y1, wrapping_div)
        } else {
            true
        }
    }
}
