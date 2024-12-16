use i256::math::{div_rem_big, div_rem_small};
use quickcheck::quickcheck;

fn u128_div(num: u128, den: u128) -> (u128, u128) {
    let x0 = num as u64;
    let x1 = (num >> 64) as u64;
    let y0 = den as u64;
    let y1 = (den >> 64) as u64;

    let num = [x0, x1];
    let den = [y0, y1];
    let (div, rem) = div_rem_big(&num, &den);

    let x0 = div[0] as u128;
    let x1 = div[1] as u128;
    let y0 = rem[0] as u128;
    let y1 = rem[1] as u128;

    (x0 | x1 << 64, y0 | y1 << 64)
}

fn u128_div_small(num: u128, den: u64) -> (u128, u64) {
    let x0 = num as u64;
    let x1 = (num >> 64) as u64;

    let num = [x0, x1];
    let (div, rem) = div_rem_small(&num, den);

    let x0 = div[0] as u128;
    let x1 = div[1] as u128;

    (x0 | x1 << 64, rem)
}

quickcheck! {
    fn u128_div_quickcheck(num: u128, den: u128) -> bool {
        if den != 0 {
            let actual = u128_div(num, den);
            let div = num / den;
            let rem = num % den;
            actual == (div, rem)
        } else {
            true
        }
    }

    fn u128_div_small_quickcheck(num: u128, den: u64) -> bool {
        if den != 0 {
            let actual = u128_div_small(num, den);
            let div = num / (den as u128);
            let rem = num % (den as u128);
            actual == (div, rem as u64)
        } else {
            true
        }
    }
}
