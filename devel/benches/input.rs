#![allow(dead_code, unused_macros, unused_macro_rules)]

use core::mem;

use bnum::types::U256;

macro_rules! gen_numbers {
    (@4 $t:ident, $count:expr, $seed:ident) => {{
        let mut rng = fastrand::Rng::with_seed($seed);
        let mut vec: Vec<($t, $t, $t, $t)> = Vec::with_capacity($count);
        // TODO: Fix, this is wayyyy too likely to overflow
        // Going to need strategies
        for _ in 0..$count {
            let x0 = rng.$t(<$t>::MIN..<$t>::MAX);
            let x1 = rng.$t(<$t>::MIN..<$t>::MAX);
            let x2 = rng.$t(<$t>::MIN..<$t>::MAX);
            let x3 = rng.$t(<$t>::MIN..<$t>::MAX);
            vec.push((x0, x1, x2, x3));
        }
        vec
    }};

    (@2 $n:ident, $d:ident, $count:expr, $seed:ident) => {{
        let mut rng = fastrand::Rng::with_seed($seed);
        let mut vec: Vec<($n, $d)> = Vec::with_capacity($count);
        // TODO: Fix, this is wayyyy too likely to overflow
        // Going to need strategies
        while vec.len() < $count {
            let num = rng.$n(<$n>::MIN..<$n>::MAX);
            let den = rng.$d(<$d>::MIN..<$d>::MAX);
            if den != 0 {
                vec.push((num, den));
            }
        }
        vec
    }};
}

macro_rules! op_generator {
    (@4 $group:ident, $name:expr, $func:ident, $iter:expr) => {{
        $group.bench_function($name, |bench| {
            bench.iter(|| {
                $iter.for_each(|&x| {
                    criterion::black_box($func(x.0, x.1, x.2, x.3));
                })
            })
        });
    }};

    (@2 $group:ident, $name:expr, $func:ident, $iter:expr) => {{
        $group.bench_function($name, |bench| {
            bench.iter(|| {
                $iter.for_each(|&x| {
                    criterion::black_box($func(x.0, x.1));
                })
            })
        });
    }};
}

macro_rules! native_op {
    ($t:ident, $w:ident, $name:ident, $op:ident) => {
        fn $name(x0: $t, x1: $t, y0: $t, y1: $t) -> ($t, $t) {
            let x: $w = (x0 as $w) | (x1 as $w) << $t::BITS;
            let y: $w = (y0 as $w) | (y1 as $w) << $t::BITS;
            let z = x.$op(y);
            (z as $t, (z >> $t::BITS) as $t)
        }
    };
}

pub fn bnum_from_u128(x: u128, y: u128) -> U256 {
    let buf = [x.to_le(), y.to_le()];
    // SAFETY: plain old data
    let slc = unsafe { mem::transmute::<[u128; 2], [u8; 32]>(buf) };
    U256::from_le_slice(&slc).unwrap()
}

pub fn bnum_from_u64(x0: u64, x1: u64, y0: u64, y1: u64) -> U256 {
    bnum_from_u128(x0 as u128 | (x1 as u128) << 64, y0 as u128 | (y1 as u128) << 64)
}
