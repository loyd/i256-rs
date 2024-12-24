#![allow(dead_code, unused_macros, unused_macro_rules)]

use std::mem;

pub use bnum::types::U256 as Bnum256;
pub use crypto_bigint::U256 as CryptoU256;
use fastrand::Rng;
pub use i256::u256;

const DEFAULT_COUNT: usize = 10000;

#[derive(Copy, Clone, Hash, PartialEq, Eq)]
pub enum RandomGen {
    // Generic
    Uniform,

    // Integers
    Simple,
    SimpleSigned,
    Large,
    LargeSigned,
}

pub trait NumberRng: Sized + Default + Copy {
    fn uniform(rng: &mut Rng) -> Self;
    fn simple(rng: &mut Rng) -> Self;
    fn large(rng: &mut Rng) -> Self;
    fn simple_signed(rng: &mut Rng) -> Self;
    fn large_signed(rng: &mut Rng) -> Self;
    fn zero() -> Self;

    #[inline]
    fn gen(strategy: RandomGen, rng: &mut Rng) -> Self {
        match strategy {
            RandomGen::Uniform => Self::uniform(rng),
            RandomGen::Simple => Self::simple(rng),
            RandomGen::SimpleSigned => Self::simple_signed(rng),
            RandomGen::Large => Self::large(rng),
            RandomGen::LargeSigned => Self::large_signed(rng),
        }
    }

    #[inline]
    fn gen_n<const N: usize>(strategy: RandomGen, rng: &mut Rng, count: usize) -> Vec<[Self; N]> {
        let mut vec: Vec<[Self; N]> = Vec::with_capacity(count);
        let is_simple = matches!(strategy, RandomGen::Simple | RandomGen::SimpleSigned);
        for _ in 0..count {
            let mut value = [Self::default(); N];
            for j in 0..N {
                value[j] = match (is_simple, j % 2) {
                    // NOTE: Simple should always have the hi digit as 0.
                    (true, 1) => Self::zero(),
                    _ => Self::gen(strategy, rng),
                };
            }
            vec.push(value);
        }
        vec
    }
}

macro_rules! unsigned_rng {
    ($($t:ident $smin:literal $smax:literal $lmin:literal $lmax:literal ; )*) => ($(
        impl NumberRng for $t {
            #[inline]
            fn uniform(rng: &mut Rng) -> $t {
                (rng.$t(<$t>::MIN..<$t>::MAX))
            }

            #[inline]
            fn simple(rng: &mut Rng) -> $t {
                (rng.$t($smin..$smax))
            }

            #[inline]
            fn simple_signed(_: &mut Rng) -> $t {
                unimplemented!()
            }

            #[inline]
            fn large(rng: &mut Rng) -> $t {
                (rng.$t($lmin..$lmax))
            }

            #[inline]
            fn large_signed(_: &mut Rng) -> $t {
                unimplemented!()
            }

            #[inline]
            fn zero() -> $t {
                0
            }
        }
    )*);
}

unsigned_rng! {
    u8 0 50 100 255 ;
    u16 0 1000 1024 65535 ;
    u32 0 1000 67108864 4294967295 ;
    u64 0 1000 288230376151711744 18446744073709551615 ;
    u128 0 1000 5316911983139663491615228241121378304 340282366920938463463374607431768211455 ;
}

macro_rules! signed_rng {
    ($(
        $t:ident
        $smin:literal $smax:literal $lmin:literal $lmax:literal
        $ssmin:literal $ssmax:literal $lsmin:literal $lsmax:literal
        ;
    )*) => ($(
        impl NumberRng for $t {
            #[inline]
            fn uniform(rng: &mut Rng) -> $t {
                (rng.$t(<$t>::MIN..<$t>::MAX))
            }

            #[inline]
            fn simple(rng: &mut Rng) -> $t {
                (rng.$t($smin..$smax))
            }

            #[inline]
            fn simple_signed(rng: &mut Rng) -> $t {
                (rng.$t($ssmin..$ssmax))
            }

            #[inline]
            fn large(rng: &mut Rng) -> $t {
                (rng.$t($lmin..$lmax))
            }

            #[inline]
            fn large_signed(rng: &mut Rng) -> $t {
                (rng.$t($lsmin..$lsmax))
            }

            #[inline]
            fn zero() -> $t {
                0
            }
        }
    )*);
}

signed_rng! {
    i8 0 50 100 127 -50 50 -127 -100 ;
    i16 0 1000 1024 32767 -1000 1000 -32767 -1024 ;
    i32 0 1000 67108864 2147483647 -1000 1000 -2147483647 -67108864 ;
    i64 0 1000 288230376151711744 9223372036854775807 -1000 1000 -9223372036854775807 -288230376151711744 ;
    i128 0 1000 5316911983139663491615228241121378304 170141183460469231731687303715884105727 -1000 1000 -170141183460469231731687303715884105727 -5316911983139663491615228241121378304 ;
}

macro_rules! add_bench {
    ($group:ident, $name:expr, $iter:expr, $func:expr) => {{
        $group.bench_function($name, |bench| {
            bench.iter(|| {
                $iter.for_each(|x| {
                    criterion::black_box($func(x));
                })
            })
        });
    }};
}

macro_rules! add_benches {
    ($group:ident, $strategy:expr, $rng:ident, $prefix:literal, $op:ident) => {{
        let bnum_data = get_bnum_data($strategy, &mut $rng);
        let crypto_data = get_crypto_data($strategy, &mut $rng);
        let i256_data = get_i256_data($strategy, &mut $rng);

        add_bench!($group, concat!($prefix, "::u256-bnum"), bnum_data.iter(), |x: &(
            Bnum256,
            Bnum256
        )| x
            .0
            .$op(x.1));
        add_bench!($group, concat!($prefix, "::u256-crypto"), crypto_data.iter(), |x: &(
            CryptoU256,
            CryptoU256
        )| x
            .0
            .$op(&x.1));
        add_bench!($group, concat!($prefix, "::u256-i256"), i256_data.iter(), |x: &(
            u256,
            u256
        )| x
            .0
            .$op(x.1));
    }};
}

pub fn get_bnum_data(strategy: RandomGen, rng: &mut Rng) -> Vec<(Bnum256, Bnum256)> {
    u128::gen_n::<4>(strategy, rng, DEFAULT_COUNT)
        .iter()
        .map(|x| (to_bnum(x[0], x[1]), to_bnum(x[2], x[3])))
        .collect()
}

pub fn get_crypto_data(strategy: RandomGen, rng: &mut Rng) -> Vec<(CryptoU256, CryptoU256)> {
    u128::gen_n::<4>(strategy, rng, DEFAULT_COUNT)
        .iter()
        .map(|x| (to_cryptobi(x[0], x[1]), to_cryptobi(x[2], x[3])))
        .collect()
}

pub fn get_i256_data(strategy: RandomGen, rng: &mut Rng) -> Vec<(u256, u256)> {
    u128::gen_n::<4>(strategy, rng, DEFAULT_COUNT)
        .iter()
        .map(|x| (u256::new(x[0], x[1]), u256::new(x[2], x[3])))
        .collect()
}

pub fn get_small_data(strategy: RandomGen, rng: &mut Rng) -> Vec<(u256, u128)> {
    u128::gen_n::<3>(strategy, rng, DEFAULT_COUNT)
        .iter()
        .map(|x| (u256::new(x[0], x[1]), x[2]))
        .collect()
}

pub fn get_half_data(strategy: RandomGen, rng: &mut Rng) -> Vec<(u256, u64)> {
    let x = u128::gen_n::<2>(strategy, rng, DEFAULT_COUNT);
    let y = u64::gen_n::<1>(strategy, rng, DEFAULT_COUNT);
    x.iter().zip(y.iter()).map(|(x, y)| (u256::new(x[0], x[1]), y[0])).collect()
}

pub fn to_bnum(x: u128, y: u128) -> Bnum256 {
    let buf = [x.to_le_bytes(), y.to_le_bytes()];
    // SAFETY: plain old data
    let slc = unsafe { mem::transmute::<[[u8; 16]; 2], [u8; 32]>(buf) };
    Bnum256::from_le_slice(&slc).unwrap()
}

pub fn to_cryptobi(lo: u128, hi: u128) -> CryptoU256 {
    // SAFETY: plain old data
    let bytes: [u8; 32] = unsafe { mem::transmute([lo.to_le_bytes(), hi.to_le_bytes()]) };
    CryptoU256::from_le_slice(&bytes)
}
