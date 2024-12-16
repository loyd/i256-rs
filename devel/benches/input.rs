#![allow(dead_code, unused_macros, unused_macro_rules)]

macro_rules! gen_numbers {
    ($t:ident, $count:expr, $seed:ident) => {{
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
}

macro_rules! op_generator {
    ($group:ident, $name:expr, $func:ident, $iter:expr) => {{
        $group.bench_function($name, |bench| {
            bench.iter(|| {
                $iter.for_each(|&x| {
                    criterion::black_box($func(x.0, x.1, x.2, x.3));
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
