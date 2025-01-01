//! Overflowing mathmetical operations, which saturate max or min on overflow.

#[rustfmt::skip]
macro_rules! define {
    (
        type => $t:ty,
        wide_type => $wide_t:ty,
        see_type => $see_t:ty $(,)?
    ) => {
        // Currently a no-op
    };
}

pub(crate) use define;
