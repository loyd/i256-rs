//! Helpers and logic for working with traits.

macro_rules! define {
    // NOTE: A lot of this looks horrifying but it's so we can
    // have a trait with a required namespace prefix, that is
    // optional. This is mostly so we can avoid importing
    // `core::ops` everywhere.

    // Implment a trait, just only with the op and no assign.
    ($(
        type => $t:ty,
        impl => $trait:ident $(:: $ns:ident)*,
        op => $op:ident,
    )*) => ($(
        impl $trait $(::$ns)* <&$t> for $t {
            type Output = <Self as $trait $(::$ns)* >::Output;

            #[inline(always)]
            fn $op(self, rhs: &Self) -> Self::Output {
                <Self as $trait $(::$ns)* > :: $op(self, *rhs)
            }
        }
    )*);

    // Implement a trait, including the op and the assign in place op.
    ($(
        type => $t:ty,
        impl => $trait:ident $(:: $ns1:ident)*,
        op => $op:ident,
        assign => $assign:ident $(:: $ns2:ident)*,
        assign_op => $op_assign:ident,
    )*) => ($(
        impl $trait $(::$ns1)* <&$t> for $t {
            type Output = <Self as $trait $(::$ns1)* >::Output;

            #[inline(always)]
            fn $op(self, rhs: &Self) -> Self::Output {
                <Self as $trait $(::$ns1)* > :: $op(self, *rhs)
            }
        }

        impl $assign $(::$ns2)* for $t {
            #[inline(always)]
            fn $op_assign(&mut self, other: Self) {
                *self = <Self as $trait $(::$ns1)* > :: $op(*self, other);
            }
        }

        impl $assign $(::$ns2)* <&$t> for $t {
            #[inline(always)]
            fn $op_assign(&mut self, other: &Self) {
                *self = <Self as $trait $(::$ns1)* > :: $op(*self, *other);
            }
        }
    )*);

    // Convert a value from a type to another using a built-in op.
    ($(
        to => $to:ty,
        from => $from:ty,
        op => $op:ident,
        $(extras => $(as $cast:ty)?,)?
    )*) => ($(
        impl From<$from> for $to {
            #[inline(always)]
            fn from(value: $from) -> Self {
                Self::$op(value $($(as $cast)?)?)
            }
        }
    )*);

    // Create an impl trait for a reference, with optional arguments
    ($(
        ref => $t:ty,
        impl => $trait:ident $(:: $ns:ident)*,
        op => $op:ident,
        $(args => $($args:ident:$type:ty,)* ;)?
    )*) => ($(
        impl $trait $(::$ns)* for &$t {
            type Output = <$t as $trait $(::$ns)* >::Output;

            #[inline(always)]
            fn $op(self $($(, $args: $type)*)?) -> Self::Output {
                $trait $(::$ns)* :: $op(*self $($(, $args)*)?)
            }
        }
    )*);

    // A TryFrom implementation for a type.
    ($(
        to => $to:ty,
        tryfrom => $from:ty,
        op => $op:ident,
        $(extras => $(as $cast:ty)?,)?
    )*) => ($(
        impl TryFrom<$from> for $to {
            type Error = $crate::TryFromIntError;

            #[inline(always)]
            fn try_from(u: $from) -> Result<Self, $crate::TryFromIntError> {
                if u >= 0 {
                    Ok(Self::$op(u $($(as $cast)?)?))
                } else {
                    Err($crate::TryFromIntError {})
                }
            }
        }
    )*);

    // This is the high-level implementation for a single type
    (impl => $t:ident) => {
        $crate::shared::bitops::traits!($t);
        $crate::shared::ops::traits!($t);
        $crate::shared::ord::traits!($t);

        $crate::shared::shift::define! { primitive => $t, impl => i8 i16 i32 i64 i128 isize u8 u16 u32 u64 u128 usize }
        $crate::shared::shift::define! { reference => $t, impl => i8 i16 i32 i64 i128 isize u8 u16 u32 u64 u128 usize }

        impl core::fmt::Debug for $t {
            #[inline(always)]
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> Result<(), core::fmt::Error> {
                core::fmt::Display::fmt(self, f)
            }
        }

        $crate::shared::traits::define! {
            to => $t, from => u8, op => from_u8,
            to => $t, from => u16, op => from_u16,
            to => $t, from => u32, op => from_u32,
            to => $t, from => u64, op => from_u64,
            to => $t, from => u128, op => from_u128,
            to => $t, from => bool, op => from_u8, extras => as u8,
            to => $t, from => char, op => from_u32, extras => as u32,
        }
    };
}

pub(crate) use define;
