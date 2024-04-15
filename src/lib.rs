// Work with refined bounded numeric types in Rust.
// Copyright (C) 2021   <Roberto Guillén>
//
// This program is free software: you can redistribute it and/or modify
// it under the terms of the GNU General Public License as published by
// the Free Software Foundation, either version 2 of the License, or (at
// your option) any later version.
//
// This program is distributed in the hope that it will be useful, but
// WITHOUT ANY WARRANTY; without even the implied warranty of
// MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
// General Public License for more details.
//
// You should have received a copy of the GNU General Public License
// along with this program.  If not, see <http://www.gnu.org/licenses/>.
//

/*!
This crate defines multiple types, traits and operators
implementations for working with bounded numbers, which allows to
define refined number types whose possible values are assured to be
present inside a specific numeric range in compile time. **This crate
uses experimental and incompleted compiler functions such as
`generic_const_exprs` feature. Therefore, nightly compiler builds are
required, and no stability is guaranteed**.

For example, you may define a [u8] number contained between 0 and 100,
for defining a type that represents a percent value:

```
use bounded_nums::BoundedU8;

fn do_stuff(value: u8) {
    let my_percent = BoundedU8::<0, 100>::from_u8(value).expect("Value out of bounds!");
}
```

The bounds of this numbers can be adjusted as required. If we want to
grow the possible bounds of the number, we can just do:

```
use bounded_nums::BoundedU8;

fn do_stuff(value: u8) {
    let my_percent = BoundedU8::<0, 100>::from_u8(value).expect("Value out of bounds!");
    let not_a_percent_anymore: BoundedU8<0, 200> = my_percent.grow::<0, 200>();
}
```

The [BoundedU8::grow] function can only take as type
parameters a range that fully contains the original range of the
number. Otherwise, the call to this function won't compile. Of course,
this also means that the [BoundedU8::grow] cannot ever
fail, as is ensured that the new range will contain the number
represented by the current bounded number.

However, if the bounds of the number wants to be changed, the
[BoundedU8::remap] can be used instead. In this case,
that function will return a [Result] value instead, since the
operation may fail in runtime in case the the contained number is not
within the new provided range.

Also, bounded numbers can be operated between them, returning a new
bounded number guaranteed to be contained within the range of possible
values of the operation:

```
use bounded_nums::BoundedU8;

fn do_stuff(value: u8) {
    let my_percent = BoundedU8::<0, 100>::from_u8(value).expect("Value out of bounds!");
    let sum: BoundedU8<0, 200> = my_percent + my_percent;
}
```

This also applies to other operations such as the subtraction and
the multiplication of bounded numbers. However, it won't compile
in case that the operation overflows the underlying number type:

```compile_fail
use bounded_nums::BoundedU8;

fn do_stuff(value: u8) {
    let my_percent = BoundedU8::<0, 100>::from_u8(value).expect("Value out of bounds!");

    // This doesn't compile, as the result can only be guaranteed to
    // be between 0 and 300, which overflows the u8 type.
    let sum = my_percent + my_percent + my_percent;
}
```

This crates also includes the `AsBoundedXX<M, N>` traits (for example,
the [AsBoundedU8]), which is implemented by both, any bounded type and
any primitive numeric type that can be safely casted into
`BoundedXX<M, N>`. It can be used to generify function definitions to
make easier using bounded types. For example:

```
use bounded_nums::{BoundedI128, AsBoundedU8, AsBoundedI32};

fn print_percent<N: AsBoundedU8<0, 100>>(percent: N) {
    println!("{}%", percent.as_bounded_u8().value());
}

fn do_whatever<N: AsBoundedI32<{-300}, 300>>(percent: N) {
    // ...
}

fn main() {
    let my_number = BoundedI128::<30, 70>::from_const::<45>();

    // This function can be called without any prior conversion, since
    // a i128 number between 30 and 70 is safely representable as a u8
    // number between 0 and 100 and, therefore, implements
    // BoundedU8<0, 100>.
    print_percent(my_number);

    let other_number: i8 = 5;

    // The primitive number i8 can be safely represented as a bounded
    // number between -300 and 300, since i8 values can just go
    // between -128 and 127.
    do_whatever(other_number);
}
```
*/

#![feature(generic_const_exprs)]
#![allow(unused)]
#![allow(incomplete_features)]

use std::{
    convert::TryFrom,
    error::Error,
    ops::{Add, Div, Mul, Sub},
};

pub mod internal;
use internal::*;

// It seems that using the < symbol inside a generic type specifier
// produces some syntax analysis issues on my editor (Emacs + Racer.).
// So, I'm moving the <= operation out to a macro just for preventing
// that.
macro_rules! le {
    ($l:expr, $r: expr) => {
        ($l) <= ($r)
    };
}

/// Error that happens when a numeric value, either a primitive or a
/// bounded one, fails to be fit into a bounded number because it is
/// out of its allowed range.
#[derive(Debug)]
pub enum BoundariesError {
    /// Indicates that the error is caused because the provided
    /// unconstrained number is above of the allowed bounds.
    Overflow,

    /// Indicates that the error is caused because the provided
    /// unconstrained number is below of the allowed bounds.
    Underflow,
}

impl std::fmt::Display for BoundariesError {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            &BoundariesError::Overflow => f.write_str("Overflow"),
            &BoundariesError::Underflow => f.write_str("Underflow"),
        }
    }
}

impl Error for BoundariesError {}

pub type Result<R> = std::result::Result<R, BoundariesError>;

macro_rules! gen_bounded_num {
    (@impl $tnum:ty, $tupper:ty) => {
	paste::paste! {
	    bounded_num_impl!(@impl $tnum, [<Bounded $tupper>], [<WhereExpr2 $tupper>], [<AsBounded $tupper>], [<max_ $tnum>], [<min_ $tnum>], [<max4_ $tnum>], [<min4_ $tnum>]);
	}
    };

    ([$($tnum:ty)+]) => {
	$(
	    gen_bounded_num!($tnum);
	)+
    };

    ($tnum:ty) => {
	paste::paste! {
	    gen_bounded_num!(@gen
			     t_num: $tnum,
			     t_impl: [<Bounded $tnum:upper>],
			     t_where_expr2: [<WhereExpr2 $tnum:upper>],
			     t_as_bounded: [<AsBounded $tnum:upper>],
			     fn_max4: [<max4_ $tnum>],
			     fn_min4: [<min4_ $tnum>]
	    );
	}
    };

    // Branch that effectively generates all the components required
    // for a specific bounded numeric type.
    (@gen
     t_num: $t_num:ty,                          /* Name of the numeric type (u8, u16...) which implementation is being generated. */
     t_impl: $t_impl:ident,                     /* Name of the struct that will represent a bounded number of type $t_num. (BoundedU8, BoundedU16...). */
     t_where_expr2: $t_where_expr2:ident,       /* Name of the struct that will be used for adding const wf to functions/impls. Struct defined on internal mod. */
     t_as_bounded: $t_as_bounded:ident,         /* Name of the AsBounded* trait that will be generated (AsBoundedU8, AsBoundedU16...). */
     fn_max4: $fn_max4:ident,                   /* Name of the function that will be used to compute the max number among for elements. Defined on internal mod. */
     fn_min4: $fn_min4:ident)                   /* Name of the function that will be used to compute the min number among for elements. Defined on internal mod. */
	=> {
            gen_bounded_num!(@gen_bounded_struct $t_num, $t_impl);
	    gen_bounded_num!(@gen_add_impl $t_num, $t_impl, $t_where_expr2);
	    gen_bounded_num!(@gen_sub_impl $t_num, $t_impl, $t_where_expr2);
	    gen_bounded_num!(@gen_mul_impl $t_num, $t_impl, $t_where_expr2, $fn_max4, $fn_min4);
	    gen_bounded_num!(@gen_as_bounded_trait $t_num, $t_impl, $t_as_bounded);
	};


    // Branch that generates the struct that represents the bounded
    // type (ex BoundedU32, BoundedI128) and it's basic
    // implementation.
    (@gen_bounded_struct $t_num:ty, $t_impl:ident) => {
	paste::paste! {
	    #[repr(transparent)]
            #[derive(Clone, Copy, PartialEq, PartialOrd, Eq, Ord)]
	    #[doc = "Holds a [" $t_num "] number which is guaranteed in compile-time that is inside the closed range `[M, N]`."]
            pub struct $t_impl<const M: $t_num, const N: $t_num> {
		value: $t_num,
            }
	}

	impl <const M: $t_num, const N: $t_num> std::fmt::Display for $t_impl<M, N> {
	    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		std::fmt::Display::fmt(&self.value, f)
	    }
	}

	impl <const M: $t_num, const N: $t_num> std::fmt::Debug for $t_impl<M, N> {
	    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
		write!(f, "{}<{}, {}>({})", stringify!($t_impl), M, N, self.value)
	    }
	}

        #[allow(unused)]
        impl<const M: $t_num, const N: $t_num> $t_impl<M, N> {
	    /// Infallibly returns the same number held by self, but
	    /// represented in a wider range, `[M1, N1]`, which fully
	    /// contains the current range `[M, N]`.  Thus, it must be
	    /// satisfied that `M1 <= M <= N <= N1`.  If the new
	    /// specified range `[M1, N1]` doesn't satisfy that
	    /// invariant, the call to this function won't compile.
	    pub const fn grow<const M1: $t_num, const N1: $t_num>(self) -> $t_impl<M1, N1>
	    where
                And<E<{ le!(M1, M) }>, E<{ le!(N, N1) }>>: IsTrue,
	    {
                $t_impl { value: self.value }
	    }

	    /// Returns the same number held by self, but in a
	    /// different range, `[M1, N1]`. If the current number is
	    /// not inside that new range, the remap operation will
	    /// fail.
            pub const fn remap<const M1: $t_num, const N1: $t_num>(self) -> Result<$t_impl<M1, N1>>
            where
                E<{ le!(M1, N1) }>: IsTrue,
            {
		if self.value < M1 {
		    Err(BoundariesError::Underflow)
		} else if self.value > N1 {
		    Err(BoundariesError::Overflow)
		} else {
		    Ok($t_impl { value: self.value })
		}
            }

	    paste::paste! {
		#[doc = "Builds a new [" $t_impl "] from an [" $t_num "] number, inside the range `[M, N]`, only if the given number is inside that range. Otherwise, the operation fails."]
		pub const fn [<from_ $t_num>](value: $t_num) -> Result<$t_impl<M, N>>
		where
                    E<{ le!(M, N) }>: IsTrue,
		{
		    if value < M {
			Err(BoundariesError::Underflow)
		    } else if value > N {
			Err(BoundariesError::Overflow)
		    } else {
			Ok($t_impl { value })
		    }
		}
	    }

	    paste::paste! {
		#[doc = "Builds a new [" $t_impl "] from a const generic number. It must be satisfied that `M <= O <= N`. Otherwise the call to this function won't compile."]
		pub const fn from_const<const O: $t_num>() -> $t_impl<M, N>
		where
                    And<E<{ le!(M, O) }>, E<{ le!(O, N) }>>: IsTrue,
		{
                    $t_impl { value: O }
		}
	    }

	    /// Returns the number held by self.
            pub const fn value(self) -> $t_num {
                self.value
            }
        }
    };

    // Branch that generates the implementation for Add operator for a specific bounded numeric type.
    (@gen_add_impl $t_num:ty, $t_impl:ident, $t_where_expr2:ident) => {
	impl<const M: $t_num, const N: $t_num, const M1: $t_num, const N1: $t_num> Add<$t_impl<M1, N1>>
	    for $t_impl<M, N> where
	    $t_where_expr2<{M + M1}, {N + N1}>:
	{
	    type Output = $t_impl<{M + M1}, {N + N1}>;

	    fn add(self, rhs: $t_impl<M1, N1>) -> Self::Output {
		$t_impl {
		    value: self.value + rhs.value
		}
	    }
	}
    };

    // Branch that generates the implementation for Sub operator for a specific bounded numeric type.
    (@gen_sub_impl $t_num:ty, $t_impl:ident, $t_where_expr2:ident) => {
	impl<const M: $t_num, const N: $t_num, const M1: $t_num, const N1: $t_num> Sub<$t_impl<M1, N1>>
	    for $t_impl<M, N> where
	    $t_where_expr2<{M - N1}, {N - M1}>:
	{
	    type Output = $t_impl<{M - N1}, {N - M1}>;

	    fn sub(self, rhs: $t_impl<M1, N1>) -> Self::Output {
		$t_impl {
		    value: self.value - rhs.value
		}
	    }
	}
    };

    // Branch that generates the implementation for Mul operator for a specific bounded numeric type.
    (@gen_mul_impl $t_num:ty, $t_impl:ident, $t_where_expr2:ident, $fn_max4:ident, $fn_min4:ident) => {
	impl<const M: $t_num, const N: $t_num, const M1: $t_num, const N1: $t_num> Mul<$t_impl<M1, N1>>
	    for $t_impl<M, N> where
	    $t_where_expr2<{$fn_min4(M * M1, M * N1, N * M1, N * N1)}, {$fn_max4(M * M1, M * N1, N * M1, N * N1)}>:
	{
	    type Output = $t_impl<{$fn_min4(M * M1, M * N1, N * M1, N * N1)}, {$fn_max4(M * M1, M * N1, N * M1, N * N1)}>;

	    fn mul(self, rhs: $t_impl<M1, N1>) -> Self::Output {
		$t_impl {
		    value: self.value * rhs.value
		}
	    }
	}
    };

    // TODO Div impl!

    // Branch that generates the definition of the Trait AsBounded* for a specific bounded numeric type.
    (@gen_as_bounded_trait $tnum:ty, $t_impl:ident, $t_as_bounded:ident) => {
	paste::paste! {
	    #[doc = "Trait implemented by that types that can be infallibly casted into a [" $t_impl "]. This trait must be implemented by any type of bounded number, as long as its bounds are contained into the range `[M, N]`."]
	    pub trait $t_as_bounded<const M: $tnum, const N: $tnum> {
		fn [<as_bounded_ $tnum>](self) -> $t_impl<M, N>;
	    }
	}
    };
}

macro_rules! as_bounded_impl {
    (@impl2 $tnum:ty, $impl:ty) => {
	paste::paste! {
	    impl<const M: $tnum, const N: $tnum, const M1: $impl, const N1: $impl> [< AsBounded $tnum:upper >]<M, N> for [< Bounded $impl:upper >]<M1, N1>
	    where E<{[< is_as_bounded_implemented_for_ $tnum _from_ $impl >](M, N, M1, N1)}>: IsTrue {

		fn [<as_bounded_ $tnum>](self) -> [< Bounded $tnum:upper >]<M, N> {
		    [< Bounded $tnum:upper >] {
			value: (self.value as $tnum)
		    }
		}
	    }

	    impl<const M: $tnum, const N: $tnum> [< AsBounded $tnum:upper >]<M, N> for $impl
	    where E<{[< is_as_bounded_implemented_for_ $tnum _from_ $impl >](M, N, $impl::MIN, $impl::MAX)}>: IsTrue {
		fn [<as_bounded_ $tnum>](self) -> [< Bounded $tnum:upper >]<M, N> {
		    [< Bounded $tnum:upper >] {
			value: (self as $tnum)
		    }
		}
	    }
	}
    };

    (@impl1 $tnum:ty, [$($impl:ty)*]) => {
	$(
	    as_bounded_impl!(@impl2 $tnum, $impl);
	)+
    };

    ([$($tnum:ty)*]) => {
	$(
	    as_bounded_impl!(@impl1 $tnum, [u8 u16 u32 u64 u128 i8 i16 i32 i64 i128]);
	)*
    };
}

gen_bounded_num!([u8 u16 u32 u64 u128 i8 i16 i32 i64 i128]);
as_bounded_impl!([u8 u16 u32 u64 u128 i8 i16 i32 i64 i128]);

#[cfg(test)]
mod tests {
    use std::ops::{Add, Div, Mul, Sub};
    macro_rules! gen_test_fun {
        ($name:ident, $ltype:ty, $rtype:ty, $ctype:ty, $f:ident) => {
            fn $name(l: $ltype, r: $rtype) -> $ctype {
                l.$f(r)
            }
        };
    }

    use super::{BoundedI32, BoundedU32};

    #[test]
    fn bounded_u32_display_ok() {
        assert_eq!(
            "55",
            format!("{}", BoundedU32::<0, 100>::from_const::<55>())
        );
    }

    #[test]
    fn bounded_u32_debug_ok() {
        assert_eq!(
            "BoundedU32<0, 100>(96)",
            format!("{:?}", BoundedU32::<0, 100>::from_const::<96>())
        );
    }

    #[test]
    fn bounded_u32_add_bounds_ok() {
        gen_test_fun!(a, BoundedU32<50, 100>, BoundedU32<10, 20>, BoundedU32<60, 120>, add);
        gen_test_fun!(b, BoundedU32<0, 50>, BoundedU32<60, 100>, BoundedU32<60, 150>, add);
    }

    #[test]
    fn bounded_u32_sub_bounds_ok() {
        gen_test_fun!(a, BoundedU32<50, 100>, BoundedU32<10, 20>, BoundedU32<30, 90>, sub);
    }

    #[test]
    fn bounded_u32_mul_bounds_ok() {
        gen_test_fun!(a, BoundedU32<50, 100>, BoundedU32<10, 20>, BoundedU32<500, 2000>, mul);
    }

    #[test]
    fn bounded_i32_add_bounds_ok() {
        gen_test_fun!(a, BoundedI32<50, 100>, BoundedI32<10, 20>, BoundedI32<60, 120>, add);
        gen_test_fun!(b, BoundedI32<50, 100>, BoundedI32<{-10}, 20>, BoundedI32<40, 120>, add);
        gen_test_fun!(c, BoundedI32<50, 100>, BoundedI32<{-20}, {-10}>, BoundedI32<30, 90>, add);

        gen_test_fun!(d, BoundedI32<{-50}, 100>, BoundedI32<10, 20>, BoundedI32<{-40}, 120>, add);
        gen_test_fun!(e, BoundedI32<{-50}, 100>, BoundedI32<{-10}, 20>, BoundedI32<{-60}, 120>, add);
        gen_test_fun!(f, BoundedI32<{-50}, 100>, BoundedI32<{-20}, {-10}>, BoundedI32<{-70}, 90>, add);

        gen_test_fun!(g, BoundedI32<{-100}, {-50}>, BoundedI32<10, 20>, BoundedI32<{-90}, {-30}>, add);
        gen_test_fun!(h, BoundedI32<{-100}, {-50}>, BoundedI32<{-10}, 20>, BoundedI32<{-110}, {-30}>, add);
        gen_test_fun!(i, BoundedI32<{-100}, {-50}>, BoundedI32<{-20}, {-10}>, BoundedI32<{-120}, {-60}>, add);
    }

    #[test]
    fn bounded_i32_sub_bounds_ok() {
        gen_test_fun!(a, BoundedI32<50, 100>, BoundedI32<10, 20>, BoundedI32<30, 90>, sub);
        gen_test_fun!(b, BoundedI32<50, 100>, BoundedI32<{-10}, 20>, BoundedI32<30, 110>, sub);
        gen_test_fun!(c, BoundedI32<50, 100>, BoundedI32<{-20}, {-10}>, BoundedI32<60, 120>, sub);

        gen_test_fun!(d, BoundedI32<{-50}, 100>, BoundedI32<10, 20>, BoundedI32<{-70}, 90>, sub);
        gen_test_fun!(e, BoundedI32<{-50}, 100>, BoundedI32<{-10}, 20>, BoundedI32<{-70}, 110>, sub);
        gen_test_fun!(f, BoundedI32<{-50}, 100>, BoundedI32<{-20}, {-10}>, BoundedI32<{-40}, 120>, sub);

        gen_test_fun!(g, BoundedI32<{-100}, {-50}>, BoundedI32<10, 20>, BoundedI32<{-120}, {-60}>, sub);
        gen_test_fun!(h, BoundedI32<{-100}, {-50}>, BoundedI32<{-10}, 20>, BoundedI32<{-120}, {-40}>, sub);
        gen_test_fun!(i, BoundedI32<{-100}, {-50}>, BoundedI32<{-20}, {-10}>, BoundedI32<{-90}, {-30}>, sub);
    }

    #[test]
    fn bounded_i32_mul_bounds_ok() {
        gen_test_fun!(a, BoundedI32<50, 100>, BoundedI32<10, 20>, BoundedI32<500, 2000>, mul);
        gen_test_fun!(b, BoundedI32<50, 100>, BoundedI32<{-10}, 20>, BoundedI32<{-1000}, 2000>, mul);
        gen_test_fun!(c, BoundedI32<50, 100>, BoundedI32<{-20}, {-10}>, BoundedI32<{-2000}, {-500}>, mul);

        gen_test_fun!(d, BoundedI32<{-50}, 100>, BoundedI32<10, 20>, BoundedI32<{-1000}, 2000>, mul);
        gen_test_fun!(e, BoundedI32<{-50}, 100>, BoundedI32<{-10}, 20>, BoundedI32<{-1000}, 2000>, mul);
        gen_test_fun!(f, BoundedI32<{-50}, 100>, BoundedI32<{-20}, {-10}>, BoundedI32<{-2000}, 1000>, mul);

        gen_test_fun!(g, BoundedI32<{-100}, {-50}>, BoundedI32<10, 20>, BoundedI32<{-2000}, {-500}>, mul);
        gen_test_fun!(h, BoundedI32<{-100}, {-50}>, BoundedI32<{-10}, 20>, BoundedI32<{-2000}, 1000>, mul);
        gen_test_fun!(i, BoundedI32<{-100}, {-50}>, BoundedI32<{-20}, {-10}>, BoundedI32<500, 2000>, mul);
    }
}
