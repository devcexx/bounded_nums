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

//! Module that contain internal types and methods that must be kept
//! public since they're exposed indirectly through the types defined
//! on this crate, but that shouldn't be directly used from outside
//1 it.

use super::*;
use std::marker::PhantomData;

mod primitive_cast;
use primitive_cast::*;

macro_rules! gen_internals {
    (@gen_fn_max $tnum:ty) => {
	paste::paste! {
	    #[doc="Returns the maximum of the given two [" $tnum "] numbers."]
	    pub const fn [< max_ $tnum >](a: $tnum, b: $tnum) -> $tnum {
		if a > b { a } else { b }
	    }
	}
    };

    (@gen_fn_min $tnum:ty) => {
	paste::paste! {
	    #[doc="Returns the minimum of the given two [" $tnum "] numbers."]
	    pub const fn [< min_ $tnum >](a: $tnum, b: $tnum) -> $tnum {
		if a < b { a } else { b }
	    }
	}
    };

    (@gen_fn_max4 $tnum:ty) => {
	paste::paste! {
	    #[doc="Returns the maximum of the given four [" $tnum "] numbers."]
	    pub const fn [< max4_ $tnum >](a: $tnum, b: $tnum, c:$tnum, d:$tnum) -> $tnum {
		[<max_ $tnum>]([<max_ $tnum>](a, b), [<max_ $tnum>](c, d))
	    }
	}
    };

    (@gen_fn_min4 $tnum:ty) => {
	paste::paste! {
	    #[doc="Returns the minimum of the given four [" $tnum "] numbers."]
	    pub const fn [< min4_ $tnum >](a: $tnum, b: $tnum, c:$tnum, d:$tnum) -> $tnum {
		[<min_ $tnum>]([<min_ $tnum>](a, b), [<min_ $tnum>](c, d))
	    }
	}
    };

    (@gen_where_expr2 $tnum:ty) => {
	paste::paste! {
	    #[doc="Mark that is used for adding const well-formed bounds inside a impl or a fn."]
	    #[doc="See <https://hackmd.io/OZG_XiLFRs2Xmw5s39jRzA?view>"]
	    pub struct [<WhereExpr2 $tnum:upper>]<const M: $tnum, const N: $tnum> {}
	}
    };

    (@gen_is_as_bounded_implemented $tnum:ty, $tright:ty) => {
        paste::paste! {
    	    #[doc = "Checks if [AsBounded" [<$tnum:upper>] "]<M, N> can be implemented by [Bounded" [<$tright:upper>] "]<M1, N1>."]
    	    #[doc = "This only will happen when M1 and N1 are in bounds of the primitive number type [" $tnum "] and the `[M1, N1]` is a range fully contained in `[M, N]`."]
    	    #[allow(unused_comparisons)]
	    pub const fn [< is_as_bounded_implemented_for_ $tnum _from_ $tright >](m: $tnum, n: $tnum, m1: $tright, n1: $tright) -> bool {
		let m1_casted = [<cast_from_ $tright _into_ $tnum>](m1);
		let n1_casted = [<cast_from_ $tright _into_ $tnum>](n1);

		match (m1_casted, n1_casted) {
		    (Some(m1), Some(n1)) => m <= m1 && n1 <= n,
		    _ => false
		}
            }
	}
    };

    (@gen_is_as_bounded_implemented_all $tnum:ty, [$($tright:ty)+]) => {
	$(
	    gen_internals!(@gen_is_as_bounded_implemented $tnum, $tright);
	)+
    };


    ([$($tnum:ty)+]) => {
	$(
	    gen_internals!($tnum);
	)+
    };

    ($tnum:ty) => {
	gen_internals!(@gen_fn_max $tnum);
	gen_internals!(@gen_fn_min $tnum);
	gen_internals!(@gen_fn_max4 $tnum);
	gen_internals!(@gen_fn_min4 $tnum);
	gen_internals!(@gen_where_expr2 $tnum);
	gen_internals!(@gen_is_as_bounded_implemented_all $tnum, [u8 u16 u32 u64 u128 i8 i16 i32 i64 i128]);
    };
}

/// Trait that marks a type-level boolean expression that
/// evaluates to true.
pub trait IsTrue {}

/// Represents a type-level boolean expression whose result is
/// defined by a const generic boolean expression.
pub enum E<const E: bool> {}
impl IsTrue for E<true> {}

/// Represents a type-level AND operation between two type-level
/// boolean expressions. It only evaluates (implements [IsTrue]),
/// when both expressions also implements [IsTrue].
pub struct And<L, R> {
    _mark: PhantomData<(L, R)>,
}

impl<L, R> IsTrue for And<L, R>
where
    L: IsTrue,
    R: IsTrue,
{
}

gen_internals!([u8 u16 u32 u64 u128 i8 i16 i32 i64 i128]);
