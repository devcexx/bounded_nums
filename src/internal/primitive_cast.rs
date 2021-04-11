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

use paste::paste;

macro_rules! gen_cast_fun {
    ($from:ty, $into:ty, |$src:ident| $code:block) => {
        paste! {
            pub const fn [<cast_from_ $from _into_ $into>]($src: $from) -> Option<$into> {
            $code
            }
        }
    };
}

macro_rules! gen_infallible_casts {
    () => {
	gen_infallible_casts!(from_smaller: u8,   into_biggers: [u8, u16, u32, u64, u128, i16, i32, i64, i128]);
	gen_infallible_casts!(from_smaller: u16,  into_biggers: [u16, u32, u64, u128, i32, i64, i128]);
	gen_infallible_casts!(from_smaller: u32,  into_biggers: [u32, u64, u128, i64, i128]);
	gen_infallible_casts!(from_smaller: u64,  into_biggers: [u64, u128, i128]);
	gen_infallible_casts!(from_smaller: u128, into_bigger: u128);
	gen_infallible_casts!([i8, i16, i32, i64, i128]);
    };

    ([]) => {};

    ([$first:ty]) => {
	gen_infallible_casts!([$first,]);
    };

    ([$first:ty, $($next:ty),*]) => {
	// Same size implementation
	gen_infallible_casts!(from_smaller: $first,into_bigger:$first);

	// Implementation for bigger ($next) types.
	$(
	    gen_infallible_casts!(from_smaller: $first, into_bigger:$next);
	)*

	// Recursive expansion for doing the same with the remaining types.
	gen_infallible_casts!([$($next),*]);
    };

    (from_smaller: $from:ty, into_biggers: [$($into:ty),+]) => {
	$(
	    gen_infallible_casts!(from_smaller: $from, into_bigger: $into);
	)+
    };

    (from_smaller: $from:ty, into_bigger: $into:ty) => {
	gen_cast_fun!($from, $into, |src| {
	    Some(src as $into)
	});
    };
}

macro_rules! gen_same_sign_casts {
    () => {
	gen_same_sign_casts!([u128, u64, u32, u16, u8]);
	gen_same_sign_casts!([i128, i64, i32, i16, i8]);
    };

    ([]) => {};

    ([$first:ty]) => {
	gen_same_sign_casts!([$first,]);
    };

    ([$first:ty, $($next:ty),*]) => {
	// Same size implementation
	// Implementation for smaller ($next) types.
	$(
	    gen_same_sign_casts!(from_bigger: $first, into_smaller:$next);
	)*

	// Recursive expansion for doing the same with the remaining types.
	gen_same_sign_casts!([$($next),*]);
    };

    (from_bigger: $from:ty, into_smaller: $into:ty) => {
	gen_cast_fun!($from, $into, |src| {
	    if src > (<$into>::MAX as $from) || src < (<$into>::MIN as $from) {
		None
	    } else {
		Some(src as $into)
	    }
	});
    };
}

macro_rules! gen_from_smaller_signed {
    () => {
	gen_from_smaller_signed!(from_smaller: i8, into_biggers: [u8, u16, u32, u64, u128]);
	gen_from_smaller_signed!(from_smaller: i16, into_biggers: [u16, u32, u64, u128]);
	gen_from_smaller_signed!(from_smaller: i32, into_biggers: [u32, u64, u128]);
	gen_from_smaller_signed!(from_smaller: i64, into_biggers: [u64, u128]);
	gen_from_smaller_signed!(from_smaller: i128, into_biggers: [u128]);
    };

    (from_smaller: $from:ty, into_biggers: [$($into:ty),+]) => {
	$(
	    gen_from_smaller_signed!(from_smaller: $from, into_bigger: $into);
	)+
    };

    (from_smaller: $from:ty, into_bigger: $into:ty) => {
	gen_cast_fun!($from, $into, |src| {
	    if src < 0 {
		None
	    } else {
		Some(src as $into)
	    }
	});
    };
}

macro_rules! gen_from_bigger_unsigned {
    () => {
	gen_from_bigger_unsigned!(from_bigger: u8, into_smallers: [i8]);
	gen_from_bigger_unsigned!(from_bigger: u16, into_smallers: [i8, i16]);
	gen_from_bigger_unsigned!(from_bigger: u32, into_smallers: [i8, i16, i32]);
	gen_from_bigger_unsigned!(from_bigger: u64, into_smallers: [i8, i16, i32, i64]);
	gen_from_bigger_unsigned!(from_bigger: u128, into_smallers: [i8, i16, i32, i64, i128]);
    };

    (from_bigger: $from:ty, into_smallers: [$($into:ty),+]) => {
	$(
	    gen_from_bigger_unsigned!(from_bigger: $from, into_smaller: $into);
	)+
    };

    (from_bigger: $from:ty, into_smaller: $into:ty) => {
	gen_cast_fun!($from, $into, |src| {
	    if src > (<$into>::MAX as $from) {
		None
	    } else {
		Some(src as $into)
	    }
	});
    };
}

macro_rules! gen_from_bigger_signed {
    () => {
	gen_from_bigger_signed!(from_bigger: i16, into_smallers: [u8]);
	gen_from_bigger_signed!(from_bigger: i32, into_smallers: [u8, u16]);
	gen_from_bigger_signed!(from_bigger: i64, into_smallers: [u8, u16, u32]);
	gen_from_bigger_signed!(from_bigger: i128, into_smallers: [u8, u16, u32, u64]);
    };

    (from_bigger: $from:ty, into_smallers: [$($into:ty),+]) => {
	$(
	    gen_from_bigger_signed!(from_bigger: $from, into_smaller: $into);
	)+
    };

    (from_bigger: $from:ty, into_smaller: $into:ty) => {
	gen_cast_fun!($from, $into, |src| {
	    if src < 0 || src > (<$into>::MAX as $from) {
		None
	    } else {
		Some(src as $into)
	    }
	});
    };
}

gen_infallible_casts!();
gen_same_sign_casts!();
gen_from_smaller_signed!();
gen_from_bigger_unsigned!();
gen_from_bigger_signed!();
