// Copyright 2020 Parity Technologies
//
// Licensed under the Apache License, Version 2.0 <LICENSE-APACHE or
// http://www.apache.org/licenses/LICENSE-2.0> or the MIT license
// <LICENSE-MIT or http://opensource.org/licenses/MIT>, at your
// option. This file may not be copied, modified, or distributed
// except according to those terms.

//! Efficient large, fixed-size big integers and hashes.


#[doc(hidden)]
pub use byteorder;


#[doc(hidden)]
pub use rustc_hex;


#[doc(hidden)]
pub use rand;


#[doc(hidden)]
pub use static_assertions;

#[doc(hidden)]
pub use crunchy::unroll;

#[doc(hidden)]
pub use uint::macros::*;

#[macro_use]
#[rustfmt::skip]
mod uint;
pub use crate::uint::*;

mod ff;
pub use ff::*;

