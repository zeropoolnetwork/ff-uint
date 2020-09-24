#[doc(hidden)] pub use byteorder;
#[doc(hidden)] pub use rustc_hex;
#[doc(hidden)] pub use rand;
#[doc(hidden)] pub use static_assertions;
#[doc(hidden)] pub use crunchy::unroll;
#[doc(hidden)] pub use concat_idents::concat_idents;
#[doc(hidden)] pub use borsh;
#[doc(hidden)] pub use serde;


#[macro_use] mod uint;
#[macro_use] mod ff;
//mod num;

pub use uint::traits::*;
pub use uint::macros::*;
pub use ff::*;
pub use ff::traits::*;
//pub use num::*;


use std::ops::{Add, AddAssign, Sub, SubAssign, Mul, MulAssign, Div, DivAssign, Rem, RemAssign, Neg, Shr, ShrAssign, Shl, ShlAssign, BitOr, BitOrAssign, BitAnd, BitAndAssign, BitXor, BitXorAssign, Not};
use std::cmp::{PartialEq, Eq, PartialOrd, Ord};

pub trait ArithNoAssign: Sized +
    Add<Self, Output=Self> +
    for<'a> Add<&'a Self, Output=Self> +
    Sub<Self, Output=Self> +
    for<'a> Sub<Self, Output=Self> +
    Mul<Self, Output=Self> +
    for<'a> Mul<&'a Self, Output=Self> +
    Div<Self, Output=Self> +
    Neg<Output=Self>
{}

pub trait ArithNoAssignEx: ArithNoAssign +
    Rem<Self, Output=Self> +
    for<'a> Rem<&'a Self, Output=Self> +
    Shl<u32, Output=Self> +
    for<'a> Shl<&'a u32, Output=Self> +
    Shr<u32, Output=Self> +
    for<'a> Shr<&'a u32, Output=Self>
{}


pub trait Arith: 
    ArithNoAssign +
    AddAssign<Self> +
    for<'a> AddAssign<&'a Self> +
    SubAssign<Self> +
    for<'a> SubAssign<&'a Self> +
    MulAssign<Self> +
    for<'a> MulAssign<&'a Self> +
    DivAssign<Self> +
    for<'a> DivAssign<&'a Self> +
    PartialEq +
    Eq +
    where for<'a> &'a Self : ArithNoAssign
{}

pub trait ArithEx: Arith + ArithNoAssignEx +
    RemAssign<Self> +
    for<'a> RemAssign<&'a Self>  +
    ShlAssign<u32> +
    for<'a> ShlAssign<&'a u32> +
    ShrAssign<u32> +
    for<'a> ShrAssign<&'a u32> +
    PartialOrd + 
    Ord 
    where for <'a> &'a Self: ArithNoAssignEx
{} 


pub trait BitLogicNoAssign: Sized +
    Not<Output=Self> +
    BitOr<Self, Output=Self> +
    for<'a> BitOr<&'a Self, Output=Self> +
    BitAnd<Self, Output=Self> +
    for<'a> BitAnd<&'a Self, Output=Self> +
    BitXor<Self, Output=Self> +
    for<'a> BitXor<&'a Self, Output=Self>
{}

pub trait BitLogic: BitLogicNoAssign +
    BitOrAssign<Self> +
    for<'a> BitOrAssign<&'a Self> +
    BitAndAssign<Self> +
    for<'a> BitAndAssign<&'a Self> +
    BitXorAssign<Self> +
    for<'a> BitXorAssign<&'a Self> +
    PartialEq +
    Eq +
    where for<'a> &'a Self: BitLogicNoAssign
{}