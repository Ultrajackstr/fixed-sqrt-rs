//! Additional and re-exported traits

use fixed::types::extra::*;
use typenum::IsLess;

pub use integer_sqrt::IntegerSquareRoot;

pub trait LtU8   : LeEqU8   + IsLess <U8,   Output=True> {}
pub trait LtU16  : LeEqU16  + IsLess <U16,  Output=True> {}
pub trait LtU32  : LeEqU32  + IsLess <U32,  Output=True> {}
pub trait LtU64  : LeEqU64  + IsLess <U64,  Output=True> {}
pub trait LtU128 : LeEqU128 + IsLess <U128, Output=True> {}

impl <U> LtU8   for U where U : LeEqU8   + IsLess <U8,   Output=True> {}
impl <U> LtU16  for U where U : LeEqU16  + IsLess <U16,  Output=True> {}
impl <U> LtU32  for U where U : LeEqU32  + IsLess <U32,  Output=True> {}
impl <U> LtU64  for U where U : LeEqU64  + IsLess <U64,  Output=True> {}
impl <U> LtU128 for U where U : LeEqU128 + IsLess <U128, Output=True> {}
