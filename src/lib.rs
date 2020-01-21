//! Square root trait for fixed-point numbers using integer square root
//! algorithm

use std::ops::Shl;
use fixed::{FixedI8, FixedI16, FixedI32, FixedI64, FixedI128, FixedU8, FixedU16,
  FixedU32, FixedU64, FixedU128};
use fixed::traits::Fixed;
use fixed::types::extra::{LeEqU8, LeEqU16, LeEqU32, LeEqU64, LeEqU128,
  Unsigned};
use integer_sqrt::IntegerSquareRoot;

pub trait FixedSqrt : Fixed where
  Self::Bits : Shl <isize, Output=Self::Bits> + IntegerSquareRoot
{
  fn sqrt (self) -> Self;
}

macro_rules! impl_sqrt_unsigned {
  ($signed:ident, $leq:ident) => {
    impl <U> FixedSqrt for $signed <U> where U : Unsigned + $leq {
      fn sqrt (self) -> Self {
        $signed::from_bits(self.to_bits().integer_sqrt() <<
          (<$signed <U> as Fixed>::Frac::ISIZE/2 +
           <$signed <U> as Fixed>::Frac::ISIZE%2))
      }
    }
  }
}

impl_sqrt_unsigned!(FixedU8,   LeEqU8);
impl_sqrt_unsigned!(FixedU16,  LeEqU16);
impl_sqrt_unsigned!(FixedU32,  LeEqU32);
impl_sqrt_unsigned!(FixedU64,  LeEqU64);
impl_sqrt_unsigned!(FixedU128, LeEqU128);

macro_rules! impl_sqrt_signed {
  ($signed:ident, $leq:ident) => {
    impl <U> FixedSqrt for $signed <U> where U : Unsigned + $leq {
      fn sqrt (self) -> Self {
        if self.is_negative() {
          panic!("fixed point square root of a negative number");
        }
        let n = $signed::from_bits(self.to_bits().integer_sqrt() <<
          (<$signed <U> as Fixed>::Frac::ISIZE/2 +
           <$signed <U> as Fixed>::Frac::ISIZE%2));
        if n.is_negative() {
          panic!("fixed point square root out of range");
        } else {
          n
        }
      }
    }
  }
}

impl_sqrt_signed!(FixedI8,   LeEqU8);
impl_sqrt_signed!(FixedI16,  LeEqU16);
impl_sqrt_signed!(FixedI32,  LeEqU32);
impl_sqrt_signed!(FixedI64,  LeEqU64);
impl_sqrt_signed!(FixedI128, LeEqU128);

#[cfg(test)]
mod tests {
  use super::*;
  use fixed::types::*;
  use fixed::types::extra::*;
  use typenum::Sub1;

  #[test]
  fn test_sqrt() {
    let x = I16F16::from_num (2);
    assert_eq!(x.sqrt(), I16F16::from_num (1.41406));

    macro_rules! test_sqrt_unsigned {
      ($fun:ident, $fixed:ident, $unsigned:ident, $maxerr:expr) => {
        fn $fun<U>(base: f64, range: i32)
          where U: Unsigned + IsLessOrEqual<$unsigned, Output = True>
        {
          for i in 0..range {
            let h_f64 = base.powi(i);
            let l_f64 = base.powi(-i);
            if let Some (h) = $fixed::<U>::checked_from_num(h_f64) {
              let h_sqrt = h.sqrt();
              assert!(h_f64.sqrt() - h_sqrt.to_num::<f64>() <= $maxerr);
            }
            if let Some (l) = $fixed::<U>::checked_from_num(l_f64) {
              let l_sqrt = l.sqrt();
              assert!(l_f64.sqrt() - l_sqrt.to_num::<f64>() <= $maxerr);
            }
          }
        }
        eprintln!("testing {}", stringify!($fun));

        $fun::<U0>(0.5, $unsigned::I32);
        $fun::<U0>(2.0, $unsigned::I32);
        $fun::<U0>(2.5, $unsigned::I32/2);
        $fun::<U0>(3.0, $unsigned::I32/2);
        $fun::<U0>(5.0, $unsigned::I32/2);

        $fun::<U1>(0.5, $unsigned::I32);
        $fun::<U1>(2.0, $unsigned::I32);
        $fun::<U1>(2.5, $unsigned::I32/2);
        $fun::<U1>(3.0, $unsigned::I32/2);
        $fun::<U1>(5.0, $unsigned::I32/2);

        $fun::<U2>(0.5, $unsigned::I32);
        $fun::<U2>(2.0, $unsigned::I32);
        $fun::<U2>(2.5, $unsigned::I32/2);
        $fun::<U2>(3.0, $unsigned::I32/2);
        $fun::<U2>(5.0, $unsigned::I32/2);

        $fun::<Sub1<Sub1<$unsigned>>>(0.5, $unsigned::I32);
        $fun::<Sub1<Sub1<$unsigned>>>(2.0, $unsigned::I32);
        $fun::<Sub1<Sub1<$unsigned>>>(2.5, $unsigned::I32/2);
        $fun::<Sub1<Sub1<$unsigned>>>(3.0, $unsigned::I32/2);
        $fun::<Sub1<Sub1<$unsigned>>>(5.0, $unsigned::I32/2);

        $fun::<Sub1<$unsigned>>(0.5, $unsigned::I32);
        $fun::<Sub1<$unsigned>>(2.0, $unsigned::I32);
        $fun::<Sub1<$unsigned>>(2.5, $unsigned::I32/2);
        $fun::<Sub1<$unsigned>>(3.0, $unsigned::I32/2);
        $fun::<Sub1<$unsigned>>(5.0, $unsigned::I32/2);

        $fun::<$unsigned>(0.5, $unsigned::I32);
        $fun::<$unsigned>(2.0, $unsigned::I32);
        $fun::<$unsigned>(2.5, $unsigned::I32/2);
        $fun::<$unsigned>(3.0, $unsigned::I32/2);
        $fun::<$unsigned>(5.0, $unsigned::I32/2);
      }
    }

    test_sqrt_unsigned!(test_sqrt_u128, FixedU128, U128, 8.0);
    test_sqrt_unsigned!(test_sqrt_u64,  FixedU64,  U64,  1.0);
    test_sqrt_unsigned!(test_sqrt_u32,  FixedU32,  U32,  1.0);
    test_sqrt_unsigned!(test_sqrt_u16,  FixedU16,  U16,  1.0);
    test_sqrt_unsigned!(test_sqrt_u8,   FixedU8,   U8,   1.0);

    macro_rules! test_sqrt_signed {
      ($fun:ident, $fixed:ident, $unsigned:ident, $maxerr:expr) => {
        fn $fun<U>(base: f64, range: i32)
          where U : Unsigned + IsLessOrEqual<$unsigned, Output = True>
        {
          for i in 0..range {
            let h_f64 = base.powi(i);
            let l_f64 = base.powi(-i);
            if let Some (h) = $fixed::<U>::checked_from_num(h_f64) {
              // skip out of range
              if $fixed::<U>::checked_from_num(h_f64.sqrt()).is_none() {
                continue
              }
              // skip out of domain
              if U::ISIZE == $unsigned::ISIZE-1 && h_f64 >= 0.5 {
                continue
              }
              assert!(h_f64.sqrt() - h.sqrt().to_num::<f64>() <= $maxerr);
            }
            if let Some (l) = $fixed::<U>::checked_from_num(l_f64) {
              // skip out of range
              if $fixed::<U>::checked_from_num(l_f64.sqrt()).is_none() {
                continue
              }
              // skip out of domain
              if U::ISIZE == $unsigned::ISIZE-1 && l_f64 >= 0.5 {
                continue
              }
              assert!(l_f64.sqrt() - l.sqrt().to_num::<f64>() <= $maxerr);
            }
          }
        }

        eprintln!("testing {}", stringify!($fun));

        $fun::<U0>(0.5, $unsigned::I32);
        $fun::<U0>(2.0, $unsigned::I32);
        $fun::<U0>(2.5, $unsigned::I32/2);
        $fun::<U0>(3.0, $unsigned::I32/2);
        $fun::<U0>(5.0, $unsigned::I32/2);

        $fun::<U1>(0.5, $unsigned::I32);
        $fun::<U1>(2.0, $unsigned::I32);
        $fun::<U1>(2.5, $unsigned::I32/2);
        $fun::<U1>(3.0, $unsigned::I32/2);
        $fun::<U1>(5.0, $unsigned::I32/2);

        $fun::<U2>(0.5, $unsigned::I32);
        $fun::<U2>(2.0, $unsigned::I32);
        $fun::<U2>(2.5, $unsigned::I32/2);
        $fun::<U2>(3.0, $unsigned::I32/2);
        $fun::<U2>(5.0, $unsigned::I32/2);

        $fun::<Sub1<Sub1<$unsigned>>>(0.5, $unsigned::I32);
        $fun::<Sub1<Sub1<$unsigned>>>(2.0, $unsigned::I32);
        $fun::<Sub1<Sub1<$unsigned>>>(2.5, $unsigned::I32/2);
        $fun::<Sub1<Sub1<$unsigned>>>(3.0, $unsigned::I32/2);
        $fun::<Sub1<Sub1<$unsigned>>>(5.0, $unsigned::I32/2);

        $fun::<Sub1<$unsigned>>(0.5, $unsigned::I32);
        $fun::<Sub1<$unsigned>>(2.0, $unsigned::I32);
        $fun::<Sub1<$unsigned>>(2.5, $unsigned::I32/2);
        $fun::<Sub1<$unsigned>>(3.0, $unsigned::I32/2);
        $fun::<Sub1<$unsigned>>(5.0, $unsigned::I32/2);

        $fun::<$unsigned>(0.5, $unsigned::I32);
        $fun::<$unsigned>(2.0, $unsigned::I32);
        $fun::<$unsigned>(2.5, $unsigned::I32/2);
        $fun::<$unsigned>(3.0, $unsigned::I32/2);
        $fun::<$unsigned>(5.0, $unsigned::I32/2);
      }
    }

    test_sqrt_signed!(test_sqrt_i128, FixedI128, U128, 8.0);
    test_sqrt_signed!(test_sqrt_i64,  FixedI64,  U64,  1.0);
    test_sqrt_signed!(test_sqrt_i32,  FixedI32,  U32,  1.0);
    test_sqrt_signed!(test_sqrt_i16,  FixedI16,  U16,  1.0);
    test_sqrt_signed!(test_sqrt_i8,   FixedI8,   U8,   1.0);
  }

}
