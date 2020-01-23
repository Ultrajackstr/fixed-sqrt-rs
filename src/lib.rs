//! Square root trait for fixed-point numbers using integer square root
//! algorithm.
//!
//! This functionality is split into two traits: `FixedSqrtEven` (re-exported as
//! `FixedSqrt`) and `FixedSqrtOdd`. This is because the square root algorithm
//! needs to be specialized for an odd number of fractional bits (represented as
//! a `typenum` parameter), and generic trait impls don't allow this kind of
//! specialization based on mutually exclusive traits.
//!
//! Computing the square root with an odd number of fractional bits requires one
//! extra bit to shift into before performing the square root. Since square root
//! is defined only for positive numbers, this can be done for all *signed*
//! fixed-point numbers (up to and including `FixedI128`) utilizing the sign bit
//! for the overflow.
//!
//! For unsigned fixed-point numbers, if an extra bit is needed (i.e. if the
//! MSB is 1), this requires a static cast to the next larger primitive integer
//! type before computing the square root. As a result, the square root trait
//! is *not* implemented for `FixedU128` with an odd number fractional bits
//! since that would require a square root algorithm for 256-bit integers which
//! isn't provided by the `integer-sqrt` library.
//!
//!
//! # Accuracy
//!
//! TODO
//!
//! # Panics
//!
//! TODO

#[allow(unused_macros)]
macro_rules! show {
  ($e:expr) => { println!("{}: {:?}", stringify!($e), $e); }
}

#[allow(unused_macros)]
macro_rules! bits8 {
  ($e:expr) => { println!("{}: {:08b}", stringify!($e), $e); }
}

use std::ops::{Rem, Shl};
use fixed::{FixedI8, FixedI16, FixedI32, FixedI64, FixedU8, FixedU16,
  FixedU32, FixedU64, FixedI128, FixedU128};
use fixed::traits::Fixed;
use fixed::types::extra::*;
use integer_sqrt::IntegerSquareRoot;

pub use FixedSqrtEven as FixedSqrt;

pub trait FixedSqrtEven : Fixed where
  Self::Bits : Shl <isize, Output=Self::Bits> + IntegerSquareRoot
{
  fn sqrt (self) -> Self;
}

pub trait FixedSqrtOdd : Fixed where
  Self::Bits : Shl <isize, Output=Self::Bits> + IntegerSquareRoot
{
  fn sqrt (self) -> Self;
}

macro_rules! impl_sqrt_unsigned_even {
  ($unsigned:ident, $leq:ident) => {
    impl <U> FixedSqrtEven for $unsigned <U> where
      U : Unsigned + $leq + Rem <U2>,
      typenum::Mod <U, U2> : typenum::Same <U0>
    {
      fn sqrt (self) -> Self {
        $unsigned::from_bits (
          self.to_bits().integer_sqrt() <<
            (<$unsigned <U> as Fixed>::Frac::ISIZE/2)
        )
      }
    }
  }
}

macro_rules! impl_sqrt_unsigned_odd {
  ($unsigned:ident, $leq:ident, $higher:ty) => {
    impl <U> FixedSqrtOdd for $unsigned <U> where
      U : Unsigned + $leq + Rem <U2>,
      typenum::Mod <U, U2> : typenum::Same <U1>
    {
      fn sqrt (self) -> Self {
        let bits = self.to_bits();
        let sqrt = if
          bits & (1 as <$unsigned <U> as Fixed>::Bits).rotate_right (1) > 0
        {
          let bits = bits as $higher << 1;
          let sqrt =
            bits.integer_sqrt() << (<$unsigned <U> as Fixed>::Frac::ISIZE/2);
          // square root should be within max value
          debug_assert!(sqrt <= <$unsigned <U> as Fixed>::Bits::max_value()
            as $higher);
          sqrt as <$unsigned <U> as Fixed>::Bits
        } else {
          let bits = bits << 1;
          bits.integer_sqrt() << (<$unsigned <U> as Fixed>::Frac::ISIZE/2)
        };
        $unsigned::from_bits (sqrt)
      }
    }
  }
}

impl_sqrt_unsigned_even!(FixedU8,   LeEqU8);
impl_sqrt_unsigned_even!(FixedU16,  LeEqU16);
impl_sqrt_unsigned_even!(FixedU32,  LeEqU32);
impl_sqrt_unsigned_even!(FixedU64,  LeEqU64);
impl_sqrt_unsigned_even!(FixedU128, LeEqU128);
impl_sqrt_unsigned_odd!(FixedU8,   LeEqU8,  u16);
impl_sqrt_unsigned_odd!(FixedU16,  LeEqU16, u32);
impl_sqrt_unsigned_odd!(FixedU32,  LeEqU32, u64);
impl_sqrt_unsigned_odd!(FixedU64,  LeEqU64, u128);

macro_rules! impl_sqrt_signed_even {
  ($signed:ident, $leq:ident) => {
    impl <U> FixedSqrtEven for $signed <U> where
      U : Unsigned + $leq + Rem <U2>,
      typenum::Mod <U, U2> : typenum::Same <U0>
    {
      fn sqrt (self) -> Self {
        if self.is_negative() {
          panic!("fixed point square root of a negative number");
        }
        let n = $signed::from_bits(
          self.to_bits().integer_sqrt() <<
            (<$signed <U> as Fixed>::Frac::ISIZE/2)
        );
        if n.is_negative() {
          panic!("fixed point square root out of range");
        } else {
          n
        }
      }
    }
  }
}

macro_rules! impl_sqrt_signed_odd {
  ($signed:ident, $leq:ident, $unsigned:ty) => {
    impl <U> FixedSqrtOdd for $signed <U> where
      U : Unsigned + $leq + Rem <U2>,
      typenum::Mod <U, U2> : typenum::Same <U1>
    {
      fn sqrt (self) -> Self {
        if self.is_negative() {
          panic!("fixed point square root of a negative number");
        }
        // because the msb of a non-negative number is zero, it is always
        // safe to shift, but we need to compute the square root on the unsigned
        // integer type
        debug_assert_eq!(
          self.to_bits() & (1 as <$signed <U> as Fixed>::Bits).rotate_right (1),
          0x0);
        let bits = (self.to_bits() << 1) as $unsigned;
        let sqrt =
          bits.integer_sqrt() << (<$signed <U> as Fixed>::Frac::ISIZE/2);
        let n = $signed::from_bits (sqrt as <$signed <U> as Fixed>::Bits);
        if n.is_negative() {
          panic!("fixed point square root out of range");
        } else {
          n
        }
      }
    }
  }
}

impl_sqrt_signed_even!(FixedI8,   LeEqU8);
impl_sqrt_signed_even!(FixedI16,  LeEqU16);
impl_sqrt_signed_even!(FixedI32,  LeEqU32);
impl_sqrt_signed_even!(FixedI64,  LeEqU64);
impl_sqrt_signed_even!(FixedI128, LeEqU128);
impl_sqrt_signed_odd!(FixedI8,   LeEqU8,   u8);
impl_sqrt_signed_odd!(FixedI16,  LeEqU16,  u16);
impl_sqrt_signed_odd!(FixedI32,  LeEqU32,  u32);
impl_sqrt_signed_odd!(FixedI64,  LeEqU64,  u64);
impl_sqrt_signed_odd!(FixedI128, LeEqU128, u128);

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
              let err = (h_f64.sqrt() - h_sqrt.to_num::<f64>()).abs();
              if err > $maxerr {
                let ftype = format!("{}<U{}>", stringify!($fixed), U::ISIZE);
                show!((ftype, h, h_sqrt, err));
                //assert!(err <= $maxerr);
              }
            }
            if let Some (l) = $fixed::<U>::checked_from_num(l_f64) {
              let l_sqrt = l.sqrt();
              let err = (l_f64.sqrt() - l_sqrt.to_num::<f64>()).abs();
              if err > $maxerr {
                let ftype = format!("{}<U{}>", stringify!($fixed), U::ISIZE);
                show!((ftype, l, l_sqrt, err));
                //assert!(err <= $maxerr);
              }
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

    //test_sqrt_unsigned!(test_sqrt_u128, FixedU128, U128, 8.0);
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
              let h_sqrt = h.sqrt();
              let err = h_f64.sqrt() - h_sqrt.to_num::<f64>();
              if err > $maxerr {
                let ftype = format!("{}<U{}>", stringify!($fixed), U::ISIZE);
                show!((ftype, h, h_sqrt, err));
                assert!(err <= $maxerr);
              }
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
              let l_sqrt = l.sqrt();
              let err = l_f64.sqrt() - l_sqrt.to_num::<f64>();
              if err > $maxerr {
                let ftype = format!("{}<U{}>", stringify!($fixed), U::ISIZE);
                show!((ftype, l, l_sqrt, err));
                assert!(err <= $maxerr);
              }
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

    //test_sqrt_signed!(test_sqrt_i128, FixedI128, U128, 8.0);
    test_sqrt_signed!(test_sqrt_i64,  FixedI64,  U64,  1.0);
    test_sqrt_signed!(test_sqrt_i32,  FixedI32,  U32,  1.0);
    test_sqrt_signed!(test_sqrt_i16,  FixedI16,  U16,  1.0);
    test_sqrt_signed!(test_sqrt_i8,   FixedI8,   U8,   1.0);
  }

  #[test]
  #[should_panic]
  fn test_sqrt_negative() {
    I16F16::from_num (-1.0).sqrt();
  }

  #[test]
  #[should_panic]
  fn test_sqrt_out_of_bounds() {
    I0F32::from_num (0.3).sqrt();
  }

  #[test]
  fn test_sqrt_unsigned_exhaustive() {
    macro_rules! test_unsigned_exhaustive {
      ($unsigned:ident, $maxerr:expr) => {
        let mut i = $unsigned::from_bits (0);
        loop {
          let err = (i.to_num::<f64>().sqrt() - i.sqrt().to_num::<f64>()).abs();
          if err >= $maxerr {
            show!((stringify!($unsigned), i, i.sqrt(), err));
            assert!(err < $maxerr);
          }
          if i == $unsigned::max_value() {
            break
          }
          i += $unsigned::from_bits (1);
        }
      }
    }
    test_unsigned_exhaustive!(U8F0, 1.0);
    test_unsigned_exhaustive!(U7F1, 8.0);
    test_unsigned_exhaustive!(U6F2, 1.0);
    test_unsigned_exhaustive!(U5F3, 8.0);
    test_unsigned_exhaustive!(U4F4, 1.0);
    test_unsigned_exhaustive!(U3F5, 8.0);
    test_unsigned_exhaustive!(U2F6, 1.0);
    test_unsigned_exhaustive!(U1F7, 1.0);
    test_unsigned_exhaustive!(U0F8, 1.0);
  }


  #[test]
  fn test_sqrt_exact() {
    /*FIXME:debug*/
    let mut x = U7F1::from_bits (0);
    show!(x);
    bits8!(x.to_bits());
    x += U7F1::from_bits (1);
    show!(x);
    bits8!(x.to_bits());
    x += U7F1::from_bits (1);
    show!(x);
    bits8!(x.to_bits());
    x += U7F1::from_bits (1);
    show!(x);
    bits8!(x.to_bits());
    fn exact8 <F : FixedSqrt> () where
      F::Bits : Shl <isize, Output=F::Bits> + IntegerSquareRoot + std::fmt::Debug
        + std::fmt::Binary
    {
      show!(F::Frac::USIZE);
      show!(F::min_value());
      show!(F::max_value());
      for i in 0.. {
        let sq = i * i;
        show!(i);
        show!(sq);
        if sq >= 256 {
          break
        }
        if let Some (x) = F::checked_from_num (sq as f64) {
          show!(x);
          show!(F::from_num (i));
          show!(x.sqrt());
          show!(x.to_bits());
          bits8!(x.to_bits());
          bits8!(F::from_num (i).to_bits());
          bits8!(x.sqrt().to_bits());
          assert_eq!(x.sqrt(), F::from_num (i));
        }
      }
    }
    exact8::<U8F0>();
    exact8::<U7F1>();
    exact8::<U6F2>();
    exact8::<U5F3>();
    exact8::<U4F4>();
    exact8::<U3F5>();
    exact8::<U2F6>();
    exact8::<U1F7>();
    exact8::<U0F8>();
  }

}
