//! Square root trait for [fixed-point numbers](https://docs.rs/fixed) using
//! [integer square root](https://docs.rs/integer-sqrt) algorithm.
//!
//! [Repository](https://gitlab.com/spearman/fixed-sqrt-rs)
//!
//! # Implementation
//!
//! **Even fractional bits**
//!
//! `FixedSqrt` is implemented for all *unsigned* fixed-point types with an
//! *even* number of bits.
//!
//! `FixedSqrt` is implemented for all *signed* fixed-point types with an even
//! number of fractional bits, *except* for the case of *zero integer* bits
//! (i.e. fractional bits equal to the total bit size of the type). This is
//! because the range for these types is *[-0.5, 0.5)*, and square roots of
//! numbers in the range *[0.25, 0.5)* will be *>= 0.5*, outside of the range of
//! representable values for that type.
//!
//! **Odd fractional bits**
//!
//! Computing the square root with an *odd* number of fractional bits requires
//! one extra bit to shift before performing the square root.
//!
//! In the case of *signed* fixed-point numbers, since square root is defined
//! only for positive input values, all signed fixed-point numbers (up to and
//! including `FixedI128`) can compute the square root *in-place* utilizing the
//! sign bit for the overflow.
//!
//! For *unsigned* fixed-point numbers with odd fractional bits, if an extra bit
//! is needed (i.e. if the most significant bit is 1), this requires a scalar
//! cast to the next larger unsigned primitive type before computing the square
//! root. As a result, the square root trait is *not* implemented for
//! `FixedU128` types with an odd number fractional bits since that would
//! require 256-bit unsigned integers, or else the domain would have to be
//! restricted to the lower half of u128 values.
//!
//! # Accuracy
//!
//! The `errors` example can be run to see exhaustive error stats for 8-bit and
//! 16-bit fixed-point types. The worst-case absolute error is shown to occur at
//! the largest values, where the percentage error is small, and the worst-case
//! percentage error occurs at the smallest values where the absolute error is
//! small.
//!
//! CSV files suitable for graphing with gnuplot can also be generated by
//! running the `errors` example with the `-p` flag.
//!
//! # Panics
//!
//! - Panics if called on a negative signed number

#[allow(unused_macros)]
macro_rules! show {
  ($e:expr) => { println!("{}: {:?}", stringify!($e), $e); }
}

#[allow(unused_macros)]
macro_rules! bits8 {
  ($e:expr) => { println!("{}: {:08b}", stringify!($e), $e); }
}

#[allow(unused_macros)]
macro_rules! bits64 {
  ($e:expr) => { println!("{}: {:064b}", stringify!($e), $e); }
}

use fixed::{FixedI8, FixedI16, FixedI32, FixedI64, FixedU8, FixedU16, FixedU32,
  FixedU64, FixedI128, FixedU128};
use fixed::traits::Fixed;
use fixed::types::extra::*;
use integer_sqrt::IntegerSquareRoot;
use typenum::{UInt, UTerm};
use typenum::bit::{B0, B1};

pub mod traits;

use self::traits::*;

/// Square root algorithm for fixed-point numbers
pub trait FixedSqrt : Fixed {
  fn sqrt (self) -> Self;
}

////////////////////////////////////////////////////////////////////////////////
//  unsigned
////////////////////////////////////////////////////////////////////////////////

macro_rules! impl_sqrt_unsigned_even {
  ($unsigned:ident, $lt:ident) => {
    impl FixedSqrt for $unsigned <UTerm> {
      fn sqrt (self) -> Self {
        $unsigned::from_bits (
          self.to_bits().integer_sqrt() <<
            (<$unsigned <UTerm> as Fixed>::Frac::USIZE/2)
        )
      }
    }
    impl <U> FixedSqrt for $unsigned <UInt <U, B0>> where
      UInt <U, B0> : $lt
    {
      fn sqrt (self) -> Self {
        $unsigned::from_bits (
          self.to_bits().integer_sqrt() <<
            (<$unsigned <UInt <U, B0>> as Fixed>::Frac::USIZE/2)
        )
      }
    }
  }
}

macro_rules! impl_sqrt_unsigned_odd {
  ($unsigned:ident, $leq:ident, $higher:ty) => {
    impl <U> FixedSqrt for $unsigned <UInt <U, B1>> where
      UInt <U, B1> : $leq
    {
      fn sqrt (self) -> Self {
        let bits = self.to_bits();
        let sqrt = if
          bits & (1 as <$unsigned <UInt <U, B1>> as Fixed>::Bits).rotate_right (1) > 0
        {
          // NOTE: we compute on the unsigned integer type of the larger size
          let bits = bits as $higher << 1;
          let sqrt = bits.integer_sqrt() << (<$unsigned <UInt <U, B1>>
            as Fixed>::Frac::USIZE/2);
          // square root should be within max value
          debug_assert!(sqrt <=
            <$unsigned <UInt <U, B1>> as Fixed>::Bits::MAX as $higher);
          sqrt as <$unsigned <UInt <U, B1>> as Fixed>::Bits
        } else {
          let bits = bits << 1;
          bits.integer_sqrt() << (<$unsigned <UInt <U, B1>> as Fixed>::Frac::USIZE/2)
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
impl_sqrt_unsigned_odd!(FixedU8,   LeEqU8,   u16);
impl_sqrt_unsigned_odd!(FixedU16,  LeEqU16,  u32);
impl_sqrt_unsigned_odd!(FixedU32,  LeEqU32,  u64);
impl_sqrt_unsigned_odd!(FixedU64,  LeEqU64,  u128);
//impl_sqrt_unsigned_odd!(FixedU128, LeEqU128, u256);   // unimplemented

////////////////////////////////////////////////////////////////////////////////
//  signed
////////////////////////////////////////////////////////////////////////////////

macro_rules! impl_sqrt_signed_even {
  ($signed:ident, $lt:ident, $unsigned:ty) => {
    impl FixedSqrt for $signed <UTerm> {
      fn sqrt (self) -> Self {
        if self.is_negative() {
          panic!("fixed point square root of a negative number");
        }
        // NOTE: as of integer-sqrt v0.1.2 there seems to be a bug when
        // computing sqrt using signed 32bit and 128bit integers, we can just
        // use unsigned integers instead
        let bits = self.to_bits() as $unsigned;
        let sqrt = bits.integer_sqrt() <<
          (<$signed <UTerm> as Fixed>::Frac::USIZE/2);
        let n = $signed::from_bits (sqrt as <$signed <UTerm> as Fixed>::Bits);
        // NOTE: by excluding the case with zero integer bits, this assertion
        // should never fail
        debug_assert!(n.count_ones() == 0 || n.is_positive());
        n
      }
    }

    impl <U> FixedSqrt for $signed <UInt <U, B0>> where
      UInt <U, B0> : $lt
    {
      fn sqrt (self) -> Self {
        if self.is_negative() {
          panic!("fixed point square root of a negative number");
        }
        // NOTE: as of integer-sqrt v0.1.2 there seems to be a bug when
        // computing sqrt using signed 32bit and 128bit integers, we can just
        // use unsigned integers instead
        let bits = self.to_bits() as $unsigned;
        let sqrt = bits.integer_sqrt() <<
          (<$signed <UInt <U, B0>> as Fixed>::Frac::USIZE/2);
        let n = $signed::from_bits (sqrt
          as <$signed <UInt <U, B0>> as Fixed>::Bits);
        // NOTE: by excluding the case with zero integer bits, this assertion
        // should never fail
        debug_assert!(n.count_ones() == 0 || n.is_positive());
        n
      }
    }
  }
}

macro_rules! impl_sqrt_signed_odd {
  ($signed:ident, $leq:ident, $unsigned:ty) => {
    impl <U> FixedSqrt for $signed <UInt <U, B1>> where
      UInt <U, B1> : $leq
    {
      fn sqrt (self) -> Self {
        if self.is_negative() {
          panic!("fixed point square root of a negative number");
        }
        // because the msb of a non-negative number is zero, it is always
        // safe to shift, but we need to compute the square root on the unsigned
        // integer type
        debug_assert_eq!(
          self.to_bits() &
            (1 as <$signed <UInt <U, B1>> as Fixed>::Bits).rotate_right (1),
          0x0);
        // NOTE: we compute on the unsigned integer type of the same size since
        // the sign bit is zero we can shift into it
        let bits = (self.to_bits() << 1) as $unsigned;
        let sqrt = bits.integer_sqrt() <<
          (<$signed <UInt <U, B1>> as Fixed>::Frac::USIZE/2);
        let n = $signed::from_bits (sqrt
          as <$signed <UInt <U, B1>> as Fixed>::Bits);
        // NOTE: this should never fail for odd fractional bits
        debug_assert!(n.count_ones() == 0 || n.is_positive());
        n
      }
    }
  }
}

impl_sqrt_signed_even!(FixedI8,   LtU8,   u8);
impl_sqrt_signed_even!(FixedI16,  LtU16,  u16);
impl_sqrt_signed_even!(FixedI32,  LtU32,  u32);
impl_sqrt_signed_even!(FixedI64,  LtU64,  u64);
impl_sqrt_signed_even!(FixedI128, LtU128, u128);
impl_sqrt_signed_odd!(FixedI8,   LeEqU8,   u8);
impl_sqrt_signed_odd!(FixedI16,  LeEqU16,  u16);
impl_sqrt_signed_odd!(FixedI32,  LeEqU32,  u32);
impl_sqrt_signed_odd!(FixedI64,  LeEqU64,  u64);
impl_sqrt_signed_odd!(FixedI128, LeEqU128, u128);

////////////////////////////////////////////////////////////////////////////////
//  tests
////////////////////////////////////////////////////////////////////////////////

#[cfg(test)]
mod tests {
  use super::*;
  use fixed::types::*;
  //use fixed::types::extra::*;
  use typenum::{Shright, Sub1};

  #[test]
  fn test_sqrt() {
    let x = I16F16::from_num (2);
    assert_eq!(x.sqrt(), I16F16::from_num (1.41406));

    macro_rules! test_sqrt_unsigned {
      ( $fun_zero:ident, $fun_even:ident, $(($fun_odd:ident),)? $fixed:ident,
        $unsigned:ident, $maxerr:expr
      ) => {
        fn $fun_zero (base: f64, range: i32) {
          for i in 0..range {
            let h_f64 = base.powi(i);
            let l_f64 = base.powi(-i);
            if let Some (h) = $fixed::<U0>::checked_from_num(h_f64) {
              let h_sqrt = h.sqrt();
              let err = (h_f64.sqrt() - h_sqrt.to_num::<f64>()).abs();
              if err > $maxerr {
                let ftype = format!("{}<U{}>",
                  stringify!($fixed), <U0>::USIZE);
                show!((ftype, h, h_sqrt, err));
                assert!(err <= $maxerr);
              }
            }
            if let Some (l) = $fixed::<U0>::checked_from_num(l_f64) {
              let l_sqrt = l.sqrt();
              let err = (l_f64.sqrt() - l_sqrt.to_num::<f64>()).abs();
              if err > $maxerr {
                let ftype = format!("{}<U{}>",
                  stringify!($fixed), <U0>::USIZE);
                show!((ftype, l, l_sqrt, err));
                assert!(err <= $maxerr);
              }
            }
          }
        }

        fn $fun_even<U>(base: f64, range: i32) where
          UInt <U, B0> : Unsigned + IsLessOrEqual<$unsigned, Output = True>
        {
          for i in 0..range {
            let h_f64 = base.powi(i);
            let l_f64 = base.powi(-i);
            if let Some (h) = $fixed::<UInt <U, B0>>::checked_from_num(h_f64) {
              let h_sqrt = h.sqrt();
              let err = (h_f64.sqrt() - h_sqrt.to_num::<f64>()).abs();
              if err > $maxerr {
                let ftype = format!("{}<U{}>",
                  stringify!($fixed), <UInt <U, B0>>::USIZE);
                show!((ftype, h, h_sqrt, err));
                assert!(err <= $maxerr);
              }
            }
            if let Some (l) = $fixed::<UInt <U, B0>>::checked_from_num(l_f64) {
              let l_sqrt = l.sqrt();
              let err = (l_f64.sqrt() - l_sqrt.to_num::<f64>()).abs();
              if err > $maxerr {
                let ftype = format!("{}<U{}>",
                  stringify!($fixed), <UInt <U, B0>>::USIZE);
                show!((ftype, l, l_sqrt, err));
                assert!(err <= $maxerr);
              }
            }
          }
        }
        $(
        fn $fun_odd<U>(base: f64, range: i32) where
          UInt <U, B1> : Unsigned + IsLessOrEqual<$unsigned, Output = True>
        {
          for i in 0..range {
            let h_f64 = base.powi(i);
            let l_f64 = base.powi(-i);
            if let Some (h) = $fixed::<UInt <U, B1>>::checked_from_num(h_f64) {
              let h_sqrt = h.sqrt();
              let err = (h_f64.sqrt() - h_sqrt.to_num::<f64>()).abs();
              if err > $maxerr {
                let ftype = format!("{}<U{}>",
                  stringify!($fixed), <UInt <U, B1>>::USIZE);
                show!((ftype, h, h_sqrt, err));
                assert!(err <= $maxerr);
              }
            }
            if let Some (l) = $fixed::<UInt <U, B1>>::checked_from_num(l_f64) {
              let l_sqrt = l.sqrt();
              let err = (l_f64.sqrt() - l_sqrt.to_num::<f64>()).abs();
              if err > $maxerr {
                let ftype = format!("{}<U{}>",
                  stringify!($fixed), <UInt <U, B1>>::USIZE);
                show!((ftype, l, l_sqrt, err));
                assert!(err <= $maxerr);
              }
            }
          }
        }
        )?
        eprint!("testing {},", stringify!($fun_even));
        $(
        eprint!("{}", stringify!($fun_odd));
        )?
        eprintln!();

        $fun_zero (0.5, $unsigned::I32);
        $fun_zero (2.0, $unsigned::I32);
        $fun_zero (2.5, $unsigned::I32/2);
        $fun_zero (3.0, $unsigned::I32/2);
        $fun_zero (5.0, $unsigned::I32/2);

        $fun_even::<U0>(0.5, $unsigned::I32);
        $fun_even::<U0>(2.0, $unsigned::I32);
        $fun_even::<U0>(2.5, $unsigned::I32/2);
        $fun_even::<U0>(3.0, $unsigned::I32/2);
        $fun_even::<U0>(5.0, $unsigned::I32/2);

        $(
        $fun_odd::<U1>(0.5, $unsigned::I32);
        $fun_odd::<U1>(2.0, $unsigned::I32);
        $fun_odd::<U1>(2.5, $unsigned::I32/2);
        $fun_odd::<U1>(3.0, $unsigned::I32/2);
        $fun_odd::<U1>(5.0, $unsigned::I32/2);
        )?

        $fun_even::<U2>(0.5, $unsigned::I32);
        $fun_even::<U2>(2.0, $unsigned::I32);
        $fun_even::<U2>(2.5, $unsigned::I32/2);
        $fun_even::<U2>(3.0, $unsigned::I32/2);
        $fun_even::<U2>(5.0, $unsigned::I32/2);

        $fun_even::<Shright<Sub1<Sub1<$unsigned>>,U1>>(0.5, $unsigned::I32);
        $fun_even::<Shright<Sub1<Sub1<$unsigned>>,U1>>(2.0, $unsigned::I32);
        $fun_even::<Shright<Sub1<Sub1<$unsigned>>,U1>>(2.5, $unsigned::I32/2);
        $fun_even::<Shright<Sub1<Sub1<$unsigned>>,U1>>(3.0, $unsigned::I32/2);
        $fun_even::<Shright<Sub1<Sub1<$unsigned>>,U1>>(5.0, $unsigned::I32/2);

        $(
        $fun_odd::<Shright<Sub1<$unsigned>,U1>>(0.5, $unsigned::I32);
        $fun_odd::<Shright<Sub1<$unsigned>,U1>>(2.0, $unsigned::I32);
        $fun_odd::<Shright<Sub1<$unsigned>,U1>>(2.5, $unsigned::I32/2);
        $fun_odd::<Shright<Sub1<$unsigned>,U1>>(3.0, $unsigned::I32/2);
        $fun_odd::<Shright<Sub1<$unsigned>,U1>>(5.0, $unsigned::I32/2);
        )?

        $fun_even::<Shright<$unsigned,U1>>(0.5, $unsigned::I32);
        $fun_even::<Shright<$unsigned,U1>>(2.0, $unsigned::I32);
        $fun_even::<Shright<$unsigned,U1>>(2.5, $unsigned::I32/2);
        $fun_even::<Shright<$unsigned,U1>>(3.0, $unsigned::I32/2);
        $fun_even::<Shright<$unsigned,U1>>(5.0, $unsigned::I32/2);
      }
    }

    test_sqrt_unsigned!(test_sqrt_u128_zero, test_sqrt_u128_even, FixedU128,
      U128, 8.0);
    test_sqrt_unsigned!(test_sqrt_u64_zero, test_sqrt_u64_even,
      (test_sqrt_u64_odd), FixedU64, U64, 1.0);
    test_sqrt_unsigned!(test_sqrt_u32_zero, test_sqrt_u32_even,
      (test_sqrt_u32_odd), FixedU32, U32, 1.0);
    test_sqrt_unsigned!(test_sqrt_u16_zero, test_sqrt_u16_even,
      (test_sqrt_u16_odd), FixedU16, U16, 1.0);
    test_sqrt_unsigned!(test_sqrt_u8_zero, test_sqrt_u8_even,
      (test_sqrt_u8_odd),  FixedU8,  U8,  1.0);

    macro_rules! test_sqrt_signed {
      ( $fun_zero:ident, $fun_even:ident, $fun_odd:ident, $fixed:ident,
        $unsigned:ident, $maxerr:expr
      ) => {
        fn $fun_zero (base: f64, range: i32) {
          for i in 0..range {
            let h_f64 = base.powi(i);
            let l_f64 = base.powi(-i);
            if let Some (h) = $fixed::<U0>::checked_from_num(h_f64) {
              let h_sqrt = h.sqrt();
              let err = (h_f64.sqrt() - h_sqrt.to_num::<f64>()).abs();
              if err > $maxerr {
                let ftype = format!("{}<U{}>",
                  stringify!($fixed), <U0>::USIZE);
                show!((ftype, h, h_sqrt, err));
                assert!(err <= $maxerr);
              }
            }
            if let Some (l) = $fixed::<U0>::checked_from_num(l_f64) {
              let l_sqrt = l.sqrt();
              let err = (l_f64.sqrt() - l_sqrt.to_num::<f64>()).abs();
              if err > $maxerr {
                let ftype = format!("{}<U{}>",
                  stringify!($fixed), <U0>::USIZE);
                show!((ftype, l, l_sqrt, err));
                assert!(err <= $maxerr);
              }
            }
          }
        }

        fn $fun_even<U>(base: f64, range: i32) where
          UInt <U, B0> : Unsigned + typenum::IsLess <$unsigned, Output = True> +
            IsLessOrEqual <$unsigned, Output = True>
        {
          for i in 0..range {
            let h_f64 = base.powi(i);
            let l_f64 = base.powi(-i);
            if let Some (h) = $fixed::<UInt <U, B0>>::checked_from_num(h_f64) {
              // skip out of range
              if $fixed::<UInt <U, B0>>::checked_from_num(h_f64.sqrt())
                .is_none()
              {
                continue
              }
              let h_sqrt = h.sqrt();
              let err = h_f64.sqrt() - h_sqrt.to_num::<f64>();
              if err > $maxerr {
                let ftype = format!("{}<U{}>",
                  stringify!($fixed), <UInt <U, B0>>::USIZE);
                show!((ftype, h, h_sqrt, err));
                assert!(err <= $maxerr);
              }
            }
            if let Some (l) = $fixed::<UInt <U, B0>>::checked_from_num(l_f64) {
              // skip out of range
              if $fixed::<UInt <U, B0>>::checked_from_num(l_f64.sqrt())
                .is_none()
              {
                continue
              }
              let l_sqrt = l.sqrt();
              let err = l_f64.sqrt() - l_sqrt.to_num::<f64>();
              if err > $maxerr {
                let ftype = format!("{}<U{}>",
                  stringify!($fixed), <UInt <U, B0>>::USIZE);
                show!((ftype, l, l_sqrt, err));
                assert!(err <= $maxerr);
              }
            }
          }
        }

        fn $fun_odd<U>(base: f64, range: i32) where
          UInt <U, B1> : Unsigned + IsLessOrEqual<$unsigned, Output = True>
        {
          for i in 0..range {
            let h_f64 = base.powi(i);
            let l_f64 = base.powi(-i);
            if let Some (h) = $fixed::<UInt <U, B1>>::checked_from_num(h_f64) {
              // skip out of range
              if $fixed::<UInt <U, B1>>::checked_from_num(h_f64.sqrt())
                .is_none()
              {
                continue
              }
              let h_sqrt = h.sqrt();
              let err = h_f64.sqrt() - h_sqrt.to_num::<f64>();
              if err > $maxerr {
                let ftype = format!("{}<U{}>",
                  stringify!($fixed), <UInt <U, B1>>::USIZE);
                show!((ftype, h, h_sqrt, err));
                assert!(err <= $maxerr);
              }
            }
            if let Some (l) = $fixed::<UInt <U, B1>>::checked_from_num(l_f64) {
              // skip out of range
              if $fixed::<UInt <U, B1>>::checked_from_num(l_f64.sqrt())
                .is_none()
              {
                continue
              }
              let l_sqrt = l.sqrt();
              let err = l_f64.sqrt() - l_sqrt.to_num::<f64>();
              if err > $maxerr {
                let ftype = format!("{}<U{}>",
                  stringify!($fixed), <UInt <U, B1>>::USIZE);
                show!((ftype, l, l_sqrt, err));
                assert!(err <= $maxerr);
              }
            }
          }
        }

        $fun_zero (0.5, $unsigned::I32);
        $fun_zero (2.0, $unsigned::I32);
        $fun_zero (2.5, $unsigned::I32/2);
        $fun_zero (3.0, $unsigned::I32/2);
        $fun_zero (5.0, $unsigned::I32/2);

        $fun_even::<U0>(0.5, $unsigned::I32);
        $fun_even::<U0>(2.0, $unsigned::I32);
        $fun_even::<U0>(2.5, $unsigned::I32/2);
        $fun_even::<U0>(3.0, $unsigned::I32/2);
        $fun_even::<U0>(5.0, $unsigned::I32/2);

        $fun_odd::<U1>(0.5, $unsigned::I32);
        $fun_odd::<U1>(2.0, $unsigned::I32);
        $fun_odd::<U1>(2.5, $unsigned::I32/2);
        $fun_odd::<U1>(3.0, $unsigned::I32/2);
        $fun_odd::<U1>(5.0, $unsigned::I32/2);

        $fun_even::<U2>(0.5, $unsigned::I32);
        $fun_even::<U2>(2.0, $unsigned::I32);
        $fun_even::<U2>(2.5, $unsigned::I32/2);
        $fun_even::<U2>(3.0, $unsigned::I32/2);
        $fun_even::<U2>(5.0, $unsigned::I32/2);

        $fun_even::<Shright<Sub1<Sub1<$unsigned>>,U1>>(0.5, $unsigned::I32);
        $fun_even::<Shright<Sub1<Sub1<$unsigned>>,U1>>(2.0, $unsigned::I32);
        $fun_even::<Shright<Sub1<Sub1<$unsigned>>,U1>>(2.5, $unsigned::I32/2);
        $fun_even::<Shright<Sub1<Sub1<$unsigned>>,U1>>(3.0, $unsigned::I32/2);
        $fun_even::<Shright<Sub1<Sub1<$unsigned>>,U1>>(5.0, $unsigned::I32/2);

        $fun_odd::<Shright<Sub1<$unsigned>,U1>>(0.5, $unsigned::I32);
        $fun_odd::<Shright<Sub1<$unsigned>,U1>>(2.0, $unsigned::I32);
        $fun_odd::<Shright<Sub1<$unsigned>,U1>>(2.5, $unsigned::I32/2);
        $fun_odd::<Shright<Sub1<$unsigned>,U1>>(3.0, $unsigned::I32/2);
        $fun_odd::<Shright<Sub1<$unsigned>,U1>>(5.0, $unsigned::I32/2);
      }
    }

    test_sqrt_signed!(test_sqrt_i128_zero, test_sqrt_i128_even,
      test_sqrt_i128_odd, FixedI128, U128, 8.0);
    test_sqrt_signed!(test_sqrt_i64_zero, test_sqrt_i64_even, test_sqrt_i64_odd,
      FixedI64, U64, 1.0);
    test_sqrt_signed!(test_sqrt_i32_zero, test_sqrt_i32_even, test_sqrt_i32_odd,
      FixedI32, U32, 1.0);
    test_sqrt_signed!(test_sqrt_i16_zero, test_sqrt_i16_even, test_sqrt_i16_odd,
      FixedI16, U16, 1.0);
    test_sqrt_signed!(test_sqrt_i8_zero, test_sqrt_i8_even,  test_sqrt_i8_odd,
      FixedI8,  U8,  1.0);
  }

  #[test]
  #[should_panic]
  fn test_sqrt_negative() {
    I16F16::from_num (-1.0).sqrt();
  }

  #[test]
  fn test_sqrt_max() {
    // test some misc max values
    // NOTE: integer-sqrt v0.1.2 has a bug where these would fail for i32 and
    // i128 types, so we changed the implementation to use unsigned instead of
    // signed types
    I4F4::MAX.sqrt();
    I8F8::MAX.sqrt();
    I16F16::MAX.sqrt();
    I32F32::MAX.sqrt();
    I64F64::MAX.sqrt();
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
          if i == $unsigned::MAX {
            break
          }
          i += $unsigned::from_bits (1);
        }
      }
    }
    test_unsigned_exhaustive!(U8F0, 1.0);
    test_unsigned_exhaustive!(U7F1, 1.0);
    test_unsigned_exhaustive!(U6F2, 1.0);
    test_unsigned_exhaustive!(U5F3, 1.0);
    test_unsigned_exhaustive!(U4F4, 1.0);
    test_unsigned_exhaustive!(U3F5, 1.0);
    test_unsigned_exhaustive!(U2F6, 1.0);
    test_unsigned_exhaustive!(U1F7, 1.0);
    test_unsigned_exhaustive!(U0F8, 1.0);

    test_unsigned_exhaustive!(U16F0, 1.0);
    test_unsigned_exhaustive!(U15F1, 1.0);
    test_unsigned_exhaustive!(U14F2, 1.0);
    test_unsigned_exhaustive!(U13F3, 1.0);
    test_unsigned_exhaustive!(U12F4, 1.0);
    test_unsigned_exhaustive!(U11F5, 1.0);
    test_unsigned_exhaustive!(U10F6, 1.0);
    test_unsigned_exhaustive!(U9F7,  1.0);
    test_unsigned_exhaustive!(U8F8,  1.0);
    test_unsigned_exhaustive!(U7F9,  1.0);
    test_unsigned_exhaustive!(U6F10, 1.0);
    test_unsigned_exhaustive!(U5F11, 1.0);
    test_unsigned_exhaustive!(U4F12, 1.0);
    test_unsigned_exhaustive!(U3F13, 1.0);
    test_unsigned_exhaustive!(U2F14, 1.0);
    test_unsigned_exhaustive!(U1F15, 1.0);
    test_unsigned_exhaustive!(U0F16, 1.0);
  }

  #[test]
  fn test_sqrt_signed_exhaustive() {
    macro_rules! test_signed_exhaustive {
      ($signed:ident, $maxerr:expr) => {
        let mut i = $signed::from_bits (0);
        loop {
          let err = (i.to_num::<f64>().sqrt() - i.sqrt().to_num::<f64>()).abs();
          if err >= $maxerr {
            show!((stringify!($signed), i, i.sqrt(), err));
            assert!(err < $maxerr);
          }
          if i == $signed::MAX {
            break
          }
          i += $signed::from_bits (1);
        }
      }
    }
    test_signed_exhaustive!(I8F0, 1.0);
    test_signed_exhaustive!(I7F1, 1.0);
    test_signed_exhaustive!(I6F2, 1.0);
    test_signed_exhaustive!(I5F3, 1.0);
    test_signed_exhaustive!(I4F4, 1.0);
    test_signed_exhaustive!(I3F5, 1.0);
    test_signed_exhaustive!(I2F6, 1.0);
    test_signed_exhaustive!(I1F7, 1.0);
    //test_signed_exhaustive!(I0F8, 1.0);   // unimplemented

    test_signed_exhaustive!(I16F0, 1.0);
    test_signed_exhaustive!(I15F1, 1.0);
    test_signed_exhaustive!(I14F2, 1.0);
    test_signed_exhaustive!(I13F3, 1.0);
    test_signed_exhaustive!(I12F4, 1.0);
    test_signed_exhaustive!(I11F5, 1.0);
    test_signed_exhaustive!(I10F6, 1.0);
    test_signed_exhaustive!(I9F7,  1.0);
    test_signed_exhaustive!(I8F8,  1.0);
    test_signed_exhaustive!(I7F9,  1.0);
    test_signed_exhaustive!(I6F10, 1.0);
    test_signed_exhaustive!(I5F11, 1.0);
    test_signed_exhaustive!(I4F12, 1.0);
    test_signed_exhaustive!(I3F13, 1.0);
    test_signed_exhaustive!(I2F14, 1.0);
    test_signed_exhaustive!(I1F15, 1.0);
    //test_signed_exhaustive!(I0F16, 1.0);  // unimplemented
  }
}
