extern crate clap;
extern crate fixed;
extern crate fixed_sqrt;
extern crate integer_sqrt;

use fixed::types::*;
use fixed::types::extra::Unsigned;
use fixed::traits::Fixed;
use fixed_sqrt::{FixedSqrtEven, FixedSqrtOdd};

//use integer_sqrt::IntegerSquareRoot;

macro_rules! show {
  ($e:expr) => { println!("{}: {:?}", stringify!($e), $e); }
}

#[allow(unused_macros)]
macro_rules! bits8 {
  ($e:expr) => { println!("{}: {:08b}", stringify!($e), $e); }
}

#[derive(Debug, Default)]
struct MaxErr <F : Fixed> {
  pub fixed   : F,
  pub sqrt    : F,
  pub exact   : f64,
  pub err_abs : f64,
  pub err_pct : f64
}

fn main() {
  use std::io::Write;
  println!("errors main...");

  let opts = clap::App::new ("FixedSqrt Errors Example")
    .arg (clap::Arg::with_name ("plot-csv")
      .short ("p")
      .help ("Dump actual vs computed sqrts to CSV for plotting"))
    .get_matches();

  macro_rules! exhaustive_unsigned {
    ($unsigned:ident) => {
      println!("{}", std::iter::repeat ('~').take (80).collect::<String>());
      show!($unsigned::min_value());
      show!($unsigned::max_value());
      let mut file = if opts.occurrences_of ("plot-csv") > 0 {
        Some (std::fs::File::create (
          format!("{}.csv", stringify!($unsigned))).unwrap())
      } else {
        None
      };
      let mut avg_err_abs = 0.0;
      let mut avg_err_pct = 0.0;
      let mut max_err_abs = MaxErr::default();
      let mut max_err_pct = MaxErr::default();
      let mut i = $unsigned::from_bits (0);
      let mut count = 0;
      loop {
        count += 1;
        let fixed   = i;
        let sqrt    = fixed.sqrt();
        let exact   = fixed.to_num::<f64>().sqrt();
        let err_abs = (exact - sqrt.to_num::<f64>()).abs();
        let err_pct = if exact == 0.0 {
          assert!(err_abs == 0.0);
          0.0
        } else {
          err_abs / exact
        };
        file.as_mut().map (|file|
          file.write (format!("{},{},{}\n", fixed, exact, sqrt).as_bytes())
            .unwrap());
        avg_err_abs += err_abs;
        avg_err_pct += err_pct;
        if err_abs > max_err_abs.err_abs {
          max_err_abs = MaxErr { fixed, sqrt, exact, err_abs, err_pct };
        }
        if err_pct > max_err_pct.err_pct {
          max_err_pct = MaxErr { fixed, sqrt, exact, err_abs, err_pct };
        }
        if i == $unsigned::max_value() {
          break
        }
        i += $unsigned::from_bits (1);
      }
      show!(count);
      avg_err_abs = avg_err_abs / count as f64;
      avg_err_pct = avg_err_pct / count as f64;
      show!(max_err_abs);
      show!(max_err_pct);
      show!(avg_err_abs);
      show!(avg_err_pct);
    }
  }

  macro_rules! exhaustive_signed {
    ($signed:ident) => {
      println!("{}", std::iter::repeat ('~').take (80).collect::<String>());
      show!($signed::min_value());
      show!($signed::max_value());
      let mut file = if opts.occurrences_of ("plot-csv") > 0 {
        Some (std::fs::File::create (
          format!("{}.csv", stringify!($signed))).unwrap())
      } else {
        None
      };
      let mut avg_err_abs = 0.0;
      let mut avg_err_pct = 0.0;
      let mut max_err_abs = MaxErr::default();
      let mut max_err_pct = MaxErr::default();
      let mut i = $signed::from_bits (0);
      let mut count = 0;
      loop {
        let fixed   = i;
        if <$signed as Fixed>::Frac::USIZE ==
          8 * std::mem::size_of::<<$signed as Fixed>::Bits>() &&
          fixed >= $signed::from_num (0.25)
        {
          break
        }
        count += 1;
        let sqrt    = fixed.sqrt();
        let exact   = fixed.to_num::<f64>().sqrt();
        let err_abs = (exact - sqrt.to_num::<f64>()).abs();
        let err_pct = if exact == 0.0 {
          0.0
        } else {
          err_abs / exact
        };
        file.as_mut().map (|file|
          file.write (format!("{},{},{}\n", fixed, exact, sqrt).as_bytes())
            .unwrap());
        avg_err_abs += err_abs;
        avg_err_pct += err_pct;
        if err_abs > max_err_abs.err_abs {
          max_err_abs = MaxErr { fixed, sqrt, exact, err_abs, err_pct };
        }
        if err_pct > max_err_pct.err_pct {
          max_err_pct = MaxErr { fixed, sqrt, exact, err_abs, err_pct };
        }
        if i == $signed::max_value() {
          break
        }
        i += $signed::from_bits (1);
      }
      show!(count);
      avg_err_abs = avg_err_abs / count as f64;
      avg_err_pct = avg_err_pct / count as f64;
      show!(max_err_abs);
      show!(max_err_pct);
      show!(avg_err_abs);
      show!(avg_err_pct);
    }
  }

  exhaustive_unsigned!(U8F0);
  exhaustive_unsigned!(U7F1);
  exhaustive_unsigned!(U6F2);
  exhaustive_unsigned!(U5F3);
  exhaustive_unsigned!(U4F4);
  exhaustive_unsigned!(U3F5);
  exhaustive_unsigned!(U2F6);
  exhaustive_unsigned!(U1F7);
  exhaustive_unsigned!(U0F8);

  exhaustive_signed!(I8F0);
  exhaustive_signed!(I7F1);
  exhaustive_signed!(I6F2);
  exhaustive_signed!(I5F3);
  exhaustive_signed!(I4F4);
  exhaustive_signed!(I3F5);
  exhaustive_signed!(I2F6);
  exhaustive_signed!(I1F7);
  //exhaustive_signed!(I0F8);

  exhaustive_unsigned!(U16F0);
  exhaustive_unsigned!(U15F1);
  exhaustive_unsigned!(U14F2);
  exhaustive_unsigned!(U13F3);
  exhaustive_unsigned!(U12F4);
  exhaustive_unsigned!(U11F5);
  exhaustive_unsigned!(U10F6);
  exhaustive_unsigned!(U9F7);
  exhaustive_unsigned!(U8F8);
  exhaustive_unsigned!(U7F9);
  exhaustive_unsigned!(U6F10);
  exhaustive_unsigned!(U5F11);
  exhaustive_unsigned!(U4F12);
  exhaustive_unsigned!(U3F13);
  exhaustive_unsigned!(U2F14);
  exhaustive_unsigned!(U1F15);
  exhaustive_unsigned!(U0F16);

  exhaustive_signed!(I16F0);
  exhaustive_signed!(I15F1);
  exhaustive_signed!(I14F2);
  exhaustive_signed!(I13F3);
  exhaustive_signed!(I12F4);
  exhaustive_signed!(I11F5);
  exhaustive_signed!(I10F6);
  exhaustive_signed!(I9F7);
  exhaustive_signed!(I8F8);
  exhaustive_signed!(I7F9);
  exhaustive_signed!(I6F10);
  exhaustive_signed!(I5F11);
  exhaustive_signed!(I4F12);
  exhaustive_signed!(I3F13);
  exhaustive_signed!(I2F14);
  exhaustive_signed!(I1F15);
  //exhaustive_signed!(I0F16);

  println!("...errors main");
}
