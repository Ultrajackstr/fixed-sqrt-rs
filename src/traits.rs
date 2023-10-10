//! Additional traits


use typenum::{uint, B0, U0};

pub trait IsEven : uint::GetBit <U0, Output=B0> {}

impl <U> IsEven for U where U : uint::GetBit <U0, Output=B0> {}