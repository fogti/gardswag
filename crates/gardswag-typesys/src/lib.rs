#![forbid(
    trivial_casts,
    unconditional_recursion,
    unsafe_code,
    unused_must_use,
    clippy::as_conversions,
    clippy::cast_ptr_alignment
)]
#![deny(unused_variables)]

pub use gardswag_core::{ty::Scheme, Substitutable, Ty, TyLit, TyVar};

/// type constraint solver
pub mod constraint;

mod collect;
pub use collect::*;
