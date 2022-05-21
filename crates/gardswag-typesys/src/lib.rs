#![forbid(
    trivial_casts,
    unconditional_recursion,
    unsafe_code,
    unused_must_use,
    clippy::as_conversions,
    clippy::cast_ptr_alignment
)]
#![deny(unused_variables)]

/// base type definitions
mod ty;
pub use ty::{FinalArgMultiplicity, Scheme, Ty, TyLit, TyVar};

pub use gardswag_subst::{FreeVars, Substitutable};

/// type constraint data structures
mod collect;
pub use collect::{ArgMultiplicity, ArgMultiplicityId, Context as CollectContext};

/// type constraint solver + data structures
pub mod constraint;
