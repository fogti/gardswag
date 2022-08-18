#![forbid(
    trivial_casts,
    unconditional_recursion,
    unsafe_code,
    unused_must_use,
    clippy::as_conversions,
    clippy::cast_ptr_alignment
)]
#![deny(unused_variables)]

// TODO: make it possible to merge multiple interners

use core::fmt;
use serde::{Deserialize, Serialize};

#[derive(Clone, Debug, Default, PartialEq, Eq, Deserialize, Serialize)]
pub struct Interner(Vec<Box<str>>);

#[derive(
    Clone, Copy, Default, PartialEq, Eq, PartialOrd, Ord, Hash, Deserialize, Serialize,
)]
pub struct Symbol(u32);

impl Symbol {
    pub const fn empty() -> Self {
        Self(0)
    }

    pub const fn is_empty(self) -> bool {
        self.0 == 0
    }
}

impl fmt::Debug for Symbol {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "#{}", self.0)
    }
}

impl Interner {
    pub fn get_or_intern(&mut self, s: &str) -> Symbol {
        if s.is_empty() {
            return Symbol::empty();
        }
        for (n, i) in self.0.iter().enumerate() {
            if &**i == s {
                return Symbol((n + 1).try_into().unwrap());
            }
        }
        let ret = Symbol(
            (self.0.len() + 1)
                .try_into()
                .expect("Interner out of indices"),
        );
        self.0.push(s.to_string().into_boxed_str());
        ret
    }

    pub fn get_already_interned(&self, s: &str) -> Symbol {
        if s.is_empty() {
            return Symbol::empty();
        }
        for (n, i) in self.0.iter().enumerate() {
            if &**i == s {
                return Symbol((n + 1).try_into().unwrap());
            }
        }
        panic!("symbol {:?} not yet interned", s)
    }

    #[inline]
    pub fn get(&self, s: Symbol) -> &str {
        if let Some(x) = s.0.checked_sub(1) {
            &*self.0[usize::try_from(x).unwrap()]
        } else {
            ""
        }
    }
}

impl fmt::Display for Interner {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_map().entries(self.0.iter().enumerate()).finish()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty() {
        let mut itn = Interner::default();
        let y = itn.get_or_intern("");
        assert!(itn.0.is_empty());
        assert_eq!(itn.get(y), "");
        assert_eq!(Symbol::empty(), y);
        let z = itn.get_already_interned("");
        assert_eq!(z, y);
    }

    #[test]
    fn basic() {
        let mut itn = Interner::default();
        let x = "this is a test!";
        let y = itn.get_or_intern(x);
        assert_eq!(itn.0.len(), 1);
        assert_eq!(itn.get(y), x);
        let z = itn.get_already_interned(x);
        assert_eq!(z, y);
    }
}
