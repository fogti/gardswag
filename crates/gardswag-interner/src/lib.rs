#![forbid(
    trivial_casts,
    unconditional_recursion,
    unsafe_code,
    unused_must_use,
    clippy::as_conversions,
    clippy::cast_ptr_alignment
)]
#![deny(unused_variables)]

use serde::{Deserialize, Serialize};

#[derive(Clone, Debug, Default, PartialEq, Eq, Deserialize, Serialize)]
pub struct Interner(Vec<Box<str>>);

#[derive(Clone, Copy, Debug, Default, PartialEq, Eq, PartialOrd, Ord, Hash, Deserialize, Serialize)]
pub struct Symbol(u32);

impl Interner {
    pub fn get_or_intern(&mut self, s: &str) -> Symbol {
        if s.is_empty() {
            return Symbol(0);
        }
        for (n, i) in self.0.iter().enumerate() {
            if &**i == s {
                return Symbol(n.try_into().unwrap());
            }
        }
        let ret = Symbol((self.0.len() + 1).try_into().expect("Interner out of indices"));
        self.0.push(s.to_string().into_boxed_str());
        ret
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

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn empty() {
        let mut itn = Interner::default();
        let y = itn.get_or_intern("");
        assert!(itn.0.is_empty());
        assert_eq!(itn.get(y), "");
    }

    #[test]
    fn basic() {
        let mut itn = Interner::default();
        let x = "this is a test!";
        let y = itn.get_or_intern(x);
        assert_eq!(itn.0.len(), 1);
        assert_eq!(itn.get(y), x);
    }
}
