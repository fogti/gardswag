#![forbid(
    trivial_casts,
    unconditional_recursion,
    unsafe_code,
    unused_must_use,
    clippy::as_conversions,
    clippy::cast_ptr_alignment
)]
#![deny(unused_variables)]
#![no_std]

use core::{cmp, fmt};

pub struct VarStack<'s, S, V> {
    pub parent: Option<&'s VarStack<'s, S, V>>,
    pub name: S,
    pub value: V,
}

impl<S: Copy + fmt::Debug, V: fmt::Debug> fmt::Debug for VarStack<'_, S, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_map().entries(self.iter()).finish()
    }
}

impl<'s, S, V> VarStack<'s, S, V> {
    pub fn find(&self, name: &S) -> Option<&V>
    where
        S: cmp::PartialEq,
    {
        let mut this = self;
        while &this.name != name {
            this = *this.parent.as_ref()?;
        }
        Some(&this.value)
    }
    pub fn iter(&'s self) -> Iter<'s, S, V>
    where
        S: Copy,
    {
        Iter { inner: Some(self) }
    }
}

pub struct Iter<'s, S, V> {
    inner: Option<&'s VarStack<'s, S, V>>,
}

impl<'s, S: Copy, V> Iterator for Iter<'s, S, V> {
    type Item = (S, &'s V);

    fn next(&mut self) -> Option<Self::Item> {
        let inner = self.inner.take()?;
        self.inner = inner.parent;
        Some((inner.name, &inner.value))
    }
}
