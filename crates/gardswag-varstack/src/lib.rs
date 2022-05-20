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

use core::fmt;

pub struct VarStack<'s, 'a, V> {
    pub parent: Option<&'s VarStack<'s, 'a, V>>,
    pub name: &'a str,
    pub value: V,
}

impl<V: fmt::Debug> fmt::Debug for VarStack<'_, '_, V> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_map().entries(self.iter()).finish()
    }
}

impl<'s, 'a, V> VarStack<'s, 'a, V> {
    pub fn find(&self, name: &str) -> Option<&V> {
        let mut this = self;
        while this.name != name {
            this = *this.parent.as_ref()?;
        }
        Some(&this.value)
    }
    pub fn iter(&'s self) -> Iter<'s, 'a, V> {
        Iter { inner: Some(self) }
    }
}

#[derive(Debug)]
pub struct Iter<'s, 'a, V> {
    inner: Option<&'s VarStack<'s, 'a, V>>,
}

impl<'s, 'a, V> Iterator for Iter<'s, 'a, V> {
    type Item = (&'a str, &'s V);

    fn next(&mut self) -> Option<Self::Item> {
        let inner = self.inner.take()?;
        self.inner = inner.parent;
        Some((inner.name, &inner.value))
    }
}
