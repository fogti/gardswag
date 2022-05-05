#[derive(Clone, Debug, PartialEq, Eq)]
pub struct Offsetted<T> {
    pub offset: usize,
    pub inner: T,
}

impl<T: std::error::Error + 'static> std::error::Error for Offsetted<T> {
    #[inline]
    fn source(&self) -> Option<&(dyn std::error::Error + 'static)> {
        Some(&self.inner)
    }
}

impl<T: core::fmt::Display> core::fmt::Display for Offsetted<T> {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "@{}: {}", self.offset, self.inner)
    }
}

impl From<Offsetted<crate::lex::ErrorKind>> for Offsetted<crate::ErrorKind> {
    #[inline]
    fn from(
        Offsetted { offset, inner }: Offsetted<crate::lex::ErrorKind>,
    ) -> Offsetted<crate::ErrorKind> {
        Self {
            offset,
            inner: inner.into(),
        }
    }
}

impl<T, E> From<Offsetted<Result<T, E>>> for Result<Offsetted<T>, Offsetted<E>> {
    #[inline]
    fn from(Offsetted { offset, inner }: Offsetted<Result<T, E>>) -> Self {
        match inner {
            Ok(inner) => Ok(Offsetted { offset, inner }),
            Err(inner) => Err(Offsetted { offset, inner }),
        }
    }
}
