#[derive(Clone, Debug)]
pub enum Ty {
    /// `()`
    Unit,
    /// `int`
    Integer,
    /// `str`
    String,
}

#[cfg(test)]
mod tests {}
