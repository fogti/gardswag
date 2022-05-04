#[derive(Clone, Debug)]
pub struct Lexer<'a> {
    inp: &'a str,
    offset: usize,
}

#[derive(Clone, Debug, PartialEq, thiserror::Error)]
#[error("offset {offset}: {kind}")]
pub struct Error {
    pub offset: usize,
    pub kind: ErrorKind,
}

#[derive(Clone, Debug, PartialEq, thiserror::Error)]
pub enum ErrorKind {
    #[error("unhandled character '{0}'")]
    UnhandledChar(char),

    #[error("unable to parse integer: {0}")]
    ParseInt(#[from] core::num::ParseIntError),
}

#[derive(Clone, Debug, PartialEq)]
pub struct Token {
    pub kind: TokenKind,
    pub offset: usize,
}

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum TokenKind {
    Keyword(Keyword),
    String(String),
    Int(i32),

    EqSym,
    Dot,
    SemiColon,

    LcBracket,
    RcBracket,
}

macro_rules! keywords {
    ($($r:ident => $s:literal),* $(,)?) => {
        #[derive(Clone, Copy, Debug, PartialEq, Eq)]
        pub enum Keyword {
            $($r),*,
        }

        impl core::str::FromStr for Keyword {
            type Err = &'static str;
            fn from_str(s: &str) -> Result<Self, &'static str> {
                Ok(match s {
                    $($s => Self::$r),*,
                    _ => return Err("unknown keyword"),
                })
            }
        }

        impl core::convert::AsRef<str> for Keyword {
            fn as_ref(&self) -> &str {
                match self {
                    $(Self::$r => $s),*,
                }
            }
        }

        impl core::fmt::Display for Keyword {
            fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
                f.write_str(self.as_ref())
            }
        }
    }
}

keywords! {
    Let => "let",
    While => "while",
    Std => "std",
}

fn count_bytes<F>(inp: &str, f: F) -> usize
where
    F: Fn(&char) -> bool,
{
    inp.chars().take_while(f).map(char::len_utf8).sum()
}

impl<'a> Lexer<'a> {
    #[inline]
    pub fn new(inp: &'a str) -> Self {
        Self { inp, offset: 0 }
    }

    #[inline(always)]
    pub fn offset(&self) -> usize {
        self.offset
    }

    fn consume(&mut self, l: usize) -> &'a str {
        let (a, b) = self.inp.split_at(l);
        self.inp = b;
        self.offset += l;
        a
    }

    fn consume_select<F>(&mut self, f: F) -> &'a str
    where
        F: Fn(&char) -> bool,
    {
        self.consume(count_bytes(self.inp, f))
    }
}

impl Iterator for Lexer<'_> {
    type Item = Result<Token, Error>;

    fn next(&mut self) -> Option<Result<Token, Error>> {
        use unicode_normalization::UnicodeNormalization as _;
        use unicode_xid::UnicodeXID as _;

        self.consume_select(|i| i.is_whitespace());
        let offset = self.offset;

        let kind = match self.inp.chars().next()? {
            '0'..='9' => {
                let s = self.consume_select(|i| i.is_ascii_digit());
                assert!(!s.is_empty());
                s.parse().map(TokenKind::Int).map_err(|e| e.into())
            }

            c if c.is_xid_start() => {
                // identifier
                let s = self.consume_select(|i| i.is_xid_continue());
                assert!(!s.is_empty());
                // check if it is a keyword
                Ok(if let Ok(kw) = s.parse::<Keyword>() {
                    TokenKind::Keyword(kw)
                } else {
                    TokenKind::String(s.nfc().to_string())
                })
            }

            c => {
                self.consume(c.len_utf8());
                match c {
                    '=' => Ok(TokenKind::EqSym),
                    '.' => Ok(TokenKind::Dot),
                    ';' => Ok(TokenKind::SemiColon),
                    '{' => Ok(TokenKind::LcBracket),
                    '}' => Ok(TokenKind::RcBracket),
                    _ => Err(ErrorKind::UnhandledChar(c)),
                }
            }
        };

        // combine {kind, offset}
        assert_ne!(offset, self.offset);
        Some(match kind {
            Ok(kind) => Ok(Token { kind, offset }),
            Err(kind) => Err(Error { kind, offset }),
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn lex_let() {
        insta::assert_debug_snapshot!(Lexer::new("let a = 1;").collect::<Vec<_>>());
    }

    #[test]
    fn lex_while() {
        insta::assert_debug_snapshot!(
            Lexer::new("while std.leq a b {\na = std.plus a b;\n}\n").collect::<Vec<_>>()
        );
    }
}
