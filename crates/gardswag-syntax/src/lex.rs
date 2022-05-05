use crate::Offsetted;
use serde::{Deserialize, Serialize};

#[derive(Clone, Debug)]
pub(crate) struct Lexer<'a> {
    inp: &'a str,
    pub(crate) offset: usize,
}

pub type Error = Offsetted<ErrorKind>;

#[derive(Clone, Debug, PartialEq, thiserror::Error)]
pub enum ErrorKind {
    #[error("unhandled character '{0}'")]
    UnhandledChar(char),

    #[error("unable to parse integer: {0}")]
    ParseInt(#[from] core::num::ParseIntError),

    #[error("unbalanced string at suboffset {0} with nesting {1:?}")]
    UnbalancedString(usize, Vec<Nest>),

    #[error("unexpected EOF")]
    UnexpectedEof,
}

pub type Token = Offsetted<TokenKind>;

#[derive(Clone, Debug, PartialEq, Eq, Deserialize, Serialize)]
pub enum TokenKind {
    Keyword(Keyword),
    Identifier(String),
    Integer(i32),
    FormatString(String),

    EqSym,
    Dot,
    SemiColon,

    LcBracket,
    RcBracket,

    LParen,
    RParen,
}

macro_rules! keywords {
    ($($r:ident => $s:literal),* $(,)?) => {
        #[derive(Clone, Copy, Debug, PartialEq, Eq, Deserialize, Serialize)]
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
    Break => "break",
    If => "if",
    Let => "let",
    Loop => "loop",
}

fn count_bytes<F>(inp: &str, mut f: F) -> usize
where
    F: FnMut(usize, char) -> bool,
{
    inp.char_indices()
        .take_while(move |&(n, i)| f(n, i))
        .map(|(_, i)| i.len_utf8())
        .sum()
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, Deserialize, Serialize)]
pub enum Nest {
    CurlyBrackets,
    Parentheses,
    Quotes,
}

impl<'a> Lexer<'a> {
    #[inline]
    pub(crate) fn new(inp: &'a str) -> Self {
        Self { inp, offset: 0 }
    }

    fn consume(&mut self, l: usize) -> &'a str {
        let (a, b) = self.inp.split_at(l);
        self.inp = b;
        self.offset += l;
        a
    }

    fn consume_select<F>(&mut self, f: F) -> &'a str
    where
        F: FnMut(usize, char) -> bool,
    {
        self.consume(count_bytes(self.inp, f))
    }
}

impl Iterator for Lexer<'_> {
    type Item = Result<Token, Error>;

    fn next(&mut self) -> Option<Result<Token, Error>> {
        use unicode_normalization::UnicodeNormalization as _;
        use unicode_xid::UnicodeXID as _;

        self.consume_select(|_, i| i.is_whitespace());
        let offset = self.offset;

        let inner = match self.inp.chars().next()? {
            '0'..='9' => {
                let s = self.consume_select(|_, i| i.is_ascii_digit());
                assert!(!s.is_empty());
                s.parse().map(TokenKind::Integer).map_err(|e| e.into())
            }

            '"' => {
                // string. all our strings are format strings,
                // thus we need to honor backets.
                let mut lvls = Vec::new();
                let mut escaped = false;
                let mut e = None;
                let s = self.consume_select(|suboffs, i| {
                    if e.is_some() || lvls.is_empty() {
                        return false;
                    }
                    if escaped {
                        return true;
                    }
                    match (i, lvls.last()) {
                        ('"', Some(Nest::Quotes)) => {
                            lvls.pop();
                        }
                        ('"', _) => lvls.push(Nest::Quotes),
                        ('{', _) => lvls.push(Nest::CurlyBrackets),
                        ('}', Some(Nest::CurlyBrackets)) => {
                            lvls.pop();
                        }
                        ('}', _) => {
                            e = Some(suboffs);
                        }
                        ('(', _) => lvls.push(Nest::Parentheses),
                        (')', Some(Nest::Parentheses)) => {
                            lvls.pop();
                        }
                        (')', _) => {
                            e = Some(suboffs);
                        }
                        ('\\', _) => {
                            escaped = true;
                        }
                        (_, _) => {}
                    }
                    true
                });

                if escaped || !lvls.is_empty() {
                    Err(ErrorKind::UnexpectedEof)
                } else if let Some(suboffs) = e {
                    Err(ErrorKind::UnbalancedString(suboffs, lvls))
                } else {
                    Ok(TokenKind::FormatString(s.to_string()))
                }
            }

            c if c.is_xid_start() => {
                // identifier
                let s = self.consume_select(|_, i| i.is_xid_continue());
                assert!(!s.is_empty());
                // check if it is a keyword
                Ok(if let Ok(kw) = s.parse::<Keyword>() {
                    TokenKind::Keyword(kw)
                } else {
                    TokenKind::Identifier(s.nfc().to_string())
                })
            }

            c => {
                self.consume(c.len_utf8());
                use TokenKind as Tk;
                match c {
                    '=' => Ok(Tk::EqSym),
                    '.' => Ok(Tk::Dot),
                    ';' => Ok(Tk::SemiColon),
                    '{' => Ok(Tk::LcBracket),
                    '}' => Ok(Tk::RcBracket),
                    '(' => Ok(Tk::LParen),
                    ')' => Ok(Tk::RParen),
                    _ => Err(ErrorKind::UnhandledChar(c)),
                }
            }
        };

        // combine {kind, offset}
        assert_ne!(offset, self.offset);
        Some(Offsetted { offset, inner }.into())
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
    fn lex_loop() {
        insta::assert_debug_snapshot!(
            Lexer::new("loop {\na = std.plus a b;\n}\n").collect::<Vec<_>>()
        );
    }
}
