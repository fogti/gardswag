use crate::Offsetted;
use serde::{Deserialize, Serialize};

#[derive(Clone, Debug)]
pub(crate) struct Lexer<'a> {
    inp: &'a str,
    pub(crate) offset: usize,
    lvl: Vec<LvlKind>,
    buffer: Option<Result<Token, Error>>,
}

#[derive(Clone, Copy, Debug)]
enum LvlKind {
    Quotes,
    Comment,
    CurlyBrks,
}

pub type Error = Offsetted<ErrorKind>;

#[derive(Clone, Debug, PartialEq, thiserror::Error)]
pub enum ErrorKind {
    #[error("unhandled character '{0}'")]
    UnhandledChar(char),

    #[error("unexpected EOF")]
    UnexpectedEof,

    #[error("unable to parse integer: {0}")]
    ParseInt(#[from] core::num::ParseIntError),

    #[error("unbalanced string at offset {0}")]
    UnbalancedString(usize),

    #[error("unbalanced nesting modifier")]
    UnbalancedNesting,

    #[error("no lambda argument given")]
    NoLambdaArg,

    #[error("invalid character in lamdba argument")]
    InvalidLambdaChar(char),

    #[error("keyword as lambda argument")]
    KeywordLambda,
}

pub type Token = Offsetted<TokenKind>;

#[derive(Clone, Debug, PartialEq, Eq, Deserialize, Serialize)]
pub enum TokenKind {
    Keyword(Keyword),
    Identifier(String),
    Lambda(String),
    Integer(i32),
    StringStart,
    StringEnd,
    PureString(String),

    EqSym,
    Dot,
    SemiColon,
    Pipe,

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
    False => "_0",
    If => "if",
    Let => "let",
    Rec => "rec",
    True => "_1",
}

fn count_bytes<F>(inp: &str, mut f: F) -> usize
where
    F: FnMut(char) -> bool,
{
    inp.chars()
        .take_while(move |&i| f(i))
        .map(|i| i.len_utf8())
        .sum()
}

impl<'a> Lexer<'a> {
    #[inline]
    pub(crate) fn new(inp: &'a str) -> Self {
        Self {
            inp,
            offset: 0,
            lvl: vec![],
            buffer: None,
        }
    }

    fn consume(&mut self, l: usize) -> &'a str {
        let (a, b) = self.inp.split_at(l);
        self.inp = b;
        self.offset += l;
        a
    }

    fn consume_select<F>(&mut self, f: F) -> &'a str
    where
        F: FnMut(char) -> bool,
    {
        self.consume(count_bytes(self.inp, f))
    }

    /// checks if the lexer is inside a format string
    fn is_in_fmtstr(&self) -> bool {
        matches!(self.lvl.last(), Some(&LvlKind::Quotes))
    }
}

impl Iterator for Lexer<'_> {
    type Item = Result<Token, Error>;

    fn next(&mut self) -> Option<Result<Token, Error>> {
        use unicode_normalization::UnicodeNormalization as _;
        use unicode_xid::UnicodeXID as _;

        if let Some(x) = self.buffer.take() {
            return Some(x);
        }

        let mut offset = self.offset;

        let inner = loop {
            if self.is_in_fmtstr() {
                // inside a format string, more output gets strictly forwarded
                struct Unescape<It>(It);

                impl<It: Iterator<Item = char>> Iterator for Unescape<It> {
                    type Item = char;

                    fn next(&mut self) -> Option<char> {
                        Some(match self.0.next()? {
                            '\\' => match self.0.next().unwrap() {
                                'n' => '\n',
                                't' => '\t',
                                x => x,
                            },
                            x => x,
                        })
                    }

                    fn size_hint(&self) -> (usize, Option<usize>) {
                        let (mini, maxi) = self.0.size_hint();
                        (mini / 2, maxi)
                    }
                }

                let mut escaped = false;
                let s = self.consume_select(|i| {
                    if escaped {
                        escaped = false;
                        return true;
                    }
                    if i == '\\' {
                        escaped = true;
                    }
                    !matches!(i, '{' | '}' | '"')
                });

                if let Some(x) = self.inp.chars().next() {
                    match x {
                        '{' => {}
                        '}' => {
                            self.consume(x.len_utf8());
                            self.buffer = Some(Err(Offsetted {
                                offset,
                                inner: ErrorKind::UnbalancedString(self.offset),
                            }));
                        }
                        '"' => {
                            self.consume(x.len_utf8());
                            self.lvl.pop();
                            self.buffer = Some(Ok(Offsetted {
                                offset: self.offset,
                                inner: TokenKind::StringEnd,
                            }));
                        }
                        _ => unreachable!(),
                    }
                }

                let inner = if escaped {
                    Some(Err(ErrorKind::UnexpectedEof))
                } else if !s.is_empty() {
                    Some(Ok(TokenKind::PureString(
                        Unescape(s.chars()).nfc().collect(),
                    )))
                } else if let Some(x) = self.buffer.take() {
                    return Some(x);
                } else {
                    None
                };

                if let Some(inner) = inner {
                    break inner;
                }
            }

            self.consume_select(|i| i.is_whitespace());
            offset = self.offset;

            let in_comment = matches!(self.lvl.last(), Some(&LvlKind::Comment));

            break match self.inp.chars().next()? {
                c if in_comment => {
                    self.consume(c.len_utf8());
                    match c {
                        '(' => {
                            if self.inp.starts_with('*') {
                                self.lvl.push(LvlKind::Comment);
                            }
                        }
                        '*' => {
                            if self.inp.starts_with(')') {
                                self.consume(1);
                                self.lvl.pop();
                            }
                        }
                        _ => {
                            self.consume_select(|i| !matches!(i, '(' /* ) */ | '*'));
                        }
                    }
                    continue;
                }

                '0'..='9' => {
                    let s = self.consume_select(|i| i.is_ascii_digit());
                    assert!(!s.is_empty());
                    s.parse().map(TokenKind::Integer).map_err(|e| e.into())
                }

                c @ '\\' | c @ 'λ' => {
                    self.consume(c.len_utf8());
                    // identifier
                    let s = self.consume_select(|i| i.is_xid_continue());
                    if let Some(fi) = s.chars().next() {
                        if !fi.is_xid_start() {
                            Err(ErrorKind::InvalidLambdaChar(fi))
                        } else if s.parse::<Keyword>().is_ok() {
                            Err(ErrorKind::KeywordLambda)
                        } else {
                            Ok(TokenKind::Lambda(s.nfc().to_string()))
                        }
                    } else {
                        Err(ErrorKind::NoLambdaArg)
                    }
                }

                c if c.is_xid_start() => {
                    // identifier
                    let s = self.consume_select(|i| i.is_xid_continue());
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
                        '"' => {
                            // string. all our strings are format strings,
                            // thus we need to honor brackets.
                            self.lvl.push(LvlKind::Quotes);
                            Ok(TokenKind::StringStart)
                        }
                        '=' => Ok(Tk::EqSym),
                        '.' => Ok(Tk::Dot),
                        ';' => Ok(Tk::SemiColon),
                        '|' => {
                            if self.inp.starts_with('>') {
                                self.consume(1);
                                Ok(Tk::Pipe)
                            } else {
                                Err(ErrorKind::UnhandledChar(c))
                            }
                        }
                        '{' => {
                            self.lvl.push(LvlKind::CurlyBrks);
                            Ok(Tk::LcBracket)
                        }
                        '}' => match self.lvl.pop() {
                            None | Some(LvlKind::CurlyBrks) => Ok(Tk::RcBracket),
                            _ => Err(ErrorKind::UnbalancedNesting),
                        },
                        '(' => {
                            if self.inp.starts_with('*') {
                                // comment
                                self.lvl.push(LvlKind::Comment);
                                continue;
                            } else {
                                Ok(Tk::LParen)
                            }
                        }
                        ')' => Ok(Tk::RParen),
                        _ => Err(ErrorKind::UnhandledChar(c)),
                    }
                }
            };
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
}
