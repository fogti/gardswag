use crate::{
    lex, parse_expr_greedy, unexpect_eoe, Annot, AnnotFmap, Error, ErrorKind, Expr, ParseResult,
    ParseResult::*, PeekLexer,
};
use gardswag_subst::{FreeVars, Substitutable};
use serde::{Deserialize, Serialize};

#[derive(Clone, Debug, Default, PartialEq, Eq, Deserialize, Serialize)]
pub struct Block<X> {
    pub stmts: Vec<Expr<X>>,
    pub term: Option<Box<Expr<X>>>,
}

impl<X> Block<X> {
    pub fn is_var_accessed(&self, v: &str) -> bool {
        self.stmts
            .iter()
            .chain(self.term.as_ref().into_iter().map(|a| &**a))
            .any(|i| i.inner.is_var_accessed(v))
    }
}

impl<X, NewExtra> AnnotFmap<NewExtra> for Block<X> {
    type Extra = X;
    type Output = Block<NewExtra>;
    fn map<F: FnMut(Self::Extra) -> NewExtra>(self, f: &mut F) -> Self::Output {
        let Block { stmts, term } = self;
        Block {
            stmts: <_ as AnnotFmap<NewExtra>>::map(stmts, f),
            term: <_ as AnnotFmap<NewExtra>>::map(term, f),
        }
    }
}

impl<In, X: FreeVars<In>> FreeVars<In> for Block<X> {
    fn fv(&self, accu: &mut std::collections::BTreeSet<In>, do_add: bool) {
        self.stmts.fv(accu, do_add);
        if let Some(x) = &self.term {
            x.fv(accu, do_add);
        }
    }
}

impl<In, X: Substitutable<In>> Substitutable<In> for Block<X> {
    type Out = X::Out;
    fn apply<F: FnMut(&In) -> Option<X::Out>>(&mut self, f: &mut F) {
        self.stmts.apply(f);
        if let Some(x) = &mut self.term {
            x.apply(f);
        }
    }
}

pub(crate) fn parse_block(
    super_offset: usize,
    lxr: &mut PeekLexer<'_>,
) -> Result<Block<()>, Error> {
    use lex::TokenKind as Tk;

    // this handles errors and EOF
    let Annot {
        offset: fi_offset,
        inner: fi_inner,
        ..
    } = unexpect_eoe(super_offset, ParseResult::from(lxr.peek()).cloned_err())?;
    let fi_offset: usize = *fi_offset;

    let mut expect_close_brack = false;
    match fi_inner {
        Tk::LcBracket => {
            expect_close_brack = true;
            let _ = lxr.next();
        }
        Tk::RcBracket => {
            return Ok(Block::default());
        }
        Tk::RParen | Tk::SemiColon => {
            return Err(Annot {
                offset: fi_offset,
                inner: ErrorKind::UnexpectedToken(lxr.next().unwrap().unwrap()),
                extra: (),
            });
        }
        _ => {}
    }

    let mut b = Block::default();

    loop {
        if let Some(Ok(Annot {
            inner: Tk::RcBracket,
            ..
        })) = lxr.peek()
        {
            if expect_close_brack {
                let _ = lxr.next();
            }
            // end of block
            break;
        }

        let expr = match parse_expr_greedy(lxr) {
            PNone if !expect_close_brack => {
                // no terminator
                break;
            }
            PNone => {
                return Err(Annot {
                    offset: fi_offset,
                    inner: ErrorKind::UnexpectedEoe,
                    extra: (),
                })
            }
            PErr(e) => return Err(e),
            POk(x) => x,
        };

        match lxr.peek() {
            None if expect_close_brack => {
                return Err(Annot {
                    offset: fi_offset,
                    inner: ErrorKind::UnexpectedEoe,
                    extra: (),
                })
            }
            None => {
                // got terminator
                b.term = Some(Box::new(expr));
            }
            Some(x) => {
                match x
                    .as_ref()
                    .map_err(|Annot { offset, inner, .. }| Annot {
                        offset: *offset,
                        inner: inner.clone().into(),
                        extra: (),
                    })?
                    .inner
                {
                    Tk::SemiColon => {
                        b.stmts.push(expr);
                        let _ = lxr.next();
                    }
                    Tk::RcBracket => {
                        // got terminator
                        b.term = Some(Box::new(expr));
                        if expect_close_brack {
                            let _ = lxr.next();
                        }
                        // end of block
                        break;
                    }
                    _ => {
                        return Err(Annot {
                            offset: fi_offset,
                            inner: ErrorKind::UnexpectedToken(lxr.next().unwrap().unwrap()),
                            extra: (),
                        });
                    }
                }
            }
        }
    }

    Ok(b)
}
