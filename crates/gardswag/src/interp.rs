use gardswag_syntax::{Block, Expr};
use std::collections::BTreeMap;

#[derive(Clone, Copy, Debug, PartialEq)]
pub enum Builtin {
    Plus,
    Minus,
    Mult,
    Eq,
    Leq,
    Not,
    StdioWrite,
}

impl Builtin {
    fn argc(self) -> usize {
        match self {
            Self::Plus | Self::Minus | Self::Mult | Self::Eq | Self::Leq => 2,
            Self::Not | Self::StdioWrite => 1,
        }
    }
}

#[derive(Clone, Debug, PartialEq)]
pub enum Value<'a> {
    Unit,
    Boolean(bool),
    Integer(i32),
    PureString(String),

    Record(BTreeMap<String, Value<'a>>),

    Builtin {
        f: Builtin,
        args: Vec<Value<'a>>,
    },
    Lambda {
        argname: &'a str,
        f: &'a Expr,
        stacksave: BTreeMap<String, Value<'a>>,
    },
}

impl From<Builtin> for Value<'static> {
    fn from(x: Builtin) -> Self {
        Value::Builtin {
            f: x,
            args: Vec::new(),
        }
    }
}

pub fn run_block<'a>(blk: &'a Block, stack: &mut Vec<(String, Value<'a>)>) {
    for i in &blk.stmts {
        run(i, stack);
        stack.pop().unwrap();
    }
    if let Some(i) = &blk.term {
        run(i, stack);
    } else {
        stack.push((String::new(), Value::Unit));
    }
}

pub fn run<'a>(expr: &'a Expr, stack: &mut Vec<(String, Value<'a>)>) {
    let orig_stklen = stack.len();
    use gardswag_syntax::ExprKind as Ek;
    match &expr.inner {
        Ek::Let { lhs, rhs, rest } => {
            run(rhs, stack);
            stack.last_mut().unwrap().0 = lhs.inner.clone();
            run_block(rest, stack);
            let got_it_back = stack.pop().unwrap();
            assert_eq!(lhs.inner, got_it_back.0);
        }
        Ek::Assign { lhs, rhs } => {
            run(rhs, stack);
            let v_rhs = stack.pop().unwrap().1;
            stack.iter_mut().rev().find(|i| i.0 == lhs.inner).unwrap().1 = v_rhs;
            stack.push((String::new(), Value::Unit));
        }
        Ek::Block(blk) => run_block(blk, stack),
        Ek::If {
            cond,
            then,
            or_else,
        } => {
            run(cond, stack);
            let v_cond = match stack.pop().unwrap().1 {
                Value::Boolean(x) => x,
                x => panic!("invalid if condition: {:?}", x),
            };
            run_block(if v_cond { then } else { or_else }, stack);
        }
        Ek::Lambda { arg, body } => {
            let mut stacksave = BTreeMap::default();
            for (k, v) in stack.iter().rev() {
                if k.is_empty()
                    || k == &arg.inner
                    || stacksave.contains_key(k)
                    || !body.inner.is_var_accessed(k)
                {
                    continue;
                }
                stacksave.insert(k.to_string(), v.clone());
            }
            stack.push((
                String::new(),
                Value::Lambda {
                    argname: &arg.inner,
                    f: body,
                    stacksave,
                },
            ));
        }
        Ek::Call { prim, arg } => {
            run(arg, stack);
            run(prim, stack);
            match stack.pop().unwrap().1 {
                Value::Builtin { f, mut args } if f.argc() < (args.len() + 1) => {
                    args.push(stack.pop().unwrap().1);
                    stack.push((String::new(), Value::Builtin { f, args }));
                }
                Value::Builtin { f, mut args } => {
                    args.push(stack.pop().unwrap().1);
                    use Builtin as Bi;
                    match f {
                        Bi::Plus => {
                            stack.push((
                                String::new(),
                                match (args.get(0).unwrap(), args.get(1).unwrap()) {
                                    (Value::Integer(a), Value::Integer(b)) => {
                                        Value::Integer(*a + *b)
                                    }
                                    _ => panic!("std.plus called with {:?}", args),
                                },
                            ));
                        }
                        Bi::Minus => {
                            stack.push((
                                String::new(),
                                match (args.get(0).unwrap(), args.get(1).unwrap()) {
                                    (Value::Integer(a), Value::Integer(b)) => {
                                        Value::Integer(*a - *b)
                                    }
                                    _ => panic!("std.minus called with {:?}", args),
                                },
                            ));
                        }
                        Bi::Mult => {
                            stack.push((
                                String::new(),
                                match (args.get(0).unwrap(), args.get(1).unwrap()) {
                                    (Value::Integer(a), Value::Integer(b)) => {
                                        Value::Integer(*a * *b)
                                    }
                                    _ => panic!("std.minus called with {:?}", args),
                                },
                            ));
                        }
                        Bi::Leq => {
                            stack.push((
                                String::new(),
                                match (args.get(0).unwrap(), args.get(1).unwrap()) {
                                    (Value::Integer(a), Value::Integer(b)) => {
                                        Value::Boolean(*a <= *b)
                                    }
                                    _ => panic!("std.minus called with {:?}", args),
                                },
                            ));
                        }
                        Bi::Eq => {
                            stack.push((String::new(), Value::Boolean(args.get(0) == args.get(1))));
                        }
                        Bi::Not => {
                            stack.push((
                                String::new(),
                                match args.get(0).unwrap() {
                                    Value::Boolean(b) => Value::Boolean(!*b),
                                    a => panic!("std.not called with {:?}", a),
                                },
                            ));
                        }
                        Bi::StdioWrite => {
                            match args.get(0).unwrap() {
                                Value::PureString(s) => print!("{}", s),
                                x => panic!("std.stdio.write called with {:?}", x),
                            }
                            stack.push((String::new(), Value::Unit));
                        }
                    }
                }
                Value::Lambda {
                    argname,
                    f,
                    stacksave,
                } => {
                    let old_stackpos = stack.len();
                    stack.last_mut().unwrap().0 = argname.to_string();
                    stack.extend(stacksave);
                    run(f, stack);
                    let ret = stack.pop().unwrap();
                    stack.truncate(old_stackpos);
                    stack.push(ret);
                }
                f => panic!(
                    "called non-callable {:?} with argument {:?}",
                    f,
                    stack.last().unwrap()
                ),
            }
        }
        Ek::Dot { prim, key } => {
            run(prim, stack);
            match stack.pop().unwrap().1 {
                Value::Record(mut rcm) => stack.push((
                    String::new(),
                    rcm.remove(&key.inner)
                        .expect("unable to find key in record"),
                )),
                x => panic!("called .{} on non-record {:?}", key.inner, x),
            }
        }
        Ek::Fix(expr) => {
            run(expr, stack);
            let top = stack.last().unwrap().1.clone();
            match &top {
                Value::Lambda {
                    argname,
                    f,
                    stacksave,
                } => {
                    let argname = argname.to_string();
                    let stacksave = stacksave.clone();
                    let f = *f;
                    stack.push((argname, top));
                    let old_stackpos = stack.len();
                    stack.extend(stacksave);
                    run(f, stack);
                    let ret = stack.pop().unwrap();
                    stack.truncate(old_stackpos);
                    stack.push(ret);
                }
                f => panic!("called non-callable {:?} with itself as argument", f),
            }
        }
        Ek::FormatString(fsts) => {
            let mut r = String::new();
            for i in fsts {
                run(i, stack);
                r += &match stack.pop().unwrap().1 {
                    Value::PureString(s) => s,
                    Value::Integer(i) => i.to_string(),
                    Value::Boolean(b) => format!("_{}", if b { '1' } else { '0' }),
                    Value::Unit => String::new(),
                    x => panic!("invoked format' stringify on non-stringifyable {:?}", x),
                };
            }
            stack.push((String::new(), Value::PureString(r)));
        }
        Ek::Record(rcde) => {
            let mut rcd = BTreeMap::new();
            for (k, v) in rcde {
                run(v, stack);
                let vv = stack.pop().unwrap().1;
                rcd.insert(k.clone(), vv);
            }
            stack.push((String::new(), Value::Record(rcd)));
        }
        Ek::Identifier(id) => {
            let v = stack
                .iter_mut()
                .rev()
                .find(|i| i.0 == id.inner)
                .unwrap()
                .1
                .clone();
            stack.push((String::new(), v));
        }
        Ek::Boolean(b) => stack.push((String::new(), Value::Boolean(*b))),
        Ek::Integer(i) => stack.push((String::new(), Value::Integer(*i))),
        Ek::PureString(s) => stack.push((String::new(), Value::PureString(s.clone()))),
    }
    assert_eq!(orig_stklen + 1, stack.len());
}
