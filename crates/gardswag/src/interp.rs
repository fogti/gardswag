use gardswag_syntax::{Block, Expr};
use gardswag_varstack::VarStack;
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

pub fn run_block<'a, 's>(blk: &'a Block, stack: &'s VarStack<'s, Value<'a>>) -> Value<'a> {
    for i in &blk.stmts {
        let _ = run(i, stack);
    }
    if let Some(i) = &blk.term {
        run(i, stack)
    } else {
        Value::Unit
    }
}

fn run_stacksave<'a, 's, 's3, I>(
    expr: &'a Expr,
    stack: &'s VarStack<'s, Value<'a>>,
    mut stacksave: I,
) -> Value<'a>
where
    I: Iterator<Item = (String, Value<'a>)>,
{
    match stacksave.next() {
        Some((name, value)) => run_stacksave(
            expr,
            &VarStack {
                parent: Some(stack),
                name: &name,
                value,
            },
            stacksave,
        ),
        None => run(expr, stack),
    }
}

pub fn run<'a, 's>(expr: &'a Expr, stack: &'s VarStack<'s, Value<'a>>) -> Value<'a> {
    tracing::trace!("expr={:?}", expr);
    tracing::trace!("stack={:?}", stack);
    use gardswag_syntax::ExprKind as Ek;
    match &expr.inner {
        Ek::Let { lhs, rhs, rest } => {
            let v_rhs = run(rhs, stack);
            run_block(
                rest,
                &VarStack {
                    parent: Some(stack),
                    name: &lhs.inner,
                    value: v_rhs,
                },
            )
        }
        Ek::Block(blk) => run_block(blk, stack),
        Ek::If {
            cond,
            then,
            or_else,
        } => {
            let v_cond = match run(cond, stack) {
                Value::Boolean(x) => x,
                x => panic!("invalid if condition: {:?}", x),
            };
            run_block(if v_cond { then } else { or_else }, stack)
        }
        Ek::Lambda { arg, body } => {
            let mut stacksave = std::collections::BTreeMap::new();
            for (k, v) in stack.iter() {
                if stacksave.contains_key(k) || k == arg.inner || !body.inner.is_var_accessed(k) {
                    continue;
                }
                stacksave.insert(k.to_string(), v.clone());
            }

            Value::Lambda {
                argname: &arg.inner,
                f: body,
                stacksave,
            }
        }
        Ek::Call { prim, arg } => {
            let v_arg = run(arg, stack);
            let v_prim = run(prim, stack);
            match v_prim {
                Value::Builtin { f, mut args } if f.argc() > (args.len() + 1) => {
                    args.push(v_arg);
                    Value::Builtin { f, args }
                }
                Value::Builtin { f, mut args } => {
                    args.push(v_arg);
                    assert_eq!(f.argc(), args.len());
                    use Builtin as Bi;
                    match f {
                        Bi::Plus => match (args.get(0).unwrap(), args.get(1).unwrap()) {
                            (Value::Integer(a), Value::Integer(b)) => Value::Integer(*a + *b),
                            _ => panic!("std.plus called with {:?}", args),
                        },
                        Bi::Minus => match (args.get(0).unwrap(), args.get(1).unwrap()) {
                            (Value::Integer(a), Value::Integer(b)) => Value::Integer(*a - *b),
                            _ => panic!("std.minus called with {:?}", args),
                        },
                        Bi::Mult => match (args.get(0).unwrap(), args.get(1).unwrap()) {
                            (Value::Integer(a), Value::Integer(b)) => Value::Integer(*a * *b),
                            _ => panic!("std.minus called with {:?}", args),
                        },
                        Bi::Leq => match (args.get(0).unwrap(), args.get(1).unwrap()) {
                            (Value::Integer(a), Value::Integer(b)) => Value::Boolean(*a <= *b),
                            _ => panic!("std.minus called with {:?}", args),
                        },
                        Bi::Eq => Value::Boolean(args.get(0) == args.get(1)),
                        Bi::Not => match args.get(0).unwrap() {
                            Value::Boolean(b) => Value::Boolean(!*b),
                            a => panic!("std.not called with {:?}", a),
                        },
                        Bi::StdioWrite => {
                            match args.get(0).unwrap() {
                                Value::PureString(s) => print!("{}", s),
                                x => panic!("std.stdio.write called with {:?}", x),
                            }
                            Value::Unit
                        }
                    }
                }
                Value::Lambda {
                    argname,
                    f,
                    stacksave,
                } => run_stacksave(
                    f,
                    &VarStack {
                        parent: Some(stack),
                        name: argname,
                        value: v_arg,
                    },
                    stacksave.into_iter(),
                ),
                f => panic!("called non-callable {:?} with argument {:?}", f, v_arg),
            }
        }
        Ek::Dot { prim, key } => match run(prim, stack) {
            Value::Record(mut rcm) => rcm
                .remove(&key.inner)
                .expect("unable to find key in record"),
            x => panic!("called .{} on non-record {:?}", key.inner, x),
        },
        Ek::Fix(expr) => {
            run(expr, stack);
            let top = run(expr, stack);
            match &top {
                Value::Lambda {
                    argname,
                    f,
                    stacksave,
                } => {
                    let argname = argname.to_string();
                    let stacksave = stacksave.clone();
                    let f = *f;
                    run_stacksave(
                        f,
                        &VarStack {
                            parent: Some(stack),
                            name: &argname,
                            value: top,
                        },
                        stacksave.into_iter(),
                    )
                }
                f => panic!("called non-callable {:?} with itself as argument", f),
            }
        }
        Ek::FormatString(fsts) => {
            let mut r = String::new();
            for i in fsts {
                r += &match run(i, stack) {
                    Value::PureString(s) => s,
                    Value::Integer(i) => i.to_string(),
                    Value::Boolean(b) => format!("_{}", if b { '1' } else { '0' }),
                    Value::Unit => String::new(),
                    x => panic!("invoked format' stringify on non-stringifyable {:?}", x),
                };
            }
            Value::PureString(r)
        }
        Ek::Record(rcde) => {
            let mut rcd = BTreeMap::new();
            for (k, v) in rcde {
                rcd.insert(k.clone(), run(v, stack));
            }
            Value::Record(rcd)
        }
        Ek::Identifier(id) => stack.find(&id.inner).unwrap().clone(),
        Ek::Boolean(b) => Value::Boolean(*b),
        Ek::Integer(i) => Value::Integer(*i),
        Ek::PureString(s) => Value::PureString(s.clone()),
    }
}
