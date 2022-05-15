use std::path::PathBuf;
use tracing::{debug, trace};

mod infer;
mod interp;

#[derive(Clone, PartialEq, clap::ArgEnum)]
enum Mode {
    /// check if the file passes parsing + type-check
    Check,

    /// perform checks, then execute the expression
    Run,
}

#[derive(clap::Parser)]
#[clap(version)]
struct Args {
    /// file to interpret
    #[clap(short, long)]
    file: PathBuf,

    /// specify the mode
    #[clap(arg_enum, short = 'm', long)]
    mode: Mode,
}

fn mk_env_std(ctx: &mut gardswag_tysy_collect::Context) -> gardswag_typesys::Scheme {
    use gardswag_core::{ty::Scheme as TyScheme, Ty, TyLit};

    macro_rules! tl {
        (int) => {{
            Ty::Literal(TyLit::Int)
        }};
        (bool) => {{
            Ty::Literal(TyLit::Bool)
        }};
        (str) => {{
            Ty::Literal(TyLit::String)
        }};
        (()) => {{
            Ty::Literal(TyLit::Unit)
        }};
    }
    macro_rules! ta {
        ($a:expr $(=> $b:expr)*) => {{
            let mut x = vec![$a];
            $(x.push($b);)+
            let mut it = x.into_iter().rev();
            let mut y = it.next().unwrap();
            for i in it {
                y = Ty::Arrow(Box::new(i), Box::new(y));
            }
            y
        }}
    }
    macro_rules! tr {
        ({ $($key:ident: $value:expr),* $(,)? }) => {{
            Ty::Record([
                $((stringify!($key).to_string(), $value)),*
            ].into_iter().collect())
        }};
    }

    use gardswag_core::ty::Context as _;
    let tyvars: Vec<usize> = (0..2).map(|_| ctx.fresh_tyvar()).collect();
    let gtv = |i| Ty::Var(tyvars[i]);

    let ty = tr!({
        plus: ta!(tl!(int) => tl!(int) => tl!(int)),
        minus: ta!(tl!(int) => tl!(int) => tl!(int)),
        mult: ta!(tl!(int) => tl!(int) => tl!(int)),
        eq: ta!(gtv(0) => gtv(1) => tl!(bool)),
        leq: ta!(tl!(int) => tl!(int) => tl!(bool)),
        not: ta!(tl!(bool) => tl!(bool)),
        stdio: tr!({
            write: ta!(tl!(str) => tl!(())),
        }),
    });

    TyScheme {
        forall: tyvars.into_iter().collect(),
        ty,
    }
}

fn main_check(dat: &str) -> anyhow::Result<(gardswag_syntax::Block, gardswag_typesys::Scheme)> {
    let parsed = gardswag_syntax::parse(dat)?;

    let mut ctx = gardswag_tysy_collect::Context::default();

    let env = infer::Env {
        vars: [("std".to_string(), mk_env_std(&mut ctx))]
            .into_iter()
            .collect(),
    };

    let mut t = infer::infer_block(&env, &mut ctx, &parsed)?;
    debug!("type check ok");
    debug!("=T> {}", t);
    trace!("--constraints-- {}", ctx.constraints.len());
    for v in &ctx.constraints {
        trace!("\t{:?}", v);
    }
    let mut ctx2 = gardswag_typesys::Context::default();
    ctx2.solve(ctx)
        .map_err(|(offset, e)| anyhow::anyhow!("@{}: {}", offset, e))?;
    ctx2.self_resolve()?;
    // generalize the type
    use gardswag_typesys::Substitutable;
    t.apply(&|&i| ctx2.on_apply(i));
    let tg = t.generalize(&env);
    trace!("--TV--");
    for (k, v) in &ctx2.m {
        trace!("\t${}:\t{}", k, v);
    }
    trace!("--CG--");
    for (k, v) in &ctx2.g {
        trace!("\t${}:\t{:?}", k, v);
    }
    tracing::info!("=G> {}", tg);
    Ok((parsed, tg))
}

fn main_interp(parsed: &gardswag_syntax::Block) -> interp::Value<'_> {
    use interp::{Builtin as Bi, Value as Val};

    let stack = gardswag_core::VarStack {
        parent: None,
        name: "std",
        value: Val::Record(
            [
                ("plus", Bi::Plus.into()),
                ("minus", Bi::Minus.into()),
                ("mult", Bi::Mult.into()),
                ("eq", Bi::Eq.into()),
                ("leq", Bi::Leq.into()),
                ("not", Bi::Not.into()),
                (
                    "stdio",
                    Val::Record(
                        [("write", Bi::StdioWrite.into())]
                            .into_iter()
                            .map(|(i, j)| (i.to_string(), j))
                            .collect(),
                    ),
                ),
            ]
            .into_iter()
            .map(|(i, j)| (i.to_string(), j))
            .collect(),
        ),
    };

    interp::run_block(parsed, &stack)
}

fn main() {
    let args = <Args as clap::Parser>::parse();

    let dat = std::fs::read(&args.file).expect("unable to read file");
    let dat = String::from_utf8(dat).expect("file doesn't contain UTF-8 text");

    tracing_subscriber::fmt::init();

    let (parsed, _) = main_check(&dat).expect("unable to parse + type-check file");

    if args.mode == Mode::Check {
        return;
    }

    let result = main_interp(&parsed);
    println!("result: {:?}", result);
}

#[cfg(test)]
mod tests {
    use super::*;

    fn dflsubscr() -> impl tracing::subscriber::Subscriber {
        tracing_subscriber::fmt::Subscriber::builder()
            .with_env_filter(tracing_subscriber::EnvFilter::from_default_env())
            .finish()
    }

    #[test]
    fn chk_hello() {
        insta::assert_yaml_snapshot!(main_check(r#"std.stdio.write("Hello world!\n");"#).unwrap());
    }

    #[test]
    fn chk_fibo() {
        tracing::subscriber::with_default(dflsubscr(), || {
            insta::assert_yaml_snapshot!(main_check(
                r#"
                let rec fib = \x \y \n {
                  (* seq: [..., x, y] ++ [z] *)
                  let z = std.plus x y;
                  if (std.leq n 0)
                    { z }
                    { fib y z (std.minus n 1) }
                };
                fib
            "#
            )
            .unwrap());
        });
    }

    #[test]
    fn run_fibo0() {
        tracing::subscriber::with_default(dflsubscr(), || {
            let x = main_check(
                r#"
                let rec fib = \x \y \n {
                  (* seq: [..., x, y] ++ [z] *)
                  let z = std.plus x y;
                  if (std.leq n 0)
                    { z }
                    { fib y z (std.minus n 1) }
                };
                fib 1 1 0
            "#,
            )
            .unwrap();
            insta::assert_yaml_snapshot!(main_interp(&x.0));
        });
    }

    #[test]
    fn run_fibo1() {
        tracing::subscriber::with_default(dflsubscr(), || {
            let x = main_check(
                r#"
                let rec fib = \x \y \n {
                  (* seq: [..., x, y] ++ [z] *)
                  let z = std.plus x y;
                  if (std.leq n 0)
                    { z }
                    { fib y z (std.minus n 1) }
                };
                fib 1 1 1
            "#,
            )
            .unwrap();
            insta::assert_yaml_snapshot!(main_interp(&x.0));
        });
    }

    #[test]
    fn run_fibo() {
        tracing::subscriber::with_default(dflsubscr(), || {
            let x = main_check(
                r#"
                let rec fib = \x \y \n {
                  (* seq: [..., x, y] ++ [z] *)
                  let z = std.plus x y;
                  if (std.leq n 0)
                    { z }
                    { fib y z (std.minus n 1) }
                };
                fib 1 1 5
            "#,
            )
            .unwrap();
            insta::assert_yaml_snapshot!(x);
            insta::assert_yaml_snapshot!(main_interp(&x.0));
        });
    }

    #[test]
    fn chk_implicit_restr() {
        tracing::subscriber::with_default(dflsubscr(), || {
            insta::assert_yaml_snapshot!(main_check(
                r#"
                \x
                let id = \y y;
                .{
                  id;
                  x;
                  y = "{x}";
                }
            "#
            )
            .unwrap());
        });
    }

    #[test]
    fn run_id() {
        tracing::subscriber::with_default(dflsubscr(), || {
            let x = main_check(
                r#"
                let id = \x x;
                id 1
            "#,
            )
            .unwrap();
            insta::assert_yaml_snapshot!(x);
            insta::assert_yaml_snapshot!(main_interp(&x.0));
        });
    }

    #[test]
    fn run_call_blti() {
        tracing::subscriber::with_default(dflsubscr(), || {
            let x = main_check(
                r#"
                std.plus 1 1
            "#,
            )
            .unwrap();
            insta::assert_yaml_snapshot!(x);
            insta::assert_yaml_snapshot!(main_interp(&x.0));
        });
    }

    #[test]
    fn run_fix() {
        tracing::subscriber::with_default(dflsubscr(), || {
            let x = main_check(
                r#"
                let rec f = \a if (std.eq a 0) { 0 } { f 0 };
                f 1
            "#,
            )
            .unwrap();
            insta::assert_yaml_snapshot!(x);
            insta::assert_yaml_snapshot!(main_interp(&x.0));
        });
    }

    #[test]
    fn run_update() {
        tracing::subscriber::with_default(dflsubscr(), || {
            let x = main_check(
                r#"
                .{
                  a = "what";
                  b = 1;
                  c = .{};
                } // .{
                  b = "no";
                  c = 50;
                }
            "#,
            )
            .unwrap();
            insta::assert_yaml_snapshot!(x);
            insta::assert_yaml_snapshot!(main_interp(&x.0));
        });
    }

    #[test]
    fn error_int_update() {
        tracing::subscriber::with_default(dflsubscr(), || {
            insta::assert_yaml_snapshot!(main_check("0//0").map_err(|e| e.to_string()));
        });
    }

    proptest::proptest! {
        #![proptest_config(proptest::test_runner::Config::with_cases(8192))]

        #[test]
        fn doesnt_crash(s in "[ -~]+") {
            if let Ok(x) = main_check(&s) {
                main_interp(&x.0);
            }
        }
    }
}
