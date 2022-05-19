use gardswag_typesys::CollectContext as TyCollectCtx;
use std::path::PathBuf;
use tracing::{debug, trace};

mod infer;
mod interp;

#[cfg(test)]
mod tests;

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

fn mk_env_std(ctx: &mut TyCollectCtx) -> gardswag_typesys::Scheme {
    use gardswag_typesys::{Scheme as TyScheme, Ty, TyLit};

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

fn main_check(
    dat: &str,
) -> anyhow::Result<(
    gardswag_syntax::Block,
    gardswag_typesys::constraint::SchemeSer,
)> {
    let parsed = gardswag_syntax::parse(dat)?;
    let mut ctx = TyCollectCtx::default();

    let env = infer::Env {
        vars: [("std".to_string(), mk_env_std(&mut ctx))]
            .into_iter()
            .collect(),
    };

    let mut t = infer::infer_block(&env, &mut ctx, 0, &parsed, None)?;
    debug!("type inference constraints generated");
    debug!("=T> {}", t);
    debug!("--constraints-- {}", ctx.constraints.len());
    for v in &ctx.constraints {
        debug!("\t{:?}", v);
    }
    let mut ctx2 = gardswag_typesys::constraint::Context::default();
    ctx2.solve(ctx)
        .map_err(|(offset, e)| anyhow::anyhow!("@{}: {}", offset, e))?;
    ctx2.self_resolve()?;
    debug!("type constraints, as far as possible, solved");
    // generalize the type
    use gardswag_typesys::Substitutable;
    t.apply(&|&i| ctx2.on_apply(i));
    //let tg = t.generalize(&env);
    let tg = gardswag_typesys::Scheme {
        forall: {
            let mut tfv = Default::default();
            t.fv(&mut tfv, true);
            tfv
        },
        ty: t,
    };
    trace!("--TV--");
    for (k, v) in &ctx2.m {
        trace!("\t${}:\t{}", k, v);
    }
    trace!("--CG--");
    for (k, v) in &ctx2.g {
        trace!("\t${}:\t{:?}", k, v);
    }
    let tgx = ctx2.export_scheme(tg);
    tracing::info!("=G> {:#?}", tgx);
    Ok((parsed, tgx))
}

fn main_interp(parsed: &gardswag_syntax::Block) -> interp::Value<'_> {
    use interp::{Builtin as Bi, Value as Val};

    let stack = gardswag_varstack::VarStack {
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
                            .map(|(i, j)| (i, j))
                            .collect(),
                    ),
                ),
            ]
            .into_iter()
            .map(|(i, j)| (i, j))
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
