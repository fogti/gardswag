use gardswag_infer_cgen as infer;
use gardswag_typesys::CollectContext as TyCollectCtx;
use std::path::PathBuf;
use tracing::{debug, trace};

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
    use gardswag_typesys::{FinalArgMultiplicity as Fam, Scheme as TyScheme, Ty, TyLit};

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
        ($af:expr, $a:expr $(=> $bf:expr, $b:expr)*) => {{
            let mut x = vec![($af, $a)];
            $(x.push(($bf, $b));)+
            let mut it = x.into_iter().rev();
            let mut y = it.next().unwrap().1;
            for (f, i) in it {
                y = f.resolved(i, y);
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
    macro_rules! ttu {
        ($($key:ident: $value:expr),* $(,)?) => {{
            Ty::TaggedUnion([
                $((stringify!($key).to_string(), $value)),*
            ].into_iter().collect())
        }}
    }
    macro_rules! tch {
        (send: $value:expr) => {{
            Ty::ChanSend(Box::new($value))
        }};
        (recv: $value:expr) => {{
            Ty::ChanRecv(Box::new($value))
        }};
    }

    let tyvars: Vec<usize> = (0..5).map(|_| ctx.fresh_tyvar()).collect();
    let gtv = |i| Ty::Var(tyvars[i]);

    let ty = tr!({
        plus: ta!(Fam::Linear, tl!(int) => Fam::Linear, tl!(int) => Fam::Linear, tl!(int)),
        minus: ta!(Fam::Linear, tl!(int) => Fam::Linear, tl!(int) => Fam::Linear, tl!(int)),
        mult: ta!(Fam::Linear, tl!(int) => Fam::Linear, tl!(int) => Fam::Linear, tl!(int)),
        eq: ta!(Fam::Linear, gtv(0) => Fam::Linear, gtv(1) => Fam::Linear, tl!(bool)),
        leq: ta!(Fam::Linear, tl!(int) => Fam::Linear, tl!(int) => Fam::Linear, tl!(bool)),
        not: ta!(Fam::Linear, tl!(bool) => Fam::Linear, tl!(bool)),
        spawn_thread: ta!(Fam::Linear, ta!(Fam::Unrestricted, tl!(()) => Fam::Linear, tl!(())) => Fam::Linear, tl!(())),
        make_chan: ta!(Fam::Erased, tl!(()) => Fam::Unrestricted, tr!({
            send: tch!(send: gtv(2)),
            recv: tch!(recv: gtv(2)),
        })),
        chan_send: ta!(Fam::Linear, gtv(3) => Fam::Linear, tch!(send: gtv(3)) => Fam::Linear, tl!(bool)),
        chan_recv: ta!(Fam::Linear, tch!(recv: gtv(4)) => Fam::Linear, ttu!(None: tl!(()), Some: gtv(4))),
        stdio: tr!({
            write: ta!(Fam::Linear, tl!(str) => Fam::Linear, tl!(())),
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
    gardswag_syntax::Block<crate::infer::InferExtra>,
    gardswag_typesys::constraint::SchemeSer,
)> {
    let parsed = gardswag_syntax::parse(dat)?;
    let mut ctx = TyCollectCtx::default();

    let env = gardswag_varstack::VarStack {
        parent: None,
        name: "std",
        value: (
            mk_env_std(&mut ctx),
            std::rc::Rc::new(core::cell::RefCell::new((vec![Default::default()], 0))),
        ),
    };

    let mut parsed = infer::infer_block(&env, &mut ctx, 0, &parsed, None)?;
    debug!("type inference constraints generated");
    debug!("=TyAst> {:?}", parsed);
    debug!("--constraints-- {}", ctx.constraints.len());
    for v in &ctx.constraints {
        debug!("\t{:?}", v);
    }
    let mut ctx2 = gardswag_typesys::constraint::Context::default();
    ctx2.solve(ctx)
        .map_err(|(offset, e)| anyhow::anyhow!("@{}: {}", offset, e))?;
    ctx2.self_resolve()?;
    debug!("type constraints, as far as possible, solved");
    parsed.apply(&mut |&i| ctx2.on_apply(i));
    // generalize the type
    use gardswag_typesys::{FreeVars as _, Substitutable as _};
    let ty = parsed
        .term
        .clone()
        .map(|i| i.extra.ty)
        .unwrap_or(gardswag_typesys::Ty::Literal(gardswag_typesys::TyLit::Unit));
    //let tg = t.generalize(&env);
    let tg = gardswag_typesys::Scheme {
        forall: {
            let mut tfv = Default::default();
            ty.fv(&mut tfv, true);
            tfv
        },
        ty,
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

fn main_interp<'a: 'envout + 'envin, 'envout, 'envin>(
    s: &'envout crossbeam_utils::thread::Scope<'envin>,
    parsed: &'a gardswag_syntax::Block<crate::infer::InferExtra>,
) -> interp::Value<'a, crate::infer::InferExtra> {
    use interp::{Builtin as Bi, Value as Val};

    let stack: gardswag_varstack::VarStack<'a, 'static, Val<'a, _>> = gardswag_varstack::VarStack {
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
                ("spawn_thread", Bi::SpawnThread.into()),
                ("make_chan", Bi::MakeChan.into()),
                ("chan_send", Bi::ChanSend.into()),
                ("chan_recv", Bi::ChanRecv.into()),
                (
                    "stdio",
                    Val::Record([("write", Bi::StdioWrite.into())].into_iter().collect()),
                ),
            ]
            .into_iter()
            .collect(),
        ),
    };

    interp::run_block(interp::Env { thscope: s }, parsed, &stack)
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

    let result = crossbeam_utils::thread::scope(|s| main_interp(s, &parsed))
        .expect("unable to join threads");
    println!("result: {:?}", result);
}
