use std::path::PathBuf;

#[derive(clap::Parser)]
#[clap(version)]
struct Args {
    /// file to interpret
    #[clap(short, long)]
    file: PathBuf,
}

fn main() {
    let args = <Args as clap::Parser>::parse();

    let dat = std::fs::read(&args.file).expect("unable to read file");
    let dat = String::from_utf8(dat).expect("file doesn't contain UTF-8 text");

    let parsed = gardswag_syntax::parse(&dat).expect("unable to parse file");

    let mut env = gardswag::Env::default();
    *env.fresh_tyvars.borrow_mut() = 100..;
    use gardswag_typesys::{Scheme as TyScheme, Ty};
    env.vars.insert(
        "std".to_string(),
        TyScheme {
            forall: [0, 1].into_iter().collect(),
            t: Ty::Record {
                m: []
                    .into_iter()
                    .map(|(i, t): (&str, Ty<_>)| (i.to_string(), t))
                    .collect(),
                partial: false,
            },
        },
    );

    match env.infer_block(&parsed) {
        Ok(x) => println!("type check result: {:?}", x),
        Err(e) => panic!("type checking error: {:?}", e),
    }
}
