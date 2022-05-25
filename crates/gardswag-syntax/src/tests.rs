fn parse(s: &str) -> Result<(gardswag_interner::Interner, super::Block<()>), super::Error> {
    let mut itn = gardswag_interner::Interner::default();
    super::parse(&mut itn, s).map(|res| (itn, res))
}

#[test]
fn block_term() {
    insta::assert_yaml_snapshot!(parse("{ a }").unwrap());
}

#[test]
fn hello_world() {
    insta::assert_yaml_snapshot!(parse(r#"std.stdio.write("Hello world!\n");"#).unwrap());
}

#[test]
fn fibo() {
    insta::assert_yaml_snapshot!(parse(
        r#"
                let a = 1;
                let b = 1;
                let rec fib = \x \y \n {
                  (* seq: [..., x, y] ++ [z] *)
                  let z = std.plus x y;
                  if (std.leq n 0)
                    { z }
                    { fib y z (std.minus n 1) }
                };
                std.stdio.write "{fib 1 1 6}\m";
            "#
    )
    .unwrap());
}

#[test]
fn complex_fstr() {
    insta::assert_yaml_snapshot!(parse(
        r#"
                "{
                  let a = 1;
                  std.stdio.write("{a}\n");
                  a
                }"
            "#
    )
    .unwrap());
}

#[test]
fn record() {
    insta::assert_yaml_snapshot!(parse(
        r#"
                let id = \x x;
                .{
                   id = id;
                   id2 = id;
                   torben = id 1;
                }
            "#
    )
    .unwrap());
}

#[test]
fn record_inherit() {
    insta::assert_yaml_snapshot!(parse(
        r#"
                let id = \x x;
                let torben = id 1;
                .{
                   id;
                   id2 = id;
                   torben;
                }
            "#
    )
    .unwrap());
}

#[test]
fn pipe() {
    insta::assert_yaml_snapshot!(parse(
        r#"
                let id = \x x |> \y y;
                \z (id z |> \m std.plus m 1 |> \m std.minus m 2)
            "#
    )
    .unwrap());
}

#[test]
fn op_update() {
    insta::assert_yaml_snapshot!(parse(
        r#"
                .{
                  a = 1;
                  b = "what";
                  c = .{};
                } // .{
                  b = 50;
                  c = "now";
                }
            "#
    )
    .unwrap());
}

proptest::proptest! {
    #![proptest_config(proptest::test_runner::Config::with_cases(4096))]

    #[test]
    fn doesnt_crash(s in "\\PC*") {
        let _ = parse(&s);
    }
}
