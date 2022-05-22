# gardswag

An esoteric language, with a similar origin as
[XTW](https://esolangs.org/wiki/XTW), designed to test
the feasibility of type checking and byte code caching.

(examples are inside `docs/examples`)

[rough language reference](docs/language_gardswag.txt)

## License

The most important code is licensed under [Apache 2.0](https://www.apache.org/licenses/LICENSE-2.0) and [CC BY-NC-SA 4.0](https://creativecommons.org/licenses/by-nc-sa/4.0/).
This causes this to be partially non-free (
 because commercial usage of the most interesting parts not allowed;
 but should this program ever gain a compiler, the output artifacts
 won't be not affected by this, and can be used commercially when the
 license of the associated/input source code allows this
).
Utilitiy crates are licensed under Apache 2.0, and if particularly simple,
also under MIT.

## Running the interpreter

The interpreter (and the rest of the code base) is written in [Rust](https://www.rust-lang.org/),
and can be built using `cargo`, e.g.
```
RUST_LOG=debug cargo run --bin gardswag -- --file docs/examples/fibo.gds --mode run
```

Using the `--mode` argument it is possible to switch between
* `check`, which runs just the parser + type checker
* `run`, which then also (tries to) execute the code

It uses the `tracing` library for logging of debugging information,
which is useful in case that tpye checking goes wrong or such.
The reported information can be adjusted using the `RUST_LOG`
environment variable.

## Types

This version does not support plugins,
but instead might support sockets in the future (tbd).

* `bool`
* `int`
* `string`
* `socket` (tbd)
* tagged unions (create a tagged values using `.<tagname> <expr>`)
* records (create using `.{ <key> = <value>; <inherit_key>; }`)

## TODO

* union partialify operator
  (turns an open or closed tagged union into a new open one)
  used to avoid "cloning matches"
  (`match x | .a y => .a y | .b y => .b y (* ... *)`)
* recursive types,
  to make compile-time unbounded data structures possible
  (where we only know the size/depth at runtime)
* sockets or plugins
* lambdas with linearity spec for the argument (0, 1, `*`)
