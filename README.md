# gardswag

An esoteric language, with a similar origin as
[XTW](https://esolangs.org/wiki/XTW), designed to test
the feasibility of type checking and byte code caching.

(examples are inside `docs/examples`)

## Types

This version does not support plugins, but instead
supports sockets.

* `bool`
* `int`
* `string`
* `socket`

## Syntax

```
function call:    FUNCTION_NAME(ARGUMENTS...)
method call:      OBJECT.METHOD(ARGUMENTS...)
```

## Standard library

* `std.stdio :: socket`
* `std.tycast :: A -> B`
* `std.tyeq :: A -> B -> bool`
