# gardswag

An esoteric language, with a similar origin as
[XTW](https://esolangs.org/wiki/XTW), designed to test
the feasibility of type checking and byte code caching.

(examples are inside `docs/examples`)

(rough language reference)[docs/language_gardswag.txt]

## Types

This version does not support plugins,
but instead might support sockets in the future (tbd).

* `bool`
* `int`
* `string`
* `socket` (tbd)
* tagged unions (create a tagged values using `.<tagname> <expr>`)
* records (create using `.{ <key> = <value>; <inherit_key>; }`)
