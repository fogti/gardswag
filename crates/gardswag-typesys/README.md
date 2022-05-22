### references / links

this implementation is primarily derived from:
  http://dev.stephendiehl.com/fun/006_hindley_milner.html
(huge shout-out to Stephen Diehl for the Haskell implementation,
  which was imo much easier to understand
  than the usually used Ocaml implementations)
Author of primary reference: Stephen Diehl
License: [CC BY-NC-SA](https://creativecommons.org/licenses/by-nc-sa/4.0/)

the book "Types and Programming Languages" by "Benjamin C. Pierce"
was used as reference, suggestion and for cross-checking
of some extensions to the implementation mentioned above
  https://www.cis.upenn.edu/~bcpierce/tapl/

the idea for implementating partial records
(which can probably be regarded as some kind of row polymorphism)
was inspired by:
  https://www.haskellforall.com/2022/03/the-hard-part-of-type-checking-nix.html

anonymous tagged union types were inspired by my own unfinished Zaias project:
  https://git.ytrizja.de/zseri/zaias/src/branch/main2/docs/example.txt

channels were inspired by their usage in Go and Erlang.
