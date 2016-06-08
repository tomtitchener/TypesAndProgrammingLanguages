## Lambda:  Lambda calculus in Haskell from Pierce Types and Programming Languages

### Chapters 5, 6, 7.

To build:

    $ stack build

Examples from "Types and Programming Languages" Benjamin Pierce.

  * Untyped lambda calculus with beta reduction "up to renaming of bound variables"
  * Untyped lambda calculus with de Bruijn presentation and full beta reduction

page 88:  "Just because you've implemented something doesn't mean you understand it" (Brian Cantwell Smith).

Doctest:  run by hand as below or:

    $ stack test.

  * doctest -i./src/ ./src/untyped/data.hs 
  * doctest -i./src/ ./src/untyped/parse.hs 
  * doctest -i./src/ ./src/untyped/eval.hs 
  * doctest -i./src/ ./app/Main.hs
