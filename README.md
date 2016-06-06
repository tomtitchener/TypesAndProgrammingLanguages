## Lambda:  Lambda calculus in Haskell from Pierce Types and Programming Languages

### Chapters 5, 6, 7.

Examples from "Types and Programming Languages" Benjamin Pierce.

  * Untyped lambda calculus with beta reduction "up to renaming of bound variables"
  * Untyped lambda calculus with de Bruijn presentation and full beta reduction

TBD:

  * testing/validation
    - consume a file of definitions (maybe just a a list of text strings with a definition per line)
    - validate a series of lambda expressions and expected results
    - convert single file of lamba definitions and expressions into files that validate e.g. pairs, bools, numerals, recursion, etc.

page 88:  "Just because you've implemented something doesn't mean you understand it" (Brian Cantwell Smith).

Doctest:

  * doctest -i./src/ ./src/untyped/data.hs 
  * doctest -i./src/ ./src/untyped/parse.hs 
  * doctest -i./src/ ./src/untyped/eval.hs 
  * doctest -i./src/ ./app/Main.hs
