## Lambda:  Lambda calculus in Haskell from Pierce Types and Programming Languages

Examples from "Types and Programming Languages" Benjamin Pierce. 

    page 88:  "Just because you've implemented something doesn't mean you understand it" (Brian Cantwell Smith). 

### Chapters 5, 6, 7. 

  * Untyped lambda calculus with beta reduction "up to renaming of bound variables"
  * Untyped lambda calculus with de Bruijn presentation and full beta reduction

### Chapters 8, 9, 10.

  * Simply typed (Boolean) lambda calculus

To build:

    $ stack build

To test (requires doctest, https://hackage.haskell.org/package/doctest):

    $ stack test 

    typesandprogramminglanguages-0.1.0.0: test (suite: typesandprogramminglanguages-test)

    Examples: 118  Tried: 118  Errors: 0  Failures: 0

    Completed 2 action(s).

(see http://blog.rcook.org/blog/2016/doctest-discover-stack/)

For docs:

    $ stack haddock

