{-
  Data types for untyped lambda calculus with and without names.
-}
module Untyped.Data (
    Sym
  , NamedλTerm(..)
  , UnnamedλTerm(..)
  ) where

import Text.PrettyPrint.Leijen ((<>), char, int, string, pretty, Pretty(..))

-------------------------------------
-- 1:  untyped calculus with names --
-------------------------------------

-- | Use a 'String' instead of 'Char' so 'Sym' can be name, e.g. for
--
--   @id = (λx.x);@  NamedλTerm
--
type Sym = String

data NamedλTerm =
  Var Sym
  | Abs Sym NamedλTerm
  | App NamedλTerm NamedλTerm
  deriving (Show, Eq)

-- | Pretty print 'NamedλTerm'
--
--  >>> pretty $ (App (Abs "x"(Var "x")) (Var "x"))
--  (λx.x x)
--
instance Pretty NamedλTerm where
  pretty (Var s)     = string s
  pretty (Abs s t)   = string "λ" <> string s <> string "." <> pretty t
  pretty (App t1 t2) = char '(' <> pretty t1 <> string " " <> pretty t2 <> char ')'

--------------------------------------------
-- 2:  untyped calculus de Bruijn indexes --
--------------------------------------------

-- | Nameless terms.
data UnnamedλTerm =
  Var2 Int
  | Abs2 UnnamedλTerm
  | App2 UnnamedλTerm UnnamedλTerm
  deriving (Show, Eq)

-- | Pretty print 'UnnamedλTerm'
--
--   >>> pretty $ (App2 (Abs2 (Var2 0)) (Var2 0))
--   (λ.0 0)
--
instance Pretty UnnamedλTerm where
 pretty (Var2 i)     = int i
 pretty (Abs2 t)     = string "λ." <> pretty t
 pretty (App2 t1 t2) = char '(' <> pretty t1 <> string " " <>  pretty t2 <> char ')'

