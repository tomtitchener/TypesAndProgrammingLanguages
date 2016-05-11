{-
  Data types for untyped lambda calculus with and without names.
-}
module Untyped.Data (
    Sym
  , Term1(..)
  , Term2(..)
  ) where

import Text.PrettyPrint.Leijen ((<>), char, int, string, pretty, Pretty(..))

-------------------------------------
-- 1:  untyped calculus with names --
-------------------------------------

-- | Use a 'String' instead of 'Char' so 'Sym' can be name, e.g. for
--
--   @id = (λx.x);@
--
type Sym = String

data Term1 =
  Var Sym
  | Abs Sym Term1
  | App Term1 Term1
  deriving (Show, Eq)

-- | Pretty print 'Term1'
--
--  >>> pretty $ (App (Abs "x"(Var "x")) (Var "x"))
--  (λx.x x)
--
instance Pretty Term1 where
  pretty (Var s)     = string s
  pretty (Abs s t)   = string "λ" <> string s <> string "." <> pretty t
  pretty (App t1 t2) = char '(' <> pretty t1 <> string " " <> pretty t2 <> char ')'

--------------------------------------------
-- 2:  untyped calculus de Bruijn indexes --
--------------------------------------------

-- | Nameless terms.
data Term2 =
  Var2 Int
  | Abs2 Term2
  | App2 Term2 Term2
  deriving (Show, Eq)

-- | Pretty print 'Term2'
--
--   >>> pretty $ (App2 (Abs2 (Var2 0)) (Var2 0))
--   (λ.0 0)
--
instance Pretty Term2 where
 pretty (Var2 i)     = int i
 pretty (Abs2 t)     = string "λ." <> pretty t
 pretty (App2 t1 t2) = char '(' <> pretty t1 <> string " " <>  pretty t2 <> char ')'

