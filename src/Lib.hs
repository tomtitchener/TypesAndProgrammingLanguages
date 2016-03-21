module Lib where

{--
 Examples from "Types and Programming Languages" Benjamin Pierce.
 1) Untyped lambda calculus with beta reduction "up to renaming of bound variables"
 2) Untyped lambda calculus with de Bruijn presentation and full beta reduction
 --}

import Data.Set
import Text.PrettyPrint.Leijen

-------
-- 1 --
-------

type Sym = String

data Term1 =
  Var Sym
  | Abs Sym Term1
  | App Term1 Term1
  deriving (Show, Eq)

-- | Pretty print Term1
--  >>> pretty $ (App (Abs "x"(Var "x")) (Var "x"))
--  λx.x x
--
instance Pretty Term1 where
  pretty (Var s)     = string s
  pretty (Abs s t)   = string "λ" <> string s <> string "." <> pretty t
  pretty (App t1 t2) = pretty t1 <> string " " <> pretty t2

freeVars :: Term1 -> Set String
freeVars (Var s)     = singleton s
freeVars (Abs s t)   = freeVars t  `difference` singleton s
freeVars (App t1 t2) = freeVars t1 `union` freeVars t2

-- Beta reduce, "up to renaming of bound variables", pages 69-71.
-- Page 55, "Operational Semantics"
-- "Each step in the computation consists of rewriting an application 
-- whose left-hand component is an abstraction, by substituting the
-- right-hand component for the bound variable in the abstractions'
-- body.  Graphically, we write
--   (λx.t12) t2 → [x ⟼ t2]t12 where [x ⟼ t2]t12 means "the term
-- obtained by replacing all free occurances of x in t12 by t2".
-- beta reduce Term1 t12 for Sym 'x' in Term1 t1
-- Naive: subst x in s with y
-- [x ⟼ s]y => subst x with s in y
βRed1 :: String -> Term1 -> Term1 -> Term1
βRed1 x s (Var y)
  | y == x    = s
  | otherwise = Var y
βRed1 x s (Abs y t)
  | y /= x && notMember y (freeVars s) = Abs y (βRed1 x s t)
  | otherwise                          = Abs y t
βRed1 x s (App t1 t2) = App (βRed1 x s t1) (βRed1 x s t2)

-- | Eval a Term1
-- >>> pretty (App (Abs "x" (Abs "y" (Var "x"))) (Abs "z" (App (Var "z") (Var "w"))))
-- λx.λy.x λz.z w
--
-- >>> pretty . eval1 $ (App (Abs "x" (Abs "y" (Var "x"))) (Abs "z" (App (Var "z") (Var "w"))))
-- λy.λz.z w
--
-- same as [x ⟼ λz.z w] λy.x
-- >>> pretty $ βRed1 "x" (Abs "z" (App (Var "z") (Var "w"))) (Abs "y" (Var "x")) 
-- λy.λz.z w
--
-- Avoiding bound variables
-- >>> pretty (App (Abs "x" (Abs "x" (Var "x"))) (Var "y"))
-- λx.λx.x y
--
-- >>> pretty . eval1 $ (App (Abs "x" (Abs "x" (Var "x"))) (Var "y"))
-- λx.x
--
-- same as [x ⟼ y] λx.x
-- >>> pretty $ βRed1 "x" (Var "y") (Abs "x" (Var "x"))
-- λx.x
--
-- Avoiding variable capture
-- >>> pretty $ (App (Abs "x" (Abs "z" (Var "x"))) (Var "z"))
-- λx.λz.x z
--
-- >>> pretty . eval1 $ (App (Abs "x" (Abs "z" (Var "x"))) (Var "z"))
-- λz.x
--
-- same as [x⟼z] λz.x
-- >>> pretty $ βRed1 "x" (Var "z") (Abs "z" (Var "x"))
-- λz.x
--
-- but [x ⟼y z] λy.x y (page 71)
-- >>> pretty . eval1 $ (App (Abs "x" (Abs "y" (App (Var "x") (Var "y")))) (App (Var "y") (Var "z")))
-- λy.x y
--
-- same as
-- >>> pretty $ βRed1 "x" (App (Var "y") (Var "z")) (Abs "y" (App (Var "x") (Var "y")))
-- λy.x y
--
eval1 :: Term1 -> Term1
eval1 v@(Var _)         = v
eval1 a@(Abs _ _)       = a
eval1 (App (Abs x y) s) = eval1 $ βRed1 x s y
eval1 (App t1 t2)       = App (eval1 t1) (eval1 t2)

-------
-- 2 --
-------

data Term2 =
  Var2 Int Sym
  | Abs2 Int Sym Term2
  | App2 Int Term2 Term2
  deriving (Show, Eq)

indexize :: Int -> Term1 -> Term2
indexize i (Var s)     = Var2 i s
indexize i (Abs s t)   = Abs2 i s (indexize (i + 1) t)
indexize i (App t1 t2) = App2 i (indexize i t1) (indexize i t2)
