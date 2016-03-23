module Lambda where

{--
 Examples from "Types and Programming Languages" Benjamin Pierce.
 1) Untyped lambda calculus with beta reduction "up to renaming of bound variables"
 2) Untyped lambda calculus with de Bruijn presentation and full beta reduction
 --}

import Data.Tuple
import qualified Data.Set as DS
import qualified Data.Map.Strict as DM
import qualified Text.PrettyPrint.Leijen as PP

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
instance PP.Pretty Term1 where
  pretty (Var s)     = PP.string s
  pretty (Abs s t)   = PP.string "λ" PP.<> PP.string s PP.<> PP.string "." PP.<> PP.pretty t
  pretty (App t1 t2) = PP.pretty t1 PP.<> PP.string " " PP.<> PP.pretty t2

freeVars :: Term1 -> DS.Set String
freeVars (Var s)     = DS.singleton s
freeVars (Abs s t)   = freeVars t  `DS.difference` DS.singleton s
freeVars (App t1 t2) = freeVars t1 `DS.union` freeVars t2

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
  | y /= x && DS.notMember y (freeVars s) = Abs y (βRed1 x s t)
  | otherwise                             = Abs y t
βRed1 x s (App t1 t2) = App (βRed1 x s t1) (βRed1 x s t2)

-- | Eval a Term1
-- >>> PP.pretty (App (Abs "x" (Abs "y" (Var "x"))) (Abs "z" (App (Var "z") (Var "w"))))
-- λx.λy.x λz.z w
--
-- >>> PP.pretty . eval1 $ (App (Abs "x" (Abs "y" (Var "x"))) (Abs "z" (App (Var "z") (Var "w"))))
-- λy.λz.z w
--
-- same as [x ⟼ λz.z w] λy.x
-- >>> PP.pretty $ βRed1 "x" (Abs "z" (App (Var "z") (Var "w"))) (Abs "y" (Var "x")) 
-- λy.λz.z w
--
-- Avoiding bound variables
-- >>> PP.pretty (App (Abs "x" (Abs "x" (Var "x"))) (Var "y"))
-- λx.λx.x y
--
-- >>> PP.pretty . eval1 $ (App (Abs "x" (Abs "x" (Var "x"))) (Var "y"))
-- λx.x
--
-- same as [x ⟼ y] λx.x
-- >>> PP.pretty $ βRed1 "x" (Var "y") (Abs "x" (Var "x"))
-- λx.x
--
-- Avoiding variable capture
-- >>> PP.pretty $ (App (Abs "x" (Abs "z" (Var "x"))) (Var "z"))
-- λx.λz.x z
--
-- >>> PP.pretty . eval1 $ (App (Abs "x" (Abs "z" (Var "x"))) (Var "z"))
-- λz.x
--
-- same as [x⟼z] λz.x
-- >>> PP.pretty $ βRed1 "x" (Var "z") (Abs "z" (Var "x"))
-- λz.x
--
-- but [x ⟼y z] λy.x y (page 71)
-- >>> PP.pretty . eval1 $ (App (Abs "x" (Abs "y" (App (Var "x") (Var "y")))) (App (Var "y") (Var "z")))
-- λy.x y
--
-- same as
-- >>> PP.pretty $ βRed1 "x" (App (Var "y") (Var "z")) (Abs "y" (App (Var "x") (Var "y")))
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
  Var2 Int
  | Abs2 Term2
  | App2 Term2 Term2
  deriving (Show, Eq)

-- | Pretty print Term1
--  >>> pretty $ (Abs "x" (Abs "y" (App (Var "x") (Var "y"))))
--  λ.λ.1 0
--
instance PP.Pretty Term2 where
  pretty (Var2 i)     = PP.int i
  pretty (Abs2 t)     = PP.string "λ. " PP.<> PP.pretty t
  pretty (App2 t1 t2) = PP.char '(' PP.<> PP.pretty t1 PP.<> PP.string " " PP.<> PP.pretty t2 PP.<> PP.char ')'

type Γ  = DM.Map String Int
type Γ' = DM.Map Int String

removeNames :: Γ -> Term1 -> (Γ, Term2)
removeNames = fun (-1) where
  fun :: Int -> Γ -> Term1 -> (Γ, Term2)
  fun l ctx (Var s)     = (ctx,  Var2 d)       where d = l - (ctx DM.! s)
  fun l ctx (Abs s t)   = (ctx', Abs2 t')      where (ctx',t') = fun (l+1) (DM.insert s (l+1) ctx) t 
  fun l ctx (App t1 t2) = (ctx', App2 t1' t2') where (ctx1,t1') = fun l ctx t1; (ctx2,t2') = fun l ctx t2; ctx' = ctx1 `DM.union` ctx2

restoreNames :: (Γ, Term2) -> Term1
restoreNames (ctx, t2) = fun (-1) t2 where
  ctx' :: Γ'
  ctx' = (DM.fromList . map swap . DM.toList) ctx
  fun :: Int -> Term2 -> Term1
  fun i (Var2 d)     = Var (ctx' DM.! (i - d))
  fun i (Abs2 t)     = Abs (ctx' DM.! (i+1)) (fun (i+1) t) 
  fun i (App2 t1 t2) = App (fun i t1) (fun i t2)
