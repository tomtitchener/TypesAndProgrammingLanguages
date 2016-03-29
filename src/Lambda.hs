module Lambda where

{--
 Examples from "Types and Programming Languages" Benjamin Pierce.
 1) Untyped lambda calculus with beta reduction "up to renaming of bound variables"
 2) Untyped lambda calculus with de Bruijn presentation and full beta reduction
 --}

import Data.List                 ((\\), elemIndices, intersect, sort, head, group)
import Data.Tree                 (Tree(..))
import Text.PrettyPrint.Leijen   ((<>), char, int, string, pretty, Pretty(..))

-------
-- 1 --
-------

type Sym = String

-- | Named terms.
data Term1 =
  Var Sym
  | Abs Sym Term1
  | App Term1 Term1
  deriving (Show, Eq)

-- | Pretty print Term1
--  >>> pretty $ (App (Abs "x"(Var "x")) (Var "x"))
--  (λx.x x)
--
instance Pretty Term1 where
  pretty (Var s)     = string s
  pretty (Abs s t)   = string "λ" <> string s <> string "." <> pretty t
  pretty (App t1 t2) = char '(' <> pretty t1 <> string " " <> pretty t2 <> char ')'

unique :: (Eq a, Ord a) => [a] -> [a]
unique = map head . group . sort

freeVars :: Term1 -> [String]
freeVars (Var s)     = [s]
freeVars (Abs s t)   = freeVars t \\ [s]
freeVars (App t1 t2) = unique $ freeVars t1 ++ freeVars t2

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
  | y /= x && notElem y (freeVars s) = Abs y (βRed1 x s t)
  | otherwise                             = Abs y t
βRed1 x s (App t1 t2) = App (βRed1 x s t1) (βRed1 x s t2)

-- | Eval a Term1
-- >>>pretty (App (Abs "x" (Abs "y" (Var "x"))) (Abs "z" (App (Var "z") (Var "w"))))
-- (λx.λy.x λz.(z w))
--
-- >>>pretty . eval1 $ (App (Abs "x" (Abs "y" (Var "x"))) (Abs "z" (App (Var "z") (Var "w"))))
-- λy.λz.(z w)
--
-- same as [x ⟼ λz.z w] λy.x
-- >>>pretty $ βRed1 "x" (Abs "z" (App (Var "z") (Var "w"))) (Abs "y" (Var "x")) 
-- λy.λz.(z w)
--
-- Avoiding bound variables
-- >>>pretty (App (Abs "x" (Abs "x" (Var "x"))) (Var "y"))
-- (λx.λx.x y)
--
-- >>>pretty . eval1 $ (App (Abs "x" (Abs "x" (Var "x"))) (Var "y"))
-- λx.x
--
-- same as [x ⟼ y] λx.x
-- >>>pretty $ βRed1 "x" (Var "y") (Abs "x" (Var "x"))
-- λx.x
--
-- Avoiding variable capture
-- >>>pretty $ (App (Abs "x" (Abs "z" (Var "x"))) (Var "z"))
-- (λx.λz.x z)
--
-- >>>pretty . eval1 $ (App (Abs "x" (Abs "z" (Var "x"))) (Var "z"))
-- λz.x
--
-- same as [x⟼z] λz.x
-- >>>pretty $ βRed1 "x" (Var "z") (Abs "z" (Var "x"))
-- λz.x
--
-- but [x ⟼y z] λy.x y (page 71)
-- >>>pretty . eval1 $ (App (Abs "x" (Abs "y" (App (Var "x") (Var "y")))) (App (Var "y") (Var "z")))
-- λy.(x y)
--
-- same as
-- >>>pretty $ βRed1 "x" (App (Var "y") (Var "z")) (Abs "y" (App (Var "x") (Var "y")))
-- λy.(x y)
--
eval1 :: Term1 -> Term1
eval1 v@(Var _)         = v
eval1 a@(Abs _ _)       = a
eval1 (App (Abs x y) s) = eval1 $ βRed1 x s y
eval1 (App t1 t2)       = App (eval1 t1) (eval1 t2)

-------
-- 2 --
-------

-- | Nameless terms.
data Term2 =
  Var2 Int
  | Abs2 Term2
  | App2 Term2 Term2
  deriving (Show, Eq)

-- | Pretty print Term2
--   >>> pretty $ (App2 (Abs2 (Var2 0)) (Var2 0))
--   (λ.0 0)
--
instance Pretty Term2 where
 pretty (Var2 i)     = int i
 pretty (Abs2 t)     = string "λ." <> pretty t
 pretty (App2 t1 t2) = char '(' <> pretty t1 <> string " " <>  pretty t2 <> char ')'

-- | Name context in text is Gamma, but as just an ordered list where indexes match order.
--   Consequence is need to "... make up names for for the variables bound by abstractions
--   in t" (6.1.5).  That's because naming contexts diverge with App, where left and right
--   terms might have bindings with same names.  Instead of list, use a tree with max of
--   two-way split to parallel App.  Traverse different paths under restore to regain
--   unique naming context.
type Γ  = Tree Sym

-- | Appends tree in second arg to end of straight line tree in first arg.
--   Used a) to append bound context to end of free context, b) to build
--   up new context for an outer Abs over an inner context.
--   Fails if tree in first arg has more than one branch.
--
--   >>> appendCtxts (Node {rootLabel = "l", subForest = [Node {rootLabel = "m", subForest = [Node {rootLabel = "n", subForest = [Node {rootLabel = "", subForest = []}]}]}]}) (Node {rootLabel = "a", subForest = [Node {rootLabel = "b", subForest = [Node {rootLabel = "c", subForest = [Node {rootLabel = "", subForest = []}]}]}]})
--   Node {rootLabel = "l", subForest = [Node {rootLabel = "m", subForest = [Node {rootLabel = "n", subForest = [Node {rootLabel = "a", subForest = [Node {rootLabel = "b", subForest = [Node {rootLabel = "c", subForest = [Node {rootLabel = "", subForest = []}]}]}]}]}]}]}
--
appendCtxts :: Γ -> Γ -> Γ
appendCtxts (Node "" [])    bctx               = bctx
appendCtxts (Node s [])     (Node s' ctxs)  = Node s [Node s' ctxs]
appendCtxts (Node s [ctx])  bctx               = Node s [appendCtxts ctx bctx]
appendCtxts n@_ dst                               = error $ "appendCtxts unrecognized source " ++ show n ++ " for dst " ++ show dst

-- | Convert Term1 to Term2 for context
--
-- >>>pretty $ snd $ removeNames [] (Abs "x" (Var "x"))
-- λ.0
--
-- >>>pretty $ snd $ removeNames [] (Abs "s" (Abs "z" (Var "z")))
-- λ.λ.0
--
-- >>>pretty $ snd $ removeNames [] (Abs "s" (Abs "z" (App (Var "s") (App (Var "s") (Var "z")))))
-- λ.λ.(1 (1 0))
--
-- >>>pretty $ snd $ removeNames [] (Abs "m" (Abs "n" (Abs "s" (Abs "z" (App (Var "m") (App (Var "s") (App (Var "n") (App (Var "z") (Var "s")))))))))
-- λ.λ.λ.λ.(3 (1 (2 (0 1))))
--
-- >>>pretty $ snd $ removeNames [] (Abs "f" (App (Abs "x" (App (Var "f") (Abs "y" (App (App (Var "x") (Var "x")) (Var "y"))))) (Abs "x" (App (Var "f") (Abs "y" (App (App (Var "x") (Var "x")) (Var "y")))))))
-- λ.(λ.(1 λ.((1 1) 0)) λ.(1 λ.((1 1) 0)))
--
removeNames' :: [Sym] -> Term1 -> (Γ,Term2)
removeNames' path (Var s)     = (ctx,  Var2 i)       where i = last $ elemIndices s path; ctx = Node "" [] -- need to safeguard elemIndices returns [] e.g. free var not in list.
removeNames' path (Abs s t)   = (ctx', Abs2 t')      where (ctx,t') = removeNames' (s:path) t; ctx' = appendCtxts (Node s []) ctx
removeNames' path (App t1 t2) = (ctx', App2 t1' t2') where (ctx1, t1') = removeNames' path t1; (ctx2, t2') = removeNames' path t2; ctx' = Node "" [ctx1, ctx2]
                                                    
removeNames :: [Sym] -> Term1 -> (Γ,Term2)
removeNames fvars t1
  | fvars `intersect` fvars' /= fvars' = error $ "removeNames not all vars free in " ++ show t1 ++ "" ++ show fvars' ++ " are included in " ++ show fvars
  | otherwise = (bctx, t2)
  where
    fvars'     = freeVars t1
    (bctx, t2) = removeNames' fvars t1
                                                    
-- | Convert Term2 to Term1 for context
-- >>> (pretty . restoreNames []) $ removeNames [] (Abs "x" (Var "x"))
-- λx.x
--
-- >>> (pretty . restoreNames []) $ removeNames [] (Abs "s" (Abs "z" (Var "z")))
-- λs.λz.z
--
-- >>> (pretty . restoreNames []) $ removeNames [] (Abs "s" (Abs "z" (App (Var "s") (App (Var "s") (Var "z")))))
-- λs.λz.(s (s z))
--
-- >>> (pretty . restoreNames []) $ removeNames [] (Abs "m" (Abs "n" (Abs "s" (Abs "z" (App (Var "m") (App (Var "s") (App (Var "n") (App (Var "z") (Var "s")))))))))
-- λm.λn.λs.λz.(m (s (n (z s))))
--
-- >>> (pretty . restoreNames []) $ removeNames [] (Abs "f" (App (Abs "x" (App (Var "f") (Abs "y" (App (App (Var "x") (Var "x")) (Var "y"))))) (Abs "g" (App (Var "f") (Abs "h" (App (App (Var "g") (Var "g")) (Var "h")))))))
-- λf.(λx.(f λy.((x x) y)) λg.(f λh.((g g) h)))
--
-- >>> (Abs "x" (Var "x")) == restoreNames [] (removeNames [] (Abs "x" (Var "x")))
-- True
--
-- >>> (Abs "s" (Abs "z" (Var "z"))) == restoreNames [] (removeNames [] (Abs "s" (Abs "z" (Var "z"))))
-- True
--    
-- >>> (Abs "s" (Abs "z" (App (Var "s") (App (Var "s") (Var "z"))))) == restoreNames [] (removeNames [] (Abs "s" (Abs "z" (App (Var "s") (App (Var "s") (Var "z"))))))
-- True
--
-- >> (Abs "m" (Abs "n" (Abs "s" (Abs "z" (App (Var "m") (App (Var "s") (App (Var "n") (App (Var "z") (Var "s"))))))))) == restoreNames [] (removeNames [] (Abs "m" (Abs "n" (Abs "s" (Abs "z" (App (Var "m") (App (Var "s") (App (Var "n") (App (Var "z") (Var "s"))))))))))
-- True
--    
-- >>> (Abs "f" (App (Abs "x" (App (Var "f") (Abs "y" (App (App (Var "x") (Var "x")) (Var "y"))))) (Abs "g" (App (Var "f") (Abs "h" (App (App (Var "g") (Var "g")) (Var "h"))))))) == restoreNames [] (removeNames [] (Abs "f" (App (Abs "x" (App (Var "f") (Abs "y" (App (App (Var "x") (Var "x")) (Var "y"))))) (Abs "g" (App (Var "f") (Abs "h" (App (App (Var "g") (Var "g")) (Var "h"))))))))
-- True
--
-- >>> (pretty . (restoreNames ["z"])) $ removeNames ["z"] (Abs "x" (Var "z"))
-- λx.z
--
-- >>> (pretty . (restoreNames ["g"])) $ removeNames ["g"] (Abs "s" (Abs "z" (Var "g")))
-- λs.λz.g
--
-- >>> (pretty . (restoreNames ["m", "n"])) $ removeNames ["m", "n"] (Abs "s" (Abs "z" (App (Var "s") (App (Var "m") (Var "n")))))
-- λs.λz.(s (m n))
--
-- >>> (pretty . restoreNames ["a","b","c"]) $ removeNames ["a","b","c"] (Abs "m" (Abs "n" (Abs "s" (Abs "z" (App (Var "a") (App (Var "b") (App (Var "n") (App (Var "z") (Var "c")))))))))
-- λm.λn.λs.λz.(a (b (n (z c))))
--    
restoreNames :: [Sym] -> (Γ,Term2) -> Term1
restoreNames = fun 
  where
    fun :: [Sym] -> (Γ,Term2) -> Term1
    fun path (_, Var2 i)                      = Var $ path !! i
    fun path (Node s [ctx],Abs2 t)            = Abs s $ fun (s:path) (ctx, t)
    fun path (Node _ [ctx1, ctx2],App2 t1 t2) = App (fun path (ctx1, t1)) (fun path (ctx2, t2))
    fun path (ctx, t)                         = error $ "restoreNames unrecognized context " ++ show ctx ++ " for term " ++ show t
