{--

 Examples from "Types and Programming Languages" Benjamin Pierce.
 1) Untyped lambda calculus with beta reduction "up to renaming of bound variables"
 2) Untyped lambda calculus with de Bruijn presentation and full beta reduction

 TBD:

   * readability
     - resolve terms back to symbols after eval so e.g. (id id) turns into id.
   * doctest over untyped lambda calc examples in text
     - church booleans
     - pairs
     - church numerals
     - operations over church numerals
     - lists
     - real bool and nat
     - recursion
     - semantics:  full beta reduction, normal-order, lazy
   * housekeeping
     - split into multiple files in an untyped folder:  data.hs, parse.hs, eval.hs.
     - map Term1 and Term2 and eval and reduce to Data.Functor.Foldable
       (https://hackage.haskell.org/package/recursion-schemes) following http://dev.stephendiehl.com/hask/#recursion-schemes

NB quote, page 88:  "Just because you've implemented something doesn't mean you understand it" (Brian Cantwell Smith).

--}

module Untyped where

import           Control.Monad                 (liftM, mapM_, void)
import           Data.Either                   (either)
import           Data.List                     (elemIndices, sort, head, group, intersect, lookup, (\\))
import           Data.Tree                     (Tree(..))
import           System.Environment            (getArgs)
import           Text.ParserCombinators.Parsec (Parser(..), (<|>), (<?>), many, many1, endBy, sepBy, lower, char, eof, parse, spaces, newline, noneOf, letter, try, parseFromFile, choice)
import qualified Text.PrettyPrint.Leijen as PP ((<>), char, int, string, pretty, Pretty(..))

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
--  >>> PP.pretty $ (App (Abs "x"(Var "x")) (Var "x"))
--  (λx.x x)
--
instance PP.Pretty Term1 where
  pretty (Var s)     = PP.string s
  pretty (Abs s t)   = PP.string "λ" PP.<> PP.string s PP.<> PP.string "." PP.<> PP.pretty t
  pretty (App t1 t2) = PP.char '(' PP.<> PP.pretty t1 PP.<> PP.string " " PP.<> PP.pretty t2 PP.<> PP.char ')'

-- | Sort input list and answer sorted order less duplicates.
--
-- >>> unique [1,1,5,5,3,2,10,10,22,22]
-- [1,2,3,5,10,22]
--
unique :: (Eq a, Ord a) => [a] -> [a]
unique = map head . group . sort

-- | Answer list of of free variables in 'Term1'
--
-- >>> freeVars (App (Var "a") (Var "b"))
-- ["a","b"]
--
freeVars :: Term1 -> [Sym]
freeVars (Var s)     = [s]
freeVars (Abs s t)   = freeVars t \\ [s]
freeVars (App t1 t2) = unique $ freeVars t1 ++ freeVars t2

-- | Beta reduce, "up to renaming of bound variables", pages 69-71.
--
--   @
--   "Each step in the computation consists of rewriting an application 
--   whose left-hand component is an abstraction, by substituting the
--   right-hand component for the bound variable in the abstractions'
--   body.
-- 
--   Graphically, we write
--
--     (λx.t12) t2 → [x ⟼ t2]t12 where [x ⟼ t2]t12
--
--   means "the term obtained by replacing all free occurances of x in t12 by t2".
--   @
--
--   Page 55, "Operational Semantics"
--
--   beta reduce 'Term1' t12 for 'Sym' 'x' in 'Term1' t1
--
--   Naive: subst x in s with y
--
--   @
--   [x⟼s]y => subst x with s in y
--   @
--
βRed1 :: String -> Term1 -> Term1 -> Term1
βRed1 x s (Var y)
  | y == x    = s
  | otherwise = Var y
βRed1 x s (Abs y t)
  | y /= x && notElem y (freeVars s) = Abs y (βRed1 x s t)
  | otherwise                          = Abs y t
βRed1 x s (App t1 t2) = App (βRed1 x s t1) (βRed1 x s t2)

-- | Eval a 'Term1' "up to renaming of bound variables"
-- 
--   TBD:  naive recursion on structure of Term1.  What are operational semantics?
--   Show example of failure of variable capture.
--
-- >>>PP.pretty (App (Abs "x" (Abs "y" (Var "x"))) (Abs "z" (App (Var "z") (Var "w"))))
-- (λx.λy.x λz.(z w))
--
-- >>>PP.pretty . eval1 $ (App (Abs "x" (Abs "y" (Var "x"))) (Abs "z" (App (Var "z") (Var "w"))))
-- λy.λz.(z w)
--
-- Same as [x ⟼ λz.z w] λy.x
--
-- >>>PP.pretty $ βRed1 "x" (Abs "z" (App (Var "z") (Var "w"))) (Abs "y" (Var "x")) 
-- λy.λz.(z w)
--
-- Avoiding bound variables
--
-- >>>PP.pretty (App (Abs "x" (Abs "x" (Var "x"))) (Var "y"))
-- (λx.λx.x y)
--
-- >>>PP.pretty . eval1 $ (App (Abs "x" (Abs "x" (Var "x"))) (Var "y"))
-- λx.x
--
-- Same as [x ⟼ y] λx.x
--
-- >>>PP.pretty $ βRed1 "x" (Var "y") (Abs "x" (Var "x"))
-- λx.x
--
-- Avoiding variable capture
--
-- >>>PP.pretty $ (App (Abs "x" (Abs "z" (Var "x"))) (Var "z"))
-- (λx.λz.x z)
--
-- >>>PP.pretty . eval1 $ (App (Abs "x" (Abs "z" (Var "x"))) (Var "z"))
-- λz.x
--
-- Same as [x⟼z] λz.x
--
-- >>>PP.pretty $ βRed1 "x" (Var "z") (Abs "z" (Var "x"))
-- λz.x
--
-- but [x ⟼y z] λy.x y (page 71)
--
-- >>>PP.pretty . eval1 $ (App (Abs "x" (Abs "y" (App (Var "x") (Var "y")))) (App (Var "y") (Var "z")))
-- λy.(x y)
--
-- Same as
--
-- >>>PP.pretty $ βRed1 "x" (App (Var "y") (Var "z")) (Abs "y" (App (Var "x") (Var "y")))
-- λy.(x y)
--
eval1 :: Term1 -> Term1
eval1 v@(Var _)         = v
eval1 a@(Abs _ _)       = a
eval1 (App (Abs x y) s) = eval1 $ βRed1 x s y
eval1 (App t1 t2)       = App (eval1 t1) (eval1 t2)

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
--   >>> PP.pretty $ (App2 (Abs2 (Var2 0)) (Var2 0))
--   (λ.0 0)
--
instance PP.Pretty Term2 where
 pretty (Var2 i)     = PP.int i
 pretty (Abs2 t)     = PP.string "λ." PP.<> PP.pretty t
 pretty (App2 t1 t2) = PP.char '(' PP.<> PP.pretty t1 PP.<> PP.string " " PP.<>  PP.pretty t2 PP.<> PP.char ')'

-- | Name context in text is 'Γ', but if context is just an ordered list 
--   where indexes match order (as in text), then consequence is need to
--
--   @
--   "... make up names for for the variables bound by abstractions in t."
--   @
--
--   (6.1.5).
-- 
--   That's because naming contexts diverge with 'App', where left and right
--   terms might have bindings with same names.
--
--   Instead of list, use a tree with max of two-way split to parallel terms
--   in 'App'
--   Traverse different paths under restore to regain unique naming context.
--
type Γ = Tree Sym

-- | Add first context to beginning of second context.  Context itself is a
--   tree, so splicing means traversing first tree to all leaf nodes and swapping
--   second tree for empty node at the end.
--
-- >>> consCtxts (Node "z" [Node "" []]) (Node "" [Node "a" [Node "" []], Node "b" [Node "" []]])
-- Node {rootLabel = "z", subForest = [Node {rootLabel = "", subForest = [Node {rootLabel = "a", subForest = [Node {rootLabel = "", subForest = []}]},Node {rootLabel = "b", subForest = [Node {rootLabel = "", subForest = []}]}]}]}
--
-- >>> consCtxts (Node "" [Node "a" [Node "" []], Node "b" [Node "" []]]) (Node "z" [Node "" []]) 
-- Node {rootLabel = "", subForest = [Node {rootLabel = "a", subForest = [Node {rootLabel = "z", subForest = [Node {rootLabel = "", subForest = []}]}]},Node {rootLabel = "b", subForest = [Node {rootLabel = "z", subForest = [Node {rootLabel = "", subForest = []}]}]}]}
--
-- >>> consCtxts (Node {rootLabel = "l", subForest = [Node {rootLabel = "m", subForest = [Node {rootLabel = "n", subForest = [Node {rootLabel = "", subForest = []}]}]}]}) (Node {rootLabel = "a", subForest = [Node {rootLabel = "b", subForest = [Node {rootLabel = "c", subForest = [Node {rootLabel = "", subForest = []}]}]}]})
-- Node {rootLabel = "l", subForest = [Node {rootLabel = "m", subForest = [Node {rootLabel = "n", subForest = [Node {rootLabel = "a", subForest = [Node {rootLabel = "b", subForest = [Node {rootLabel = "c", subForest = [Node {rootLabel = "", subForest = []}]}]}]}]}]}]}
--
consCtxts :: Γ -> Γ -> Γ
consCtxts a b = walk a
  where
    walk (Node "" [])      = b
    walk (Node x  [])      = Node x [b]
    walk (Node x  [c])     = Node x [walk c]
    walk (Node "" [c1,c2]) = Node "" [walk c1, walk c2]
    walk n = error $ "consCtxts walk unexpected arg " ++ show n

-- | Safeguarded replacement of Term1 with pair <naming context, Term2> 
--   where test of free vars guarantees @elemIndices s path@ does not
--   answer empty list.
removeNames' :: [Sym] -> Term1 -> (Γ,Term2)
removeNames' path (Var s) = (ctx, Var2 i)            where i = last (elemIndices s path); ctx = Node "" []
removeNames' path (Abs s t)   = (ctx', Abs2 t')      where (ctx,t') = removeNames' (s:path) t; ctx' = consCtxts (Node s []) ctx
removeNames' path (App t1 t2) = (ctx', App2 t1' t2') where (ctx1, t1') = removeNames' path t1; (ctx2, t2') = removeNames' path t2; ctx' = Node "" [ctx1, ctx2]
                                                    
-- | Convert 'Term1' to pair of context 'Γ' and (unnamed) 'Term2' for free vars ['Sym'],
--   being careful to first check all free vars in Term1 are included in list.
--
-- >>>PP.pretty $ snd $ removeNames [] (Abs "x" (Var "x"))
-- λ.0
--
-- >>>PP.pretty $ snd $ removeNames [] (Abs "s" (Abs "z" (Var "z")))
-- λ.λ.0
--
-- >>>PP.pretty $ snd $ removeNames [] (Abs "s" (Abs "z" (App (Var "s") (App (Var "s") (Var "z")))))
-- λ.λ.(1 (1 0))
--
-- >>>PP.pretty $ snd $ removeNames [] (Abs "m" (Abs "n" (Abs "s" (Abs "z" (App (Var "m") (App (Var "s") (App (Var "n") (App (Var "z") (Var "s")))))))))
-- λ.λ.λ.λ.(3 (1 (2 (0 1))))
--
-- >>>PP.pretty $ snd $ removeNames [] (Abs "f" (App (Abs "x" (App (Var "f") (Abs "y" (App (App (Var "x") (Var "x")) (Var "y"))))) (Abs "x" (App (Var "f") (Abs "y" (App (App (Var "x") (Var "x")) (Var "y")))))))
-- λ.(λ.(1 λ.((1 1) 0)) λ.(1 λ.((1 1) 0)))
--
removeNames :: [Sym] -> Term1 -> (Γ,Term2)
removeNames fvars t1
  | fvars `intersect` fvars' /= fvars' = error $ "removeNames not all vars free in " ++ show t1 ++ "" ++ show fvars' ++ " are included in " ++ show fvars
  | otherwise = (bctx, t2)
  where
    fvars'     = freeVars t1
    (bctx, t2) = removeNames' fvars t1
                                                    
-- | Convert (unnamed) 'Term2' to 'Term1' for free vars ['Sym'] and context 'Γ'.
--
-- >>> (PP.pretty . restoreNames []) $ removeNames [] (Abs "x" (Var "x"))
-- λx.x
--
-- >>> (PP.pretty . restoreNames []) $ removeNames [] (Abs "s" (Abs "z" (Var "z")))
-- λs.λz.z
--
-- >>> (PP.pretty . restoreNames []) $ removeNames [] (Abs "s" (Abs "z" (App (Var "s") (App (Var "s") (Var "z")))))
-- λs.λz.(s (s z))
--
-- >>> (PP.pretty . restoreNames []) $ removeNames [] (Abs "m" (Abs "n" (Abs "s" (Abs "z" (App (Var "m") (App (Var "s") (App (Var "n") (App (Var "z") (Var "s")))))))))
-- λm.λn.λs.λz.(m (s (n (z s))))
--
-- >>> (PP.pretty . restoreNames []) $ removeNames [] (Abs "f" (App (Abs "x" (App (Var "f") (Abs "y" (App (App (Var "x") (Var "x")) (Var "y"))))) (Abs "g" (App (Var "f") (Abs "h" (App (App (Var "g") (Var "g")) (Var "h")))))))
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
-- >>> (Abs "m" (Abs "n" (Abs "s" (Abs "z" (App (Var "m") (App (Var "s") (App (Var "n") (App (Var "z") (Var "s"))))))))) == restoreNames [] (removeNames [] (Abs "m" (Abs "n" (Abs "s" (Abs "z" (App (Var "m") (App (Var "s") (App (Var "n") (App (Var "z") (Var "s"))))))))))
-- True
--    
-- >>> (Abs "f" (App (Abs "x" (App (Var "f") (Abs "y" (App (App (Var "x") (Var "x")) (Var "y"))))) (Abs "g" (App (Var "f") (Abs "h" (App (App (Var "g") (Var "g")) (Var "h"))))))) == restoreNames [] (removeNames [] (Abs "f" (App (Abs "x" (App (Var "f") (Abs "y" (App (App (Var "x") (Var "x")) (Var "y"))))) (Abs "g" (App (Var "f") (Abs "h" (App (App (Var "g") (Var "g")) (Var "h"))))))))
-- True
--
-- >>> (PP.pretty . (restoreNames ["z"])) $ removeNames ["z"] (Abs "x" (Var "z"))
-- λx.z
--
-- >>> (PP.pretty . (restoreNames ["g"])) $ removeNames ["g"] (Abs "s" (Abs "z" (Var "g")))
-- λs.λz.g
--
-- >>> (PP.pretty . (restoreNames ["m", "n"])) $ removeNames ["m", "n"] (Abs "s" (Abs "z" (App (Var "s") (App (Var "m") (Var "n")))))
-- λs.λz.(s (m n))
--
-- >>> (PP.pretty . restoreNames ["a","b","c"]) $ removeNames ["a","b","c"] (Abs "m" (Abs "n" (Abs "s" (Abs "z" (App (Var "a") (App (Var "b") (App (Var "n") (App (Var "z") (Var "c")))))))))
-- λm.λn.λs.λz.(a (b (n (z c))))
--
restoreNames :: [Sym] -> (Γ,Term2) -> Term1
restoreNames path (_, Var2 i)                      = if i < length path then Var $ path !! i else error $ "restoreNames no var in " ++ show path ++ " for index " ++ show i
restoreNames path (Node s [ctx],Abs2 t)            = Abs s $ restoreNames (s:path) (ctx, t)
restoreNames path (Node _ [ctx1, ctx2],App2 t1 t2) = App (restoreNames path (ctx1, t1)) (restoreNames path (ctx2, t2))
restoreNames path (ctx, t)                         = error $ "restoreNames unrecognized context " ++ show ctx ++ " for term " ++ show t

----------------------------
-- Eval of nameless terms --
----------------------------

-- | Shift indexes for free 'Var's in 'Term' t by offset d.  Counts binders 
--   in subterms to identify free 'Var's that need to be shifted by binding
--   depth d.  Answers same 'Term' as input with indexes for all free 'Var's 
--   shifted by offset d.
--
--   Relies on 'removeNames' bumping indexes for free vars successively with each
--   additional binding, which happens automatically as path that starts from free
--   vars becomes one longer with each binding.
--
--   Avoids shifting of bound vars by counting binding depth in c, starting at 0.
--
--   Note index in first argument may be negative, to shift back down a level, e.g. 
--   for outermost call.  Shift of x only "carries" into 'Var' in term when index 
--   for 'Var' is greater than the binding depth, counting from 0.
--
-- >>> termShift 1 (Abs2 (Var2 0))
-- Abs2 (Var2 0)
--
-- >>> termShift 1 (Abs2 (Var2 1))
-- Abs2 (Var2 2)
--
-- >>> termShift 1 (Abs2 (Abs2 (Abs2 (Var2 2))))
-- Abs2 (Abs2 (Abs2 (Var2 2)))
--    
-- >>> termShift 1 (Abs2 (Abs2 (Abs2 (Var2 3))))
-- Abs2 (Abs2 (Abs2 (Var2 4)))
--    
termShift :: Int -> Term2 -> Term2
termShift d = walk 0
  where
    walk :: Int -> Term2 -> Term2
    walk c (Var2 i)     = if i >= c then Var2 (i+d) else Var2 i
    walk c (Abs2 t1)    = Abs2 $ walk (c+1) t1
    walk c (App2 t1 t2) = App2 (walk c t1) (walk c t2)

-- | Substitute s for index j in term t where j is always 0,
--   and s is always an abstraction, effectively, substitute s
--   for top level binding in t.
--    
--   Descend subterms in t counting up a binding level for
--   each abstraction.  At terminal 'Var'(s) in t, if 'Var' index
--   i equals binding depth, substitute with s, being careful
--   to shift s by binding depth.
--
--  >>> snd $ termSubst 0 (Node "x" [Node "" []], Abs2 (Var2 0)) (Node "x" [Node "" []], Abs2 (Var2 0))
--  Abs2 (Var2 0)
-- 
termSubst :: Int -> (Γ,Term2) -> (Γ,Term2) -> (Γ,Term2)
termSubst 0 (c1, s@(Abs2 _)) t = walk 0 t
  where
    walk :: Int -> (Γ,Term2) -> (Γ,Term2)
    walk c (c2, t'@(Var2 i))                  = if i == 0 + c then (c2, termShift c s) else (c2, t')
    walk c (Node x [ctx], Abs2 t1)            = (Node x [ctx'], Abs2 t2) where (ctx', t2) = walk (c+1) (ctx, t1)
    walk c (Node "" [ctx1, ctx2], App2 t1 t2) = (Node "" [ctx1', ctx2'], App2 t1' t2') where (ctx1', t1') = walk c (ctx1, t1); (ctx2', t2') = walk c (ctx2, t2)
    walk c t = error $ "termSubst walk unexpected arg vals c " ++ show c ++ " t " ++ show t 
termSubst 0 (_, s) t = error $ "termSubst called with top level terms other than Abs2, s " ++ show s 
termSubst n (_, s) t = error $ "termSubst called with non-zero index " ++ show n ++ " for terms s " ++ show s ++ " and t " ++ show t
    
-- | Substitute 'Term2 s' in first argument in inner term of 'Term2 t'
--   in second argument.  Implements application of t1 and s--(t1 s)--where
--   both t1 and s are abstractions and t is the term within abstraction t1.
--   s is value to substitute for top-level index 0 in t1.
-- 
--   Shifts s up by one to account for expansion by 1 of binding in
--   top-level term t1, then shift result back down by 1 to compensate.
--
βRed2 :: (Γ,Term2) -> (Γ,Term2) -> (Γ,Term2)
βRed2 (c1, s@(Abs2 _)) (c2, t) = (c3, termShift (-1) t2) where (c3, t2) = termSubst 0 (c1, termShift 1 s) (c2, t)
βRed2 s t = error $ "βRed2 unexpected types for term s " ++ show  s ++ " or t " ++ show t

-- | Environment is an assoc list of symbols with context and 'Term2' tuples.
-- 
--   Initialized in file with syntax e.g. @id = λx.x;@ below:
--
--   @
--   id = λx.x;
--   (id id);
--   @
-- 
type Env2 = [(Sym, (Γ,Term2))]

-- | At leaf of 'Term2', check for match of name for 'Var2' in
--   list of free vars in 'Env2'.  If there's a match, substitute
--   'Term2' from 'Env2' for 'Var2' and splice context for 'Term2'
--   from 'Env2'.  Relies on 'TermShift' to increase de Bruijn 
--   indexes for bound vars and not free vars.
-- 
subst :: Env2 -> (Γ,Term2) -> (Γ,Term2)
subst es p@(c, v@(Var2 i)) = if i < length es then (c'', t) else p where (_, (c', t)) = es !! i; c'' = consCtxts c c'
subst _ p                  = p

eval2' :: Env2 -> (Γ,Term2) -> (Γ,Term2)
eval2' e (Node _ [c1, c2], App2 (Abs2 t) s@(Abs2 _)) = (c', t') where (c', t')            = βRed2  (c1,s) (c2,t)        -- E-AppAbs
eval2' e (c,               App2 v1@(Abs2 _) t2)      = (c', App2  v1  t2') where (c',t2') = eval2' e $ subst e (c,t2)   -- E-App2
eval2' e (c,               App2 t1 t2)               = (c', App2  t1' t2)  where (c',t1') = eval2' e $ subst e (c,t1)   -- E-App1
eval2' e t@_ = t

-- | Call-by-value operational semantics ("Operational Symantics", page 55) for 
--   evaluation of nameless term following Figure 5.3 "Untyped lambda calculus (λ)".
--   Stops at point of recurring to self.
--
--   Carry contexts for 1) free variables 'Env2' and 2) names for terms in 'Term2' (Γ)
--   through evaluation of input 'Term2' to resolve terminal 'Var2' to 'Term2' for free
--   vars and to update context for names during 'βRed2'.
-- 
--   TBD: "un"substitute back to Env2 symbols from concluding reduction,
--   search t2 in p'@(_, t2) for matches against RHS of env, replacing
--   matches with symbol from env.
--
--   TBD: count terms to avoid co-recursion/unfold.
--
eval2 :: Env2 -> (Γ,Term2) -> (Γ,Term2)
eval2 env p@(_, t1) = if t1 == t2 then p' else eval2 env p' where p'@(_, t2) = eval2' env p

-----------
-- Parse --
-----------

-- | Id can't have λ, dot, parens, or space, because just 'lower' seems 
--   to catch λ.  Parse of id is distinct because 'Abs' needs it plan as 
--   a 'Sym' but 'Var' wraps it.
-- 
-- >>> parse parseId "test" "x"
-- Right "x"
--
-- >>> parse parseId "test" "id"
-- Right "id"
--
parseId :: Parser Sym
parseId = many1 (noneOf "λ.(); ")

-- | 'Var' just wraps id.
-- 
-- >>> parse parseVar "test" "x"
-- Right (Var "x")
--
-- >>> parse parseVar "test" "id"
-- Right (Var "id")
--
parseVar :: Parser Term1
parseVar = liftM Var parseId

-- | Space(s) after var or id is optional
-- 
-- >>> parse parseAbs "test" "λx.x"
-- Right (Abs "x" (Var "x"))
--
-- >>> parse parseAbs "test" "λx. x"
-- Right (Abs "x" (Var "x"))
--
parseAbs :: Parser Term1
parseAbs = char 'λ' >> parseId >>= \v -> spaces >> char '.' >> spaces >> parseTerm >>= \e -> return $ Abs v e

-- | One or more in a row, nested left.
--
-- >>> parse parseAppTerm "test" "x y"
-- Right (App (Var "x") (Var "y"))
--
-- >>> parse parseAppTerm "test" "x y z"
-- Right (App (App (Var "x") (Var "y")) (Var "z"))
--
parseAppTerm :: Parser Term1
parseAppTerm = liftM (foldl1 App) (many1 parseATerm)

-- | Parse according to parentheses.
--
-- >>> parse parseATerm "test" "(a(b(c d)))"
-- Right (App (Var "a") (App (Var "b") (App (Var "c") (Var "d"))))
--
-- >>> parse parseATerm "test" "(((a b)c)d)"
-- Right (App (App (App (Var "a") (Var "b")) (Var "c")) (Var "d"))
-- 
parseATerm :: Parser Term1
parseATerm = (char '(' >> parseTerm >>= \e -> char ')' >> spaces >> return e) <|> (parseVar >>= \v -> spaces >> return v)

-- | Parse a Term 
-- 
-- >>> parse parseTerm "lambda" "(λx.x)y"
-- Right (App (Abs "x" (Var "x")) (Var "y"))
--
-- >>> parse parseTerm "lambda" "λx.x y"
-- Right (Abs "x" (App (Var "x") (Var "y")))
--
parseTerm :: Parser Term1
parseTerm = parseAppTerm <|> parseAbs

data Command = TermCommand Term1 | BinderCommand Sym Term1 deriving (Eq, Show)

parseTermCommand :: Parser Command
parseTermCommand = liftM TermCommand parseTerm <?> "term command"

parseBinderCommand :: Parser Command
parseBinderCommand = parseId >>= \i -> spaces >> char '=' >> spaces >> parseTerm >>= \t -> return (BinderCommand i t) <?> "binder command"

parseCommand :: Parser Command
parseCommand = parseBinderCommand <|> parseTermCommand <?> "command"

parseCommands :: Parser [Command]
parseCommands = parseCommand `endBy` choice [eof, void newline, char ';' >> void newline]

-- | Evaluator for named lambda expression.  Convert to unnamed.  Evaluate.  Restore names.  Pretty print.
--  
-- >>> either (PP.string . show) (\t -> PP.pretty (restoreNames [] (eval2 [] (removeNames [] t)))) (parse parseTerm "lambda" "((λx.x) (λx.x))")
-- λx.x
--
evalStr :: String -> String
evalStr s = either show right $ parse parseTerm "lambda" s
  where
    right t1 = show . PP.pretty $ restoreNames fctx $ eval2 [] (removeNames fctx t1)
      where
        fctx = freeVars t1

termCommand2Term1s :: Command -> [Term1]
termCommand2Term1s (TermCommand t1) = [t1]
termCommand2Term1s _                = []

binderCommand2Env2 :: Command -> Env2
binderCommand2Env2 (BinderCommand s t) = [(s, removeNames [] t)]
binderCommand2Env2 _                   = []

evalTerm1 ::  Env2 -> Term1 -> String
evalTerm1 env t1 = show . PP.pretty $ restoreNames syms $ eval2 env (removeNames syms t1)
  where
    syms = map fst env

evalCommands :: [Command] -> [String]
evalCommands cmds = map (evalTerm1 env) t1s
  where
    env  = concatMap binderCommand2Env2 cmds
    t1s  = concatMap termCommand2Term1s cmds

-- | Parser for file with list of lines, converted to [Command], which then gets
--   split into environment with assoc list of sym with term and a list of terms
--   to evaluate in the context of the environment, e.g.
--
--   @    
--   id = λx.x;
--   (id id);
--   @
--    
-- >>> either (putStrLn . show) (\cmds -> mapM_ putStrLn (evalCommands cmds)) (parse parseCommands "lambda" "id = λx.x;\n(id id);\n")
-- λx.x
--
readFile' :: String -> IO ()
readFile' fName = do
  cmds  <- parseFromFile parseCommands fName
  either print (mapM_ putStrLn . evalCommands) cmds
  
readFile :: IO ()
readFile = getArgs >>= \[fName,_] -> readFile' fName