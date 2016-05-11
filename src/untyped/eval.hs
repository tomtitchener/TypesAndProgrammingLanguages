{--
  Evaluation routines for untyped calculus.
--}
module Untyped.Eval(
    eval1
  , EvalStrategy
  , callByValEval
  , fullBetaEval
  , eval
  , evalCommands
  ) where

import Data.Function                 (fix)
import Data.List                     (elemIndices, sort, head, group, intersect, lookup, (\\))
import Data.Tree                     (Tree(..))
import Text.PrettyPrint.Leijen       (pretty)
import Untyped.Data                  (Sym,Term1(..), Term2(..))
import Untyped.Parse                 (Command(..), parseCommands)
import Text.ParserCombinators.Parsec (parse)

-------------------------------------
-- 1:  untyped calculus with names --
-------------------------------------

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
-- >>>pretty (App (Abs "x" (Abs "y" (Var "x"))) (Abs "z" (App (Var "z") (Var "w"))))
-- (λx.λy.x λz.(z w))
--
-- >>>pretty . eval1 $ (App (Abs "x" (Abs "y" (Var "x"))) (Abs "z" (App (Var "z") (Var "w"))))
-- λy.λz.(z w)
--
-- Same as [x ⟼ λz.z w] λy.x
--
-- >>>pretty $ βRed1 "x" (Abs "z" (App (Var "z") (Var "w"))) (Abs "y" (Var "x")) 
-- λy.λz.(z w)
--
-- Avoiding bound variables
--
-- >>>pretty (App (Abs "x" (Abs "x" (Var "x"))) (Var "y"))
-- (λx.λx.x y)
--
-- >>>pretty . eval1 $ (App (Abs "x" (Abs "x" (Var "x"))) (Var "y"))
-- λx.x
--
-- Same as [x ⟼ y] λx.x
--
-- >>>pretty $ βRed1 "x" (Var "y") (Abs "x" (Var "x"))
-- λx.x
--
-- Avoiding variable capture
--
-- >>>pretty $ (App (Abs "x" (Abs "z" (Var "x"))) (Var "z"))
-- (λx.λz.x z)
--
-- >>>pretty . eval1 $ (App (Abs "x" (Abs "z" (Var "x"))) (Var "z"))
-- λz.x
--
-- Same as [x⟼z] λz.x
--
-- >>>pretty $ βRed1 "x" (Var "z") (Abs "z" (Var "x"))
-- λz.x
--
-- but [x ⟼y z] λy.x y (page 71)
--
-- >>>pretty . eval1 $ (App (Abs "x" (Abs "y" (App (Var "x") (Var "y")))) (App (Var "y") (Var "z")))
-- λy.(x y)
--
-- Same as
--
-- >>>pretty $ βRed1 "x" (App (Var "y") (Var "z")) (Abs "y" (App (Var "x") (Var "y")))
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

-- | Convert 'Term1' to pair of context 'Γ' and (unnamed) 'Term2' for free vars ['Sym'],
--   being careful to first check all free vars in Term1 are included in list.
--
--   Be careful with element index!  What I want is distance for symbol "x" from end of list.
--   So if list is ["x","x"] and I'm trying to find the index for "x", then the answer should
--   be 0, because looking backward up list, "x" is first element in list.  List grows from
--   head, starting with reverse of list of globals.  So if list of globals is ["a","b","c"]
--   then reversal is ["c","b","a"] and first Abs for "x" builds ["x","c","b","a"].  Now let's
--   say we have Abs over "x" and I want to know what's the closest "x" looking "up" the list,
--   then it's going to be the one at the start, or index 0.  That way, if there's an Abs that
--   shadows a free var, then I get the index for the Abs, not the one for the free var.  The
--   same way, if there's an inner Abs over "x" that shadows an inner one, then I get the index
--   for the inner Abs, which is what I want--the one that's closest looking back up the list 
--   of Abs and from there up the list of free vars.  The same way, when restoring names, be
--   careful to reverse the list of free vars and then grow the list from the head, so the 
--   indexes in Var2 match up.
-- 
-- >>>pretty $ snd $ removeNames [] (Abs "x" (Var "x"))
-- λ.0
--
-- >>>pretty $ snd $ removeNames [] (Abs "x" (Abs "x" (Var "x")))
-- λ.λ.0
--
-- >>>pretty $ snd $ removeNames ["x"] (Abs "x" (Abs "x" (Var "x")))
-- λ.λ.0
--
-- >>>pretty $ snd $ removeNames ["y"] (Abs "x" (Abs "x" (Var "y")))
-- λ.λ.2
--
-- >>>pretty $ snd $ removeNames ["a","b","c"] (Abs "x" (Var "c"))
-- λ.1
--
-- >>>pretty $ snd $ removeNames ["a","b","c"] (Abs "x" (Var "a"))
-- λ.3
--
-- >>>pretty $ snd $ removeNames ["x"] (Abs "x" (Var "x"))
-- λ.0
--
-- >>>pretty $ snd $ removeNames ["s","z"] (Abs "s" (Abs "z" (Var "z")))
-- λ.λ.0
--
-- >>>pretty $ snd $ removeNames ["a","b","c"] (Abs "s" (Abs "z" (App (Var "s") (App (Var "s") (Var "z")))))
-- λ.λ.(1 (1 0))
--
-- >>>pretty $ snd $ removeNames [] (Abs "m" (Abs "n" (Abs "s" (Abs "z" (App (Var "m") (App (Var "s") (App (Var "n") (App (Var "z") (Var "s")))))))))
-- λ.λ.λ.λ.(3 (1 (2 (0 1))))
--
-- >>>pretty $ snd $ removeNames [] (Abs "f" (App (Abs "x" (App (Var "f") (Abs "y" (App (App (Var "x") (Var "x")) (Var "y"))))) (Abs "x" (App (Var "f") (Abs "y" (App (App (Var "x") (Var "x")) (Var "y")))))))
-- λ.(λ.(1 λ.((1 1) 0)) λ.(1 λ.((1 1) 0)))
--
removeNames :: [Sym] -> Term1 -> (Γ,Term2)
removeNames fvars t
  | sort (fvars `intersect` fvars') /= sort fvars' = error $ "removeNames not all vars free in (" ++ show t ++ "), i.e. " ++ show fvars' ++ ", are included in " ++ show fvars ++ " " ++ show fvars'
  | otherwise = fun (reverse fvars) t
  where
    fvars' = freeVars t
    fun path (Var s)     = (ctx, Var2 i)        where i = head (elemIndices s path); ctx = Node "" []
    fun path (Abs s t)   = (ctx', Abs2 t')      where (ctx, t') = fun (s:path) t; ctx' = Node s [ctx]
    fun path (App t1 t2) = (ctx', App2 t1' t2') where (ctx1, t1') = fun path t1; (ctx2, t2') = fun path t2; ctx' = Node "" [ctx1, ctx2]
    
-- | Convert (unnamed) 'Term2' to 'Term1' for free vars ['Sym'] and context 'Γ'.
--
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
-- >>> (Abs "m" (Abs "n" (Abs "s" (Abs "z" (App (Var "m") (App (Var "s") (App (Var "n") (App (Var "z") (Var "s"))))))))) == restoreNames [] (removeNames [] (Abs "m" (Abs "n" (Abs "s" (Abs "z" (App (Var "m") (App (Var "s") (App (Var "n") (App (Var "z") (Var "s"))))))))))
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
restoreNames syms = fun (reverse syms)
  where
    fun path (_, Var2 i)                      = if i < length path then Var $ path !! i else error $ "fun no var in " ++ show path ++ " for index " ++ show i
    fun path (Node s [ctx],Abs2 t)            = Abs s $ fun (s:path) (ctx, t)
    fun path (Node _ [ctx1, ctx2],App2 t1 t2) = App (fun path (ctx1, t1)) (fun path (ctx2, t2))
    fun path (ctx, t)                         = error $ "restoreNames unrecognized context " ++ show ctx ++ " for term " ++ show t

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
--   for all top level bindings in t, recursively.
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
termSubst 0 (c1, s) t = walk 0 t
  where
    walk :: Int -> (Γ,Term2) -> (Γ,Term2)
    walk c p@(_,                  Var2 i)     = if i == 0 + c then (c1, termShift c s) else p
    walk c (Node x [ctx],         Abs2 t1)    = (Node x [ctx'], Abs2 t2) where (ctx', t2) = walk (c+1) (ctx, t1)
    walk c (Node "" [ctx1, ctx2], App2 t1 t2) = (Node "" [ctx1', ctx2'], App2 t1' t2') where (ctx1', t1') = walk c (ctx1, t1); (ctx2', t2') = walk c (ctx2, t2)
    walk c t = error $ "termSubst walk unexpected arg vals c " ++ show c ++ " t " ++ show t 
termSubst n (_, s) t = error $ "termSubst called with non-zero index " ++ show n ++ " for terms s " ++ show s ++ " and t " ++ show t

-- | Substitute 'Term2 s' in first argument in inner term of 'Term2 t'
--   in second argument.  Implements application of t1 and s--(t1 s)--where
--   t1 is an abstractions and t is the term within abstraction t1 and s
--   is the value to substitute for top-level index 0 in t1.
-- 
--   Shifts s up by one to account for expansion by 1 of binding in
--   top-level term t1, then shift result back down by 1 to compensate.
--
--   Generic code handles reductions for call by value, where s is only ever Abs (val)
--   as well as other strategies, where s may be any Term.
 -- 
βRed2 :: (Γ,Term2) -> (Γ,Term2) -> (Γ,Term2)
βRed2 (c1, s) (Node _ [c2], Abs2 t) = (c3, termShift (-1) t2) where (c3, t2) = termSubst 0 (c1, termShift 1 s) (c2, t)
βRed2 s t = error $ "βRed2 unexpected types for term s " ++ show  s ++ " or t " ++ show t

-- 5.3.6 Exercise [***] Adapt these rules to describe the three other strategies for evaluation--full beta-reduction, normal order, lazy evaluation.

type EvalStrategy = ((Γ,Term2) -> (Γ,Term2))

-- | Call-by-value operational semantics ("Operational Symantics", page 55) for 
--   evaluation of nameless term following Figure 5.3 "Untyped lambda calculus (λ)",
--   details in callByValEval.  Outer wrapper stops at point of recurring to self (fix).
--
--   Call-by-value example, page 55:
--
-- >>> either (putStrLn . show) (\cmds -> mapM_ putStrLn (evalCommands callByValEval cmds)) (parse parseCommands "lambda" "id = λx.x;\n(id (id (λz. id z)));\n")
-- λz.(id z)
--
-- Note:  call by value leaves eval of Church numerals hanging:
--
-- >>> either (putStrLn . show) (\cmds -> mapM_ putStrLn (evalCommands callByValEval cmds)) (parse parseCommands "lambda" "zero = (λs.λz.z);\nscc = (λn.λs.λz.s (n s z));\n(scc zero);\n")
-- λs.λz.(s ((zero s) z))
--
-- Note:  call by value leaves eval of Church numerals hanging:
-- Implements runtime substitution during eval vs. static substitution before eval.
--
-- >>> either (putStrLn . show) (\cmds -> mapM_ putStrLn (evalCommands callByValEval cmds)) (parse parseCommands "lambda" "zero = (λs.λz.z);\nscc = (λn.λs.λz.s (n s z));\n(scc zero);\n")
-- λs.λz.(s ((zero s) z))
--
callByValEval :: EvalStrategy
callByValEval (Node "" [c1, c2], App2 t@(Abs2 _) s@(Abs2 _)) = βRed2  (c2,s) (c1,t)                                                          -- E-AppAbs
callByValEval (Node "" [c1, c2], App2 v1@(Abs2 _) t2)        = (Node "" [c1, c2'], App2  v1  t2') where (c2',t2') = callByValEval (c2,t2)  -- E-App2
callByValEval (Node "" [c1, c2], App2 t1 t2)                 = (Node "" [c1', c2], App2  t1' t2)  where (c1',t1') = callByValEval (c1,t1)  -- E-App1
callByValEval t@_ = t

-- | Full beta reduction following instructions from answer in text (page 502).
--
--  Rules copied from solution:
-- 
--     t1 -> t1'
--  ---------------               E-App1
--  t1 t2 -> t1' t2
--
--     t2 -> t2'
--  ---------------               E-App2
--  t1 t2 -> t1 t2'
--
--  (λx.t12) t2 -> [x ⟼ t2]t12   E-AppAbs
--
--  Note the syntactic category of values is not used.
--
--  But this doesn't work.  Is there something different about "non-deterministic" beta reduction from the example in the text?
--  The eval gives λz.(id z), not λz.z.
--
--  >>> either (putStrLn . show) (\cmds -> mapM_ putStrLn (evalCommands fullBetaEval' cmds)) (parse parseCommands "lambda" "id = (λx.x);\n(id (id (λz. id z)));\n")
--  λz.(id z)
--
-- Maybe traversal by pattern match of type fails due to overlap, for which ghc does give you a warning.
-- The logic behind the evaluation relation in Figure 5-3 for the two rules E-App1 and E-App2 eludes me.
-- The premise require one of the terms be able to take a step, which means the term must be in the shape
-- that matches E-AppAbs.  Yet the logic for call by value just follows the types in the operational
-- semantics.  
--
--       t1 -> t1'
--    ---------------               E-App1
--    t1 t2 -> t1' t2
--
--       t2 -> t2'
--    ---------------               E-App2
--     v1 t2 -> v1 t2'
--
--    (λx.t12) v2 -> [x ⟼ v2]t12   E-AppAbs
--
-- Because the types for (λx.t12) v2, v1 t2, and t1 t2 are unique, they map to traversal by pattern
-- match cleanly.  The thing that's confusing about the premise is that it isn't tested except by
-- failure of eval for e.g. t1 -> t1' or t2 -> t2'.  The implementation just blindly goes ahead
-- and tries to eval t1 assuming the eval will result in an E-AppAbs.  And if it doesn't then the
-- OCaml eval throws and mine answers the same term as before and so eval comes to a stop.
--
-- Reducing experimentally the left or the right terms of an App that isn't a redex and reducing 
-- the other side if the first doesn't reduce doesn't work.  
--
-- Example in text is depth first traversal, reducing from the inside out.  How would you know an
-- implementation like that conformed to the reduction rules?  One strategy is to try reducing 
-- experimentally.  If the LHS doesn't reduce, try the RHS.  But this still leaves you with an
-- outer Abs with an unreduced App inside.  Must be that a mix of reducing on one side and then
-- the other eventually gets you to the bottom level.  Note the description of beta reduction in
-- https://en.wikipedia.org/wiki/Lambda_calculus says "with regards to reduibility, all bets are off."
-- If there were a definition of fully-reduced, then this could be formulated as a search across all
-- traversals L and R until you reached a fully-reduced version.
--
-- What would path for canonical example (id (id (λz. id z))) look like?
--
--   Init  (id (id (λz. id z)))
--   Left  (id (λz. id z))
--   Right (id ( .. )            Nope!  Right side doesn't reduce!  Left side ends with lambda too.
--
--   Init  (id (id (λz. id z)))
--   Right (id (λz. id z))
--   Left  (λz. id z)            Nope!  Need an App to reduce under all rules.
--
-- There's no path following the reduction rules in the answer in the book to get to the
-- same place as he shows in his example.  The reduction rules do not show how to reach a
-- redex within an outer Abs.
-- 
fullBetaEval' :: EvalStrategy
fullBetaEval' (Node "" [c1, c2], App2 t12@(Abs2 _) t2) = βRed2 (c2,t2) (c1,t12)                               -- E-AppAbs
fullBetaEval' (Node "" [c1, c2], App2 t1 t2)           = if t2' /= t2 then (Node "" [c1, c2'], App2  t1  t2') -- E-App2
                                                                      else (Node "" [c1', c2], App2  t1' t2)  -- E-App1
                                                          where
                                                            (c2',t2') = fullBetaEval' (c2,t2)
                                                            (c1',t1') = fullBetaEval' (c1,t1)
fullBetaEval' p = p

-- | Mechanically speaking, what happens if we just provide a way to reduce within an outer
--   Abs?  This works.  But it sure doesn't seem to follow the rules from the answer in the
--   text.  It's hard to see just how this differs from normal order.  Maybe by the time you
--   work through all those rules in the answer in the text you wind up with something that
--   this implementation interprets.  Either way, as this suffices to carry out arithmetic
--   operations on Church numerals.
--
--  >>> either (putStrLn . show) (\cmds -> mapM_ putStrLn (evalCommands fullBetaEval cmds)) (parse parseCommands "lambda" "id = (λx.x);\n(id (id (λz. id z)));\n")
--  λz.z
--
fullBetaEval :: EvalStrategy
fullBetaEval (Node "" [c1, c2], App2 t12@(Abs2 _) t2) = βRed2 (c2,t2) (c1,t12)
fullBetaEval (Node "" [c1, c2], App2 t1 t2)           = (Node "" [c1', c2'], App2 t1' t2') 
                                                          where
                                                            (c1',t1') = fullBetaEval (c1,t1)
                                                            (c2',t2') = fullBetaEval (c2,t2)
fullBetaEval (Node n [c],       Abs2 t)               = (Node n [c'], Abs2 t')
                                                          where
                                                            (c',t') = fullBetaEval (c,t)
fullBetaEval p                                        = p
 
-- | Eval wrapper stops at point of recurring to self (fix).
--
--   TBD: count terms to avoid co-recursion/unfold?
--
eval :: EvalStrategy -> (Γ,Term2) -> (Γ,Term2)
eval strat = fix (\v p@(_,t) -> let p'@(_, t') = strat p in if t == t' then p' else v p')

-----------------------------------------------------
-- 3:  eval Commands including Binder substitution --
-----------------------------------------------------
                   
-- | Symbol lookup for assignment of sym to term, e.g. @id = (λx.x);@.
--
type Env = [(Sym, (Γ,Term2))]

-- | Walk down term in second arg (t) substituting context and 
--   term from env in first arg (e) where index for 'Var2' from term
--   in second arg reaches back beyond depth of binders recorded
--   in depth during walk (d), into free vars recorded by env in
--   first arg.  Keep in mind 'Var2' index to free vars is incremented
--   by depth, so index into free vars in Env has to be decremented
--   by depth, then subtracted from length of environment to index
--   back to front.  Note 'Sym' from pair in 'Env' is discarded here,
--   and must be reconstructed during 'unsubst' below to reconstruct
--   free vars for 'restoreNames'.
-- 
subst :: Env -> (Γ,Term2) -> (Γ,Term2)
subst e = walk 0
  where
    walk d (Node "" [], Var2 i) = if i >= d then snd (e !! (length e - (1 + (i-d)))) else (Node "" [], Var2 i)
    walk d (Node n [c], Abs2 t) = (Node n [c'], Abs2 t') where (c',t') = walk (1+d) (c,t)
    walk d (Node "" [c1,c2], App2 t1 t2) = (Node "" [c1',c2'], App2 t1' t2') where (c1',t1') = walk d (c1,t1); (c2',t2') = walk d (c2,t2)

-- | Map @[(Sym, (Γ,Term2))]@ (e) to @[(Term1, Sym)]@ (e') in first arg
--   for lookup by 'Term1' in second arg, then replace 'Term1' with
--   (@Var Sym@) where lookup succeeds else descend ('unsubst'').
--   Be careful constructing @[(Term1, Sym)]@ from @[(Sym, (Γ,Term2))]@
--   via 'restoreNames' to reconstruct free vars for successive terms
--   in @[(Sym, (Γ,Term2))]@ by building list of free vars from 'Sym'
--   at beginning of 'Env' in first argument (@scanl@).
--
unsubst :: Env -> Term1 -> Term1
unsubst e =
  unsubst' 
  where
    syms = map fst e
    freeVarss = scanl (flip (:)) [head syms] (tail syms)
    e' = map (\(f,(s,(c,t))) -> (restoreNames f (c,t), s)) $ zip freeVarss e
    unsubst' t@(Var _)     = t
    unsubst' t@(Abs s t1)  = maybe t' Var (lookup t e') where t' = Abs s (unsubst' t1)
    unsubst' t@(App t1 t2) = maybe t' Var (lookup t e') where t' = App (unsubst' t1) (unsubst' t2)

-- | Capture TermCommand in list, skip BinderCommand.
termCommand2Term1s :: Command -> [Term1]
termCommand2Term1s (TermCommand t1) = [t1]
termCommand2Term1s _                = []

-- | Append contents for BinderCommand to list, skip TermCommand.
--   Used to fold over BinderCommands in input file, where later
--   BinderCommands may reference names for earlier BinderCommands,
--   i.e. reference but no recursion.  Call to @map fst env@ for
--   first arg to 'removeNames' creates list of free vars for each 
--   successive Term2 from names for previous BinderCommands.
-- 
envAndBinderCommand2Env :: Env -> Command -> Env
envAndBinderCommand2Env env (BinderCommand s t) = env ++ [(s, subst env (removeNames (map fst env) t))]
envAndBinderCommand2Env env _ = env

-- | Given function that implements evaluation strategy in first argument, then 'Env' with global environment of
--   assoc list of 'Sym' to 'Term2' and 'Term1', use 'Sym' from 'Env' for free vars to remove names from 'Term1',
--   creating tuple '(Γ,Term2)', then evaluate the result and restore names using free vars and eval result.
--
evalTerm1 :: EvalStrategy -> Env -> Term1 -> Term1
evalTerm1 strat env =
  unsubst env . restoreNames syms . eval strat . subst env . removeNames syms
  where
    syms = map fst env

-- | Separate binders from terms in '[Command]' and then evaluate all terms using
--   free vars with terms in binders and answer the list of resulting terms.
--    
evalCommands :: EvalStrategy -> [Command] -> [String]
evalCommands strat cmds = map (show . pretty . evalTerm1 strat env) terms
  where
    env  = foldl envAndBinderCommand2Env [] cmds
    terms = concatMap termCommand2Term1s cmds

