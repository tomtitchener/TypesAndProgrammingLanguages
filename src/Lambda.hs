module Lambda where
{--
 Examples from "Types and Programming Languages" Benjamin Pierce.
 1) Untyped lambda calculus with beta reduction "up to renaming of bound variables"
 2) Untyped lambda calculus with de Bruijn presentation and full beta reduction
 --}

import           Control.Monad                 (liftM)
import           Data.Either                   (either)
import           Data.List                     ((\\), elemIndices, intersect, sort, head, group)
import           Data.Tree                     (Tree(..))
import           Text.ParserCombinators.Parsec (Parser(..), (<|>), (<?>), many1, lower, char, parse, spaces, noneOf, letter, try)
import qualified Text.PrettyPrint.Leijen as PP ((<>), char, int, string, pretty, Pretty(..))

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
--  >>> PP.pretty $ (App (Abs "x"(Var "x")) (Var "x"))
--  (λx.x x)
--
instance PP.Pretty Term1 where
  pretty (Var s)     = PP.string s
  pretty (Abs s t)   = PP.string "λ" PP.<> PP.string s PP.<> PP.string "." PP.<> PP.pretty t
  pretty (App t1 t2) = PP.char '(' PP.<> PP.pretty t1 PP.<> PP.string " " PP.<> PP.pretty t2 PP.<> PP.char ')'

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
-- >>>PP.pretty (App (Abs "x" (Abs "y" (Var "x"))) (Abs "z" (App (Var "z") (Var "w"))))
-- (λx.λy.x λz.(z w))
--
-- >>>PP.pretty . eval1 $ (App (Abs "x" (Abs "y" (Var "x"))) (Abs "z" (App (Var "z") (Var "w"))))
-- λy.λz.(z w)
--
-- same as [x ⟼ λz.z w] λy.x
-- >>>PP.pretty $ βRed1 "x" (Abs "z" (App (Var "z") (Var "w"))) (Abs "y" (Var "x")) 
-- λy.λz.(z w)
--
-- Avoiding bound variables
-- >>>PP.pretty (App (Abs "x" (Abs "x" (Var "x"))) (Var "y"))
-- (λx.λx.x y)
--
-- >>>PP.pretty . eval1 $ (App (Abs "x" (Abs "x" (Var "x"))) (Var "y"))
-- λx.x
--
-- same as [x ⟼ y] λx.x
-- >>>PP.pretty $ βRed1 "x" (Var "y") (Abs "x" (Var "x"))
-- λx.x
--
-- Avoiding variable capture
-- >>>PP.pretty $ (App (Abs "x" (Abs "z" (Var "x"))) (Var "z"))
-- (λx.λz.x z)
--
-- >>>PP.pretty . eval1 $ (App (Abs "x" (Abs "z" (Var "x"))) (Var "z"))
-- λz.x
--
-- same as [x⟼z] λz.x
-- >>>PP.pretty $ βRed1 "x" (Var "z") (Abs "z" (Var "x"))
-- λz.x
--
-- but [x ⟼y z] λy.x y (page 71)
-- >>>PP.pretty . eval1 $ (App (Abs "x" (Abs "y" (App (Var "x") (Var "y")))) (App (Var "y") (Var "z")))
-- λy.(x y)
--
-- same as
-- >>>PP.pretty $ βRed1 "x" (App (Var "y") (Var "z")) (Abs "y" (App (Var "x") (Var "y")))
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
--   >>> PP.pretty $ (App2 (Abs2 (Var2 0)) (Var2 0))
--   (λ.0 0)
--
instance PP.Pretty Term2 where
 pretty (Var2 i)     = PP.int i
 pretty (Abs2 t)     = PP.string "λ." PP.<> PP.pretty t
 pretty (App2 t1 t2) = PP.char '(' PP.<> PP.pretty t1 PP.<> PP.string " " PP.<>  PP.pretty t2 PP.<> PP.char ')'

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
-- >> (Abs "m" (Abs "n" (Abs "s" (Abs "z" (App (Var "m") (App (Var "s") (App (Var "n") (App (Var "z") (Var "s"))))))))) == restoreNames [] (removeNames [] (Abs "m" (Abs "n" (Abs "s" (Abs "z" (App (Var "m") (App (Var "s") (App (Var "n") (App (Var "z") (Var "s"))))))))))
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
restoreNames = fun 
  where
    fun :: [Sym] -> (Γ,Term2) -> Term1
    fun path (_, Var2 i)                      = Var $ path !! i
    fun path (Node s [ctx],Abs2 t)            = Abs s $ fun (s:path) (ctx, t)
    fun path (Node _ [ctx1, ctx2],App2 t1 t2) = App (fun path (ctx1, t1)) (fun path (ctx2, t2))
    fun path (ctx, t)                         = error $ "restoreNames unrecognized context " ++ show ctx ++ " for term " ++ show t

----------------------------
-- Eval of nameless terms --
----------------------------

-- [1 ⟼ s] (λ.2) maps to [x ⟼ s] (λy.x) assuming 1 is index of x in the outer context.
-- Replace sym for 1 with s in term t.  Note match despite 1 vs. 2!
-- "When a substitution goes under λ-abstraction, (as in above), the context in which the
-- substitution is taking place becomes one variable longer than the original; we need to
-- increment the indices of the free variables in s so that they keep referring to the same
-- names in the new context as they did before.  But we have to do this carefully:  we can't
-- just shift every variable index in s up by one, because this would also shift bound
-- variables within s.  For example, if s = 2 (λ.0) (i.e., s = z (λw.w), assuming 2 is the
-- index for z in the outer context), we need to shift the 2 but not the 0.  The shifting
-- function below takes a "cutoff" parameter c that controls which variables should be shifted.
-- It starts at 0 (meaning all variables should be shifted) and gets incremented by 1 every
-- time the shifting function goes through a binder.  So, when calculating "shift from c to
-- d for t", we know that the term t comes from inside c-many binders in the original argument
-- to "shift from 0 to d".  Therefore, all identifiers k < c in t are bound in the original
-- argument and should not be shifted, while identifiers k >= c are free and should be
-- shifted." (Page 79).
    
-- | Shift indexes for free Vars in Term t by offset d.  Counts binders in 
--   subterms to identify free Vars that need to be shifted by binding
--   depth d.  Answers same Term as input with indexes for all free Vars 
--   shifted by offset d.  Relies on "removeNames" bumping indexes for free 
--   vars successively with each additional binding, which happens automatically
--   as path that starts from free vars becomes one longer with each binding.
--   Avoids shifting of bound vars by counting binding depth in c, starting at 0.
--   Note d may be negative, to shift back down a level, e.g. for outermost call.
--   Shift of x only "carries" into Var in term when index for Var is greater 
--   than the binding depth, counting from 0.
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
    walk c t'@(Var2 i) = if i >= c then Var2 (i+d) else t'
    walk c (Abs2 t1) = Abs2 $ walk (c+1) t1
    walk c (App2 t1 t2) = App2 (walk c t1) (walk c t2)

-- | Substitute s for index j in term t where j is always 0, 
--   effectively, substitute s for top level binding in t.
--   Descend subterms in t counting up a binding level for
--   each abstraction.  At terminal Var(s) in t, if Var index
--   i equals binding depth, substitute with s, being careful
--   to shift s by binding depth.
--
--  termSubst 0 (Abs2 (Var2 0)) (Abs2 (Var2 0))
-- 
termSubst :: Int -> Term2 -> Term2 -> Term2
termSubst 0 s@(Abs2 _) t@(Abs2 _) = walk 0 t
  where
    walk :: Int -> Term2 -> Term2
    walk c t'@(Var2 i)  = if i == 0 + c then termShift c s else t'
    walk c (Abs2 t1)    = Abs2 $ walk (c+1) t1
    walk c (App2 t1 t2) = App2 (walk c t1) (walk c t2)
termSubst 0 s t = error $ "termSubst called with top level terms other than Abs2, s " ++ show s ++ " or t " ++ show t
termSubst n s t = error $ "termSubst called with non-zero index " ++ show n ++ " for terms s " ++ show s ++ " and t " ++ show t
    
-- | Substitute s in t.  Called for application of t1
--   and s--(t1 s)--where both t1 and s are abstractions
--   and t is the term within abstraction t1.  s is value
--   to substitute for top-level index 0 in t1.  Shift s
--   up by one to account for expansion by 1 of binding
--   in top-level term t1, then shift result back down
--   by 1 to compensate.
βRed2 :: Term2 -> Term2 -> Term2
βRed2 s@(Abs2 _) t@(Abs2 _) = termShift (-1) $ termSubst 0 (termShift 1 s) t
βRed2 s t = error $ "βRed2 unexpected types for term s " ++ show  s ++ " or t " ++ show t

eval2' :: Term2 -> Term2
eval2' (App2 t1@(Abs2 t12) v2@(Abs2 _)) = βRed2 v2 t12
eval2' (App2 v1@(Abs2 _) t2)            = App2 v1  t2' where t2' = eval2' t2
eval2' (App2 t1 t2)                     = App2 t1' t2  where t1' = eval2' t1
eval2' t@_ = t

eval2 :: Term2 -> Term2
eval2 t1 = if t1 == t2 then t2 else eval2 t2 where t2 = eval2 t1

-----------
-- Parse --
-----------

--  Factoring out left recursion was tricky, and I wound up cribbing from this:
--    http://stackoverflow.com/questions/18555390/lambda-calculus-grammar-llr

-- | Id can't have λ, dot, paren, or space, lower seems to catch λ.
--   Parse of id is distinct because Abs needs it plan as a Sym but
--   Var wraps it.
-- 
-- >>> parse parseId "test" "x"
-- Right "x"
--
-- >>> parse parseId "test" "id"
-- Right "id"
--
parseId :: Parser Sym
parseId = many1 (noneOf "λ.() ") >>= \i -> spaces >> return i

-- | Var just wraps id.
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
parseAbs :: Parser Term1
parseAbs = char 'λ' >> parseId >>= \v -> char '.' >> spaces >> parseExpr >>= \e -> return $ Abs v e

-- | One or more in a row, nested left.
--
-- >>> parse parseApp "test" "x y"
-- Right (App (Var "x") (Var "y"))
--
parseApp :: Parser Term1
parseApp = liftM (foldl1 App) (many1 parseTerm)

-- | Parse according to parentheses.
--
-- >>> parse parseParenExpr "test" "(a(b(c d)))"
-- Right (App (Var "a") (App (Var "b") (App (Var "c") (Var "d"))))
--
-- >>> parse parseParenExpr "test" "(((a b)c)d)"
-- Right (App (App (App (Var "a") (Var "b")) (Var "c")) (Var "d"))
-- 
parseParenExpr :: Parser Term1
parseParenExpr = char '(' >> parseExpr >>= \e -> char ')' >> return e

-- | Allows expressions that aren't redexes.
--
-- >>> parse parseExpr "lambda" "λy.λz.z w x"
-- Right (Abs "y" (Abs "z" (App (App (Var "z") (Var "w")) (Var "x"))))
-- 
-- >>> either (putStrLn . show) (putStrLn . show . PP.pretty) $ parse parseExpr "lambda" "λy.λz.z w x"
-- λy.λz.((z w) x)
-- 
parseExpr :: Parser Term1
parseExpr = parseAbs <|> parseApp <?> "expr"

parseTerm :: Parser Term1
parseTerm = parseVar <|> parseParenExpr <?> "term"

evalStr :: String -> String
evalStr s = either show right (parse parseTerm "lambda" s)
  where
    right t1 = show . PP.pretty $ restoreNames fctx (bctx, eval2 t2)
      where
        fctx       = freeVars t1
        (bctx, t2) = removeNames fctx t1
    
