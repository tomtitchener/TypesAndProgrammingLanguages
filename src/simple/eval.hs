{--
  Evaluation routines for simply typed lambda calculus.
--}

module Simple.Eval(
  evalCommands
  ) where

import Control.Monad                 (foldM, liftM)
import Data.Either
import Data.Either.Utils             (maybeToEither)
import Data.Function                 (fix)
import Data.List                     (elemIndices, sort, head, group, intersect, lookup, (\\), find)
import Data.Maybe                    (fromJust, mapMaybe)
import Data.Tree                     (Tree(..), flatten)
import Simple.Data                   (Sym, Ty(..),NamedTerm(..), UnnamedTerm(..))
import Simple.Parse                  (Command(..), parseCommands)
import Text.ParserCombinators.Parsec (parse)
import Text.PrettyPrint.Leijen       (pretty)

-- | Sort input list and answer sorted order less duplicates.
--
-- >>> unique [1,1,5,5,3,2,10,10,22,22]
-- [1,2,3,5,10,22]
--
unique :: (Eq a, Ord a) => [a] -> [a]
unique = map head . group . sort

-- | Answer list of of free variables in 'NamedTerm'
--
-- >>> freeVars (NTmApp (NTmVar "a") (NTmVar "b"))
-- ["a","b"]
--
freeVars :: NamedTerm -> [Sym]
freeVars NTmTrue          = []
freeVars NTmFalse         = []
freeVars (NTmIf t1 t2 t3) = unique $ freeVars t1 ++ freeVars t2 ++ freeVars t3
freeVars (NTmVar s)       = [s]
freeVars (NTmAbs s _ t)   = freeVars t \\ [s]
freeVars (NTmApp t1 t2)   = unique $ freeVars t1 ++ freeVars t2

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
type Γ = Tree (Sym, Maybe Ty) -- TBD, infer type for all syms?

---------------------------
-- Checking Simple Types --
---------------------------

-- | Type conctext is an association list of type by symbol.
-- 
type Γ' = [(Sym, Ty)]

-- | Test type is bool
--
testTyBool :: Ty -> Either String Ty
testTyBool TyBool = Right TyBool
testTyBool ty     = Left $ "type is not Bool " ++ show ty

-- | Test type is arrow.
--
testTyArr :: Ty -> Either String Ty
testTyArr ty@(TyArrow _ _) = Right ty
testTyArr ty               = Left $ "type " ++ show ty ++ " is not TyArr"

-- | Test types are equal
--
testTysEqual :: Ty -> Ty -> Either String Ty
testTysEqual ty1 ty2 = if ty1 == ty2 then Right ty1 else Left $ "unequal types " ++ show ty1 ++ " and " ++ show ty2

-- | Validate first arg is arrow type and that first type in arrow is equal to type of second arg.
--   Answer second type in arrow, which will be return type for app.
--
testTyArg :: Ty -> Ty -> Either String Ty
testTyArg arr@(TyArrow fr to) fr' = if fr == fr' then Right to else Left $"arg type " ++ show fr' ++ " not equal to input for arrow type " ++ show arr
testTyArg ty _ = Left $ "testTyArg first arg " ++ show ty ++ " not arrow"

-- | Search for sym in context
--
checkIsSym :: Sym -> Γ' -> Either String Ty
checkIsSym s ctx = maybeToEither ("missing sym for var " ++ show s ++ " in context " ++ show ctx) (lookup s ctx) 

-- | Given context, walk term answering either error string about type mismatch somewhere in term or type of term.
--
-- >>> checkTypes [] NTmTrue
-- Right TyBool
--
-- >>> checkTypes [] NTmFalse
-- Right TyBool
--
-- >>> checkTypes [] (NTmIf NTmTrue NTmTrue NTmFalse)
-- Right TyBool
--
-- >>> checkTypes [] (NTmAbs "x" TyBool (NTmVar "x"))
-- Right (TyArrow TyBool TyBool)
--
-- >>> checkTypes [] (NTmApp (NTmAbs "x" TyBool (NTmVar "x")) NTmTrue)
-- Right TyBool
--
-- >>> checkTypes [] (NTmApp (NTmAbs "x" (TyArrow TyBool TyBool) (NTmVar "x")) (NTmAbs "x" TyBool (NTmVar "x")))
-- Right (TyArrow TyBool TyBool)
--
checkTypes :: Γ' -> NamedTerm -> Either String Ty
checkTypes _    NTmTrue         = Right TyBool
checkTypes _    NTmFalse        = Right TyBool
checkTypes ctx (NTmIf t1 t2 t3) = checkTypes ctx t1 >>= testTyBool >> checkTypes ctx t2 >>= \ty2 -> checkTypes ctx t3 >>= \ty3 -> testTysEqual ty2 ty3
checkTypes ctx (NTmVar s)       = checkIsSym s ctx 
checkTypes ctx (NTmAbs s fr t)  = liftM (TyArrow fr) (checkTypes ctx' t) where ctx' = (s, fr):ctx
checkTypes ctx (NTmApp t1 t2)   = checkTypes ctx t1 >>= testTyArr >>= \arr -> checkTypes ctx t2 >>= testTyArg arr

-- | Convert 'NamedTerm' to pair of context 'Γ' and (unnamed) 'UnnamedTerm' for free vars ['Sym'],
--   being careful to first check all free vars in NamedTerm are included in list.
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
--   indexes in UTmVar match up.
-- 
-- >>>pretty $ snd $ removeNames [] (NTmAbs "x" TyBool (NTmVar "x"))
-- λ.0
--
-- >>>pretty $ snd $ removeNames [] (NTmAbs "x" TyBool (NTmAbs "x" TyBool (NTmVar "x")))
-- λ.λ.0
--
-- >>>pretty $ snd $ removeNames ["x"] (NTmAbs "x" TyBool (NTmAbs "x" TyBool (NTmVar "x")))
-- λ.λ.0
--
-- >>>pretty $ snd $ removeNames ["y"] (NTmAbs "x" TyBool (NTmAbs "x" TyBool (NTmVar "y")))
-- λ.λ.2
--
-- >>>pretty $ snd $ removeNames ["a","b","c"] (NTmAbs "x" TyBool (NTmVar "c"))
-- λ.1
--
-- >>>pretty $ snd $ removeNames ["a","b","c"] (NTmAbs "x" TyBool (NTmVar "a"))
-- λ.3
--
-- >>>pretty $ snd $ removeNames ["x"] (NTmAbs "x" TyBool (NTmVar "x"))
-- λ.0
--
-- >>>pretty $ snd $ removeNames ["s","z"] (NTmAbs "s" TyBool (NTmAbs "z" TyBool (NTmVar "z")))
-- λ.λ.0
--
-- >>>pretty $ snd $ removeNames ["a","b","c"] (NTmAbs "s" TyBool (NTmAbs "z" TyBool (NTmApp (NTmVar "s") (NTmApp (NTmVar "s") (NTmVar "z")))))
-- λ.λ.(1 (1 0))
--
-- >>>pretty $ snd $ removeNames [] (NTmAbs "m" TyBool (NTmAbs "n" TyBool (NTmAbs "s" TyBool (NTmAbs "z" TyBool (NTmApp (NTmVar "m") (NTmApp (NTmVar "s") (NTmApp (NTmVar "n") (NTmApp (NTmVar "z") (NTmVar "s")))))))))
-- λ.λ.λ.λ.(3 (1 (2 (0 1))))
--
-- >>>pretty $ snd $ removeNames [] (NTmAbs "f" TyBool (NTmApp (NTmAbs "x" TyBool (NTmApp (NTmVar "f") (NTmAbs "y" TyBool (NTmApp (NTmApp (NTmVar "x") (NTmVar "x")) (NTmVar "y"))))) (NTmAbs "x" TyBool (NTmApp (NTmVar "f") (NTmAbs "y" TyBool (NTmApp (NTmApp (NTmVar "x") (NTmVar "x")) (NTmVar "y")))))))
-- λ.(λ.(1 λ.((1 1) 0)) λ.(1 λ.((1 1) 0)))
--
removeNames :: [Sym] -> NamedTerm -> (Γ, UnnamedTerm)
removeNames fvars t
  | sort (fvars `intersect` fvars') /= sort fvars' = error $ "removeNames not all vars free in (" ++ show t ++ "), i.e. " ++ show fvars' ++ ", are included in " ++ show fvars ++ " " ++ show fvars'
  | otherwise = fun (reverse fvars) t
  where
    fvars' = freeVars t
    fun path NTmTrue          = (ctx, UTmTrue)           where ctx = Node ("",Nothing) []
    fun path NTmFalse         = (ctx, UTmFalse)          where ctx = Node ("",Nothing) []
    fun path (NTmIf t1 t2 t3) = (ctx, UTmIf t1' t2' t3') where (ctx1, t1') = fun path t1; (ctx2, t2') = fun path t2; (ctx3, t3') = fun path t3; ctx = Node ("",Nothing) [ctx1, ctx2, ctx3]
    fun path (NTmVar s)       = (ctx, UTmVar i)          where i = head (elemIndices s path); ctx = Node ("",Nothing) []
    fun path (NTmAbs s ty t)  = (ctx, UTmAbs t')         where (ctx', t') = fun (s:path) t; ctx = Node (s,Just ty) [ctx']
    fun path (NTmApp t1 t2)   = (ctx, UTmApp t1' t2')    where (ctx1, t1') = fun path t1; (ctx2, t2') = fun path t2; ctx = Node ("",Nothing) [ctx1, ctx2]
                                                               
-- | Convert (unnamed) 'UnnamedTerm' to 'NamedTerm' for free vars ['Sym'] and context 'Γ'.
--
-- >>> (pretty . restoreNames []) $ removeNames [] (NTmAbs "x" TyBool (NTmVar "x"))
-- λx:Bool.x
--
restoreNames :: [Sym] -> (Γ,UnnamedTerm) -> NamedTerm
restoreNames syms = fun (reverse syms)
  where
    fun path (_, UTmTrue)                                = NTmTrue
    fun path (_, UTmFalse)                               = NTmFalse
    fun path (Node _ [ctx1, ctx2, ctx3], UTmIf t1 t2 t3) = NTmIf (fun path (ctx1, t1)) (fun path (ctx2, t2)) (fun path (ctx3, t3))
    fun path (_, UTmVar i)                               = if i < length path then NTmVar $ path !! i else error $ "fun no var in " ++ show path ++ " for index " ++ show i
    fun path (Node (s,ty) [ctx], UTmAbs t)               = NTmAbs s (fromJust ty) $ fun (s:path) (ctx, t)
    fun path (Node _ [ctx1, ctx2], UTmApp t1 t2)         = NTmApp (fun path (ctx1, t1)) (fun path (ctx2, t2))
    fun path (ctx, t)                                    = error $ "restoreNames unrecognized context " ++ show ctx ++ " for term " ++ show t
    
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
-- >>> termShift 1 (UTmAbs (UTmVar 0))
-- UTmAbs (UTmVar 0)
--
-- >>> termShift 1 (UTmAbs (UTmVar 1))
-- UTmAbs (UTmVar 2)
--
-- >>> termShift 1 (UTmAbs (UTmAbs (UTmAbs (UTmVar 2))))
-- UTmAbs (UTmAbs (UTmAbs (UTmVar 2)))
--    
-- >>> termShift 1 (UTmAbs (UTmAbs (UTmAbs (UTmVar 3))))
-- UTmAbs (UTmAbs (UTmAbs (UTmVar 4)))
--    
termShift :: Int -> UnnamedTerm -> UnnamedTerm
termShift d = walk 0
  where
    walk :: Int -> UnnamedTerm -> UnnamedTerm
    walk c UTmTrue          = UTmTrue
    walk c UTmFalse         = UTmFalse
    walk c (UTmIf t1 t2 t3) = UTmIf (walk c t1) (walk c t2) (walk c t3)
    walk c (UTmVar i)       = if i >= c then UTmVar (i+d) else UTmVar i
    walk c (UTmAbs t1)      = UTmAbs $ walk (c+1) t1
    walk c (UTmApp t1 t2)   = UTmApp (walk c t1) (walk c t2)

-- | Substitute s for index j in term t where j is always 0,
--   and s is always an abstraction, effectively, substitute s
--   for all top level bindings in t, recursively.
--    
--   Descend subterms in t counting up a binding level for
--   each abstraction.  At terminal 'Var'(s) in t, if 'Var' index
--   i equals binding depth, substitute with s, being careful
--   to shift s by binding depth.
--
--  >>> snd $ termSubst 0 (Node ("x",Nothing) [Node ("",Nothing) []], UTmAbs (UTmVar 0)) (Node ("x",Nothing) [Node ("",Nothing) []], UTmAbs (UTmVar 0))
--  UTmAbs (UTmVar 0)
--
termSubst :: Int -> (Γ,UnnamedTerm) -> (Γ,UnnamedTerm) -> (Γ,UnnamedTerm)
termSubst 0 (c1, s) t = walk 0 t
  where
    walk :: Int -> (Γ,UnnamedTerm) -> (Γ,UnnamedTerm)
    walk c pr@(_,                      UTmTrue)      = pr
    walk c pr@(_,                      UTmFalse)     = pr
    walk c (Node _ [ctx1, ctx2, ctx3], UTmIf t1 t2 t3) = (Node ("", Nothing) [ctx1', ctx2', ctx3'], UTmIf t1' t2' t3') where (ctx1', t1') = walk c (ctx1, t1); (ctx2', t2') = walk c (ctx2, t2); (ctx3', t3') = walk c (ctx3, t3)
    walk c pr@(_,                      UTmVar i)       = if i == 0 + c then (c1, termShift c s) else pr
    walk c (Node (x, ty) [ctx],        UTmAbs t1)      = (Node (x, ty) [ctx'], UTmAbs t2) where (ctx', t2) = walk (c+1) (ctx, t1)
    walk c (Node _ [ctx1, ctx2],       UTmApp t1 t2)   = (Node ("", Nothing) [ctx1', ctx2'], UTmApp t1' t2') where (ctx1', t1') = walk c (ctx1, t1); (ctx2', t2') = walk c (ctx2, t2)
    walk c t = error $ "termSubst walk unexpected arg vals c " ++ show c ++ " t " ++ show t 
termSubst n (_, s) t = error $ "termSubst called with non-zero index " ++ show n ++ " for terms s " ++ show s ++ " and t " ++ show t

-- | Substitute 'UnnamedTerm s' in first argument in inner term of 'UnnamedTerm t'
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
βRed2 :: (Γ,UnnamedTerm) -> (Γ,UnnamedTerm) -> (Γ,UnnamedTerm)
βRed2 (c1, s) (Node _ [c2], UTmAbs t) = (c3, termShift (-1) t2) where (c3, t2) = termSubst 0 (c1, termShift 1 s) (c2, t)
βRed2 s t = error $ "βRed2 unexpected types for term s " ++ show  s ++ " or t " ++ show t

type EvalStrategy = ((Γ,UnnamedTerm) -> (Γ,UnnamedTerm))

-- | Mechanically speaking, what happens if we just provide a way to reduce within an outer
--   Abs?  This works.  But it sure doesn't seem to follow the rules from the answer in the
--   text.  It's hard to see just how this differs from normal order.  Maybe by the time you
--   work through all those rules in the answer in the text you wind up with something that
--   this implementation interprets.  Either way, as this suffices to carry out arithmetic
--   operations on Church numerals.
--
--  >>> either (putStrLn . show) (\cmds -> mapM_ putStrLn (evalCommands fullBetaEval cmds)) (parse parseCommands "lambda" "id = (λx:Bool.x);\n(id (id (t)));\n")
--  t
--
--
fullBetaEval :: EvalStrategy
fullBetaEval (Node _ [c1, c2], UTmApp t12@(UTmAbs _) t2) = βRed2 (c2,t2) (c1,t12)
fullBetaEval (Node _ [c1, c2], UTmApp t1 t2)             = (Node ("", Nothing) [c1', c2'], UTmApp t1' t2')
                                                             where
                                                               (c1',t1') = fullBetaEval (c1, t1)
                                                               (c2',t2') = fullBetaEval (c2, t2)
fullBetaEval (Node (n,ty) [c], UTmAbs t)                 = (Node (n,ty) [c'], UTmAbs t')
                                                             where
                                                               (c',t') = fullBetaEval (c,t)
fullBetaEval p                                           = p
 
-- | Eval wrapper stops at point of recurring to self (fix).
--
--   TBD: count terms to avoid co-recursion/unfold?
--
eval :: EvalStrategy -> (Γ,UnnamedTerm) -> (Γ,UnnamedTerm)
eval strat = fix (\v p@(_,t) -> let p'@(_, t') = strat p in if t == t' then p' else v p')

-----------------------------------------------------
-- 3:  eval Commands including Binder substitution --
-----------------------------------------------------
                   
-- | Symbol lookup for assignment of sym to term, e.g. @id = (λx.x);@.
--
type Env = [(Sym, (Γ,UnnamedTerm))]

-- | Walk down term in second arg (t) substituting context and 
--   term from env in first arg (e) where index for 'UTmVar' from term
--   in second arg reaches back beyond depth of binders recorded
--   in depth during walk (d), into free vars recorded by env in
--   first arg.  Keep in mind 'UTmVar' index to free vars is incremented
--   by depth, so index into free vars in Env has to be decremented
--   by depth, then subtracted from length of environment to index
--   back to front.  Note 'Sym' from pair in 'Env' is discarded here,
--   and must be reconstructed during 'unsubst' below to reconstruct
--   free vars for 'restoreNames'.
-- 
subst :: Env -> (Γ,UnnamedTerm) -> (Γ,UnnamedTerm)
subst e = walk 0
  where
    walk d pr@(Node _ [],        UTmTrue)        = pr
    walk d pr@(Node _ [],        UTmFalse)       = pr
    walk d (Node _ [c1, c2, c3], UTmIf t1 t2 t3) = (Node ("", Nothing) [c1', c2', c3'], UTmIf t1' t2' t3') where (c1',t1') = walk d (c1,t1); (c2',t2') = walk d (c2,t2); (c3',t3') = walk d (c3,t3)
    walk d pr@(Node _ [],        UTmVar i)       = if i >= d then snd (e !! (length e - (1 + (i-d)))) else pr
    walk d (Node (n,ty) [c],     UTmAbs t)       = (Node (n, ty) [c'], UTmAbs t') where (c',t') = walk (1+d) (c,t)
    walk d (Node _ [c1,c2],      UTmApp t1 t2)   = (Node ("", Nothing) [c1',c2'], UTmApp t1' t2') where (c1',t1') = walk d (c1,t1); (c2',t2') = walk d (c2,t2)

-- | Map @[(Sym, (Γ,UnnamedTerm))]@ (e) to @[(NamedTerm, Sym)]@ (e') in first arg
--   for lookup by 'NamedTerm' in second arg, then replace 'NamedTerm' with
--   (@Var Sym@) where lookup succeeds else descend ('unsubst'').
--   Be careful constructing @[(NamedTerm, Sym)]@ from @[(Sym, (Γ,UnnamedTerm))]@
--   via 'restoreNames' to reconstruct free vars for successive terms
--   in @[(Sym, (Γ,UnnamedTerm))]@ by building list of free vars from 'Sym'
--   at beginning of 'Env' in first argument (@scanl@).
--
unsubst :: Env -> NamedTerm -> NamedTerm
unsubst e =
  unsubst' 
  where
    syms = map fst e
    freeVarss = scanl (flip (:)) [head syms] (tail syms)
    e' = map (\(f,(s,(c,t))) -> (restoreNames f (c,t), s)) $ zip freeVarss e
    unsubst' NTmTrue            = NTmTrue
    unsubst' NTmFalse           = NTmFalse
    unsubst' t@(NTmIf t1 t2 t3) = maybe t' NTmVar (lookup t e') where t' = NTmIf (unsubst' t1) (unsubst' t2) (unsubst' t3)
    unsubst' t@(NTmVar _)       = t
    unsubst' t@(NTmAbs s ty t1) = maybe t' NTmVar (lookup t e') where t' = NTmAbs s ty (unsubst' t1)
    unsubst' t@(NTmApp t1 t2)   = maybe t' NTmVar (lookup t e') where t' = NTmApp (unsubst' t1) (unsubst' t2)

-- | Capture TermCommand in list, skip BinderCommand.
termCommand2MaybeNamedTerm :: Command -> Maybe NamedTerm
termCommand2MaybeNamedTerm (TermCommand t1) = Just t1
termCommand2MaybeNamedTerm _                = Nothing

-- | Append contents for BinderCommand to list, skip TermCommand.
--   Used to fold over BinderCommands in input file, where later
--   BinderCommands may reference names for earlier BinderCommands,
--   i.e. reference but no recursion.  Call to @map fst env@ for
--   first arg to 'removeNames' creates list of free vars for each 
--   successive UnnamedTerm from names for previous BinderCommands.
-- 
envAndBinderCommand2Env :: Env -> Command -> Env
envAndBinderCommand2Env env (BinderCommand s t) = env ++ [(s, subst env (removeNames (map fst env) t))]
envAndBinderCommand2Env env _ = env

checkBinderTypes :: Γ' -> Command -> Either String Γ'
checkBinderTypes env (BinderCommand s t) = checkTypes env t >>= \ty -> return $ env ++ [(s, ty)]
checkBinderTypes env (TermCommand t)     = checkTypes env t >> return env

-- | Given function that implements evaluation strategy in first argument, then 'Env' with global environment of
--   assoc list of 'Sym' to 'UnnamedTerm' and 'NamedTerm', use 'Sym' from 'Env' for free vars to remove names from 'NamedTerm',
--   creating tuple '(Γ,UnnamedTerm)', then evaluate the result and restore names using free vars and eval result.
--
evalNamedTerm :: EvalStrategy -> Env -> NamedTerm -> NamedTerm
evalNamedTerm strat env =
  unsubst env . restoreNames syms . eval strat . subst env . removeNames syms
  where
    syms = map fst env

-- | Separate binders from terms in '[Command]' and then evaluate all ter ms using
--   free vars with terms in binders and answer the list of resulting terms.
--    
evalCmds :: EvalStrategy -> [Command] -> [String]
evalCmds strat cmds = map (show . pretty . evalNamedTerm strat env) terms
  where
    env   = foldl envAndBinderCommand2Env [] cmds
    terms = mapMaybe termCommand2MaybeNamedTerm cmds

typeCheckCommands :: [Command] -> Either String Γ'
typeCheckCommands = foldM checkBinderTypes [] 

evalCommands :: EvalStrategy -> [Command] -> [String]
evalCommands strat cmds = either (:[]) (\_ ->evalCmds strat cmds) $ typeCheckCommands cmds
