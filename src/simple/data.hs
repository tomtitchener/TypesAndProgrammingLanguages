{-
  Data types for simply typed lambda calculus.
-}

module Simple.Data (
    Sym
  , Ty(..)
  , NamedTerm(..)
  , UnnamedTerm(..)
  ) where

import Text.PrettyPrint.Leijen ((<>), char, int, string, pretty, Pretty(..))

-------------------------------------
-- 1:  untyped calculus with names --
-------------------------------------

-- | Use a 'String' instead of 'Char' so 'Sym' can be name, e.g. for
--
--   @id = (x.x);@  NamedTerm
--
type Sym = String

-- | Types in simple typed calculus are just Bool and function (→), e.g. product.
-- 
data Ty =
    TyBool
  | TyArrow Ty Ty
  deriving (Show, Eq)

-- | Pretty print 'ty'
--
-- >>> pretty $ TyArrow TyBool TyBool
-- (Bool→Bool)
--
instance Pretty Ty where
  pretty TyBool = string "Bool"
  pretty (TyArrow t1 t2) = char '(' <> pretty t1 <> char '→' <> pretty t2 <> char ')'

-- | Simple typed calculus adds type Bool to Lambda terms.
--
data NamedTerm =
    NTmTrue
  | NTmFalse
  | NTmIf NamedTerm NamedTerm NamedTerm
  | NTmVar Sym
  | NTmAbs Sym Ty NamedTerm 
  | NTmApp NamedTerm NamedTerm
  deriving (Show, Eq)

-- | Pretty print 'NamedTerm'
--
--  >>> pretty $ (NTmApp (NTmAbs "x" TyBool (NTmVar "x")) (NTmVar "x"))
--  (λx:Bool.x x)
--
instance Pretty NamedTerm where
  pretty NTmTrue          = char 't'
  pretty NTmFalse         = char 'f'
  pretty (NTmIf t1 t2 t3) = string "If " <> pretty t1 <> string " then " <> pretty t2 <> string " else " <> pretty t3 
  pretty (NTmVar s)       = string s
  pretty (NTmAbs n ty t)  = string "λ" <> string n <> char ':' <> pretty ty <> char '.' <> pretty t
  pretty (NTmApp t1 t2)   = char '(' <> pretty t1 <> char ' ' <> pretty t2 <> char ')'
  
--------------------------------------------
-- 2:  untyped calculus de Bruijn indexes --
--------------------------------------------

-- | Simple typed calculus adds type Bool to Lambda terms.
--
data UnnamedTerm =
    UTmTrue
  | UTmFalse
  | UTmIf UnnamedTerm UnnamedTerm UnnamedTerm
  | UTmVar Int
  | UTmAbs UnnamedTerm
  | UTmApp UnnamedTerm UnnamedTerm
  deriving (Show, Eq)

-- | Pretty print 'UnnamedTerm'
--
--   >>> pretty $ (UTmApp (UTmAbs (UTmVar 0)) (UTmVar 0))
--   (λ.0 0)
--
instance Pretty UnnamedTerm where
  pretty UTmTrue          = char 't'
  pretty UTmFalse         = char 't'
  pretty (UTmIf t1 t2 t3) = string "If " <> pretty t1 <> string " then " <> pretty t2 <> string " else " <> pretty t3 
  pretty (UTmVar i)       = int i
  pretty (UTmAbs t)       = string "λ." <> pretty t
  pretty (UTmApp t1 t2)   = char '(' <> pretty t1 <> char ' ' <>  pretty t2 <> char ')'

