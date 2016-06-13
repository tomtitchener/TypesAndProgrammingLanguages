{--
  Parser functions for untyped lambda calculus.
--}

module Simple.Parse(
    Command(..)
  , parseCommands
  ) where

import Control.Monad                 (liftM, void)
import Text.ParserCombinators.Parsec (Parser(..), (<|>), (<?>), many, many1, endBy, lower, string, char, eof, parse, spaces, newline, noneOf, letter, try, parseFromFile, choice)
import Simple.Data                   (Sym, Ty(..), NamedTerm(..))

-----------
-- Parse --
-----------

data Command = TermCommand NamedTerm | BinderCommand Sym NamedTerm | Comment deriving (Eq, Show)

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
parseId = many1 (noneOf "#λ.();: ")

-- | 'Var' just wraps id.
-- 
-- >>> parse parseVar "test" "x"
-- Right (NTmVar "x")
--
-- >>> parse parseVar "test" "id"
-- Right (NTmVar "id")
--
parseVar :: Parser NamedTerm
parseVar = liftM NTmVar parseId

-- | Trivial
--
-- >>> parse parseBool "test" "Bool"
-- Right TyBool
--
parseBool :: Parser Ty
parseBool = string "Bool" >> return TyBool

-- | Trivial?
--
-- >>> parse parseArrow "test" "(Bool→Bool)"
-- Right (TyArrow TyBool TyBool)
-- 
-- >>> parse parseArrow "test" "((Bool→Bool) → (Bool→Bool))"
-- Right (TyArrow (TyArrow TyBool TyBool) (TyArrow TyBool TyBool))
-- 
parseArrow :: Parser Ty
parseArrow = char '(' >> spaces >> parseType >>= \t1 -> spaces >> char '→' >> spaces >> parseType >>= \t2 -> spaces >> char ')' >> return (TyArrow t1 t2)

-- | Only types supported by simple typed calculus are Bool and Arrow.
-- 
parseType :: Parser Ty
parseType = try parseBool <|> try parseArrow

-- | Catch type in abstraction, is only impact on syntax compated with untyped lambda calculus.
-- 
-- >>> parse parseAbs "test" "λx:Bool.x"
-- Right (NTmAbs "x" TyBool (NTmVar "x"))
--
-- >>> parse parseAbs "test" "λx:(Bool→Bool).(λx:Bool.x)"
-- Right (NTmAbs "x" (TyArrow TyBool TyBool) (NTmAbs "x" TyBool (NTmVar "x")))
--
parseAbs :: Parser NamedTerm
parseAbs = char 'λ' >> spaces >> parseId >>= \n -> spaces >> char ':' >> spaces >> parseType >>= \t -> spaces >> char '.' >> spaces >> parseTerm >>= \e -> return $ NTmAbs n t e

-- | Parse according to parentheses.
--
-- >>> parse parseATerm "test" "(a(b(c d)))"
-- Right (NTmApp (NTmVar "a") (NTmApp (NTmVar "b") (NTmApp (NTmVar "c") (NTmVar "d"))))
--
-- >>> parse parseATerm "test" "(((a b)c)d)"
-- Right (NTmApp (NTmApp (NTmApp (NTmVar "a") (NTmVar "b")) (NTmVar "c")) (NTmVar "d"))
-- 
parseATerm :: Parser NamedTerm
parseATerm = (char '(' >> parseTerm >>= \e -> char ')' >> spaces >> return e) <|> (parseVar >>= \v -> spaces >> return v)

-- | One or more in a row, nested left.
--
-- >>> parse parseAppTerm "test" "x y"
-- Right (NTmApp (NTmVar "x") (NTmVar "y"))
--
-- >>> parse parseAppTerm "test" "x y z"
-- Right (NTmApp (NTmApp (NTmVar "x") (NTmVar "y")) (NTmVar "z"))
--
parseAppTerm :: Parser NamedTerm
parseAppTerm = liftM (foldl1 NTmApp) (many1 parseATerm)

-- | Parse a Term 
-- 
-- >>> parse parseTerm "lambda" "(λx:Bool.x)y"
-- Right (NTmApp (NTmAbs "x" TyBool (NTmVar "x")) (NTmVar "y"))
--
-- >>> parse parseTerm "lambda" "λx:Bool.x y"
-- Right (NTmAbs "x" TyBool (NTmApp (NTmVar "x") (NTmVar "y")))
--
parseTerm :: Parser NamedTerm
parseTerm = parseAppTerm <|> parseAbs

parseTermCommand :: Parser Command
parseTermCommand = liftM TermCommand (spaces >> parseTerm) <?> "term command"

parseBinderCommand :: Parser Command
parseBinderCommand = spaces >> parseId >>= \i -> spaces >> char '=' >> spaces >> parseTerm >>= \t -> return (BinderCommand i t) <?> "binder command"

parseComment :: Parser Command
parseComment = spaces >> char '#' >> many (noneOf "\n") >> return Comment <?> "comment"

parseCommand :: Parser Command
parseCommand = try parseBinderCommand <|> try parseTermCommand <|> try parseComment <?> "command"

-- | Parse list of (possibly intermingled) list of 'Command' each of which is either a 'BinderCommand' with a 'Sym' and a 'NamedTerm', separated by @=@, e.g.
--
--     @id = (λx.x);@
--
--   or a 'TermCommand' with a single 'NamedTerm', e.g.
--
--     @(id id);@
--
--   @
--   # comment here
--   id = (λx.x);
--   # empty lines permitted
--   
--   tru = (λt.λf.t);
--   fls = (λt.λf.f);
--   test = (λl.λm.λn. l m n);
--   (id id);
--   (test tru (λv.v) (λw.w));
--   (test fls (λv.v) (λw.w));
--   @
--
parseCommands :: Parser [Command]
parseCommands = parseCommand `endBy` choice [eof, void newline, char ';' >> void newline]

