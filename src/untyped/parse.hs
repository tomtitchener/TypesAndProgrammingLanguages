{--
  Parser functions for untyped lambda calculus.
--}

module Untyped.Parse(
    Command(..)
  , parseCommands
  ) where

import Control.Monad                 (liftM, void)
import Text.ParserCombinators.Parsec (Parser(..), (<|>), (<?>), many, many1, endBy, lower, char, eof, parse, spaces, newline, noneOf, letter, try, parseFromFile, choice)
import Untyped.Data                  (Sym, NamedλTerm(..))

-----------
-- Parse --
-----------

data Command = TermCommand NamedλTerm | BinderCommand Sym NamedλTerm | Comment deriving (Eq, Show)

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
parseId = many1 (noneOf "#λ.(); ")

-- | 'Var' just wraps id.
-- 
-- >>> parse parseVar "test" "x"
-- Right (Var "x")
--
-- >>> parse parseVar "test" "id"
-- Right (Var "id")
--
parseVar :: Parser NamedλTerm
parseVar = liftM Var parseId

-- | Space(s) after var or id is optional
-- 
-- >>> parse parseAbs "test" "λx.x"
-- Right (Abs "x" (Var "x"))
--
-- >>> parse parseAbs "test" "λx. x"
-- Right (Abs "x" (Var "x"))
--
parseAbs :: Parser NamedλTerm
parseAbs = char 'λ' >> parseId >>= \v -> spaces >> char '.' >> spaces >> parseTerm >>= \e -> return $ Abs v e

-- | Parse according to parentheses.
--
-- >>> parse parseATerm "test" "(a(b(c d)))"
-- Right (App (Var "a") (App (Var "b") (App (Var "c") (Var "d"))))
--
-- >>> parse parseATerm "test" "(((a b)c)d)"
-- Right (App (App (App (Var "a") (Var "b")) (Var "c")) (Var "d"))
-- 
parseATerm :: Parser NamedλTerm
parseATerm = (char '(' >> parseTerm >>= \e -> char ')' >> spaces >> return e) <|> (parseVar >>= \v -> spaces >> return v)

-- | One or more in a row, nested left.
--
-- >>> parse parseAppTerm "test" "x y"
-- Right (App (Var "x") (Var "y"))
--
-- >>> parse parseAppTerm "test" "x y z"
-- Right (App (App (Var "x") (Var "y")) (Var "z"))
--
parseAppTerm :: Parser NamedλTerm
parseAppTerm = liftM (foldl1 App) (many1 parseATerm)

-- | Parse a Term 
-- 
-- >>> parse parseTerm "lambda" "(λx.x)y"
-- Right (App (Abs "x" (Var "x")) (Var "y"))
--
-- >>> parse parseTerm "lambda" "λx.x y"
-- Right (Abs "x" (App (Var "x") (Var "y")))
--
-- >>> parse parseTerm "lambda" "(id (id t));"
-- Right (App (Var "id") (App (Var "id") (Var "t")))
--
parseTerm :: Parser NamedλTerm
parseTerm = parseAppTerm <|> parseAbs

parseTermCommand :: Parser Command
parseTermCommand = liftM TermCommand (spaces >> parseTerm) <?> "term command"

parseBinderCommand :: Parser Command
parseBinderCommand = spaces >> parseId >>= \i -> spaces >> char '=' >> spaces >> parseTerm >>= \t -> return (BinderCommand i t) <?> "binder command"

parseComment :: Parser Command
parseComment = spaces >> char '#' >> many (noneOf "\n") >> return Comment <?> "comment"

parseCommand :: Parser Command
parseCommand = try parseBinderCommand <|> try parseTermCommand <|> try parseComment <?> "command"

-- | Parse list of (possibly intermingled) list of 'Command' each of which is either a 'BinderCommand' with a 'Sym' and a 'NamedλTerm', separated by @=@, e.g.
--
--     @id = (λx.x);@
--
--   or a 'TermCommand' with a single 'NamedλTerm', e.g.
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

