{--

 Examples from "Types and Programming Languages" Benjamin Pierce.
 1) Untyped lambda calculus with beta reduction "up to renaming of bound variables"
 2) Untyped lambda calculus with de Bruijn presentation and full beta reduction

 TBD:

   * testing/validation
     - add parse of comments and empty lines for file of definitions and lambda expressions
     - consume a file of definitions (maybe just a a list of text strings with a definition per line)
     - validate a series of lambda expressions and expected results
     - convert single file of lamba definitions and expressions into files that validate e.g. pairs, bools, numerals, recursion, etc.

page 88:  "Just because you've implemented something doesn't mean you understand it" (Brian Cantwell Smith).
--}

module Main where

import Prelude                       hiding (readFile)
import System.Environment            (getArgs)
import Text.ParserCombinators.Parsec (parse, parseFromFile)
import Untyped                       (EvalStrategy, parseCommands, evalCommands, callByValEval, fullBetaEval)

-- | Parser for file with list of lines, converted to [Command], which then gets
--   split into environment with assoc list of sym with term and a list of terms
--   to evaluate in the context of the environment, e.g.
--
--   @    
--   id = λx.x;
--   (id id);
--   @
--
--   See "test.l" for examples.  Use this function in ghci to run file by hand:  @λ: readFile' "test.l"@.
--
-- >>> either (putStrLn . show) (\cmds -> mapM_ putStrLn (evalCommands callByValEval cmds)) (parse parseCommands "lambda" "id = λx.x;\n(id id);\n")
-- id
--
--    
-- >>> either (putStrLn . show) (\cmds -> mapM_ putStrLn (evalCommands fullBetaEval cmds)) (parse parseCommands "lambda" "id = λx.x;\n(id id);\n")
-- id
--
--
readFile' :: EvalStrategy -> String -> IO ()
readFile' strat fName = parseFromFile parseCommands fName >>= either print (mapM_ putStrLn . evalCommands strat)

-- | Expects file name as single command-line argument.
-- 
readFile :: EvalStrategy -> IO ()
readFile strat = getArgs >>= readFile' strat . head

main :: IO ()
main = readFile fullBetaEval

