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
--   See "test" for examples.  Use this function in ghci to run file by hand:  @λ: readFile' "foo.l"@.
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

-- | Church booleans
--
-- >>> readFile' fullBetaEval "./test/bool.l"
-- l
-- m
-- tru
-- fls
-- fls
-- fls
-- tru
-- tru
-- tru
-- fls
-- fls
-- tru
-- tru
-- fls
--
-- | Church numerals
--
-- >>> readFile' fullBetaEval "./test/num.l"
-- one
-- one
-- zero
-- one
-- two
-- three
-- four
-- four
-- zero
-- zero
-- one
-- two
-- four
-- one
-- one
-- nine
-- fls
-- tru
-- zero
-- zero
-- one
-- two
-- one
-- two
-- three
-- tru
-- fls
-- tru
-- tru
-- fls
--
-- | Recursion
-- 
-- >>> readFile' fullBetaEval "./test/recur.l"
-- omega
-- twentyfour
--
main :: IO ()
main = readFile fullBetaEval

