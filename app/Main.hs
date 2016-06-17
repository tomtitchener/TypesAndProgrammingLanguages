module Main where

import           Prelude                       hiding (readFile)
import           System.Environment            (getArgs)
import           Text.ParserCombinators.Parsec (parse, parseFromFile)
import qualified Simple as S                   (EvalStrategy, parseCommands, evalCommands, fullBetaEval) 
import qualified Untyped as U                  (EvalStrategy, parseCommands, evalCommands, callByValEval, fullBetaEval) 

-- | Parser for file with list of lines, converted to [Command], which then gets
--   split into environment with assoc list of sym with term and a list of terms
--   to evaluate in the context of the environment, e.g.
--
--   @    
--   id = λx.x;
--   (id id);
--   @
--
--   See "test" for examples.  Use this function in ghci to run file by hand:  @λ: readFileUnnamed "foo.l"@.
--
-- >>> either (putStrLn . show) (\cmds -> mapM_ putStrLn (U.evalCommands U.callByValEval cmds)) (parse U.parseCommands "lambda" "id = λx.x;\n(id id);\n")
-- id
--
--    
-- >>> either (putStrLn . show) (\cmds -> mapM_ putStrLn (U.evalCommands U.fullBetaEval cmds)) (parse U.parseCommands "lambda" "id = λx.x;\n(id id);\n")
-- id
--
--
readFileUnnamed :: U.EvalStrategy -> String -> IO ()
readFileUnnamed strat fName = parseFromFile U.parseCommands fName >>= either print (mapM_ putStrLn . U.evalCommands strat)

-- | Expects file name as single command-line argument.
-- 
readForFileUnnamed :: U.EvalStrategy -> IO ()
readForFileUnnamed strat = getArgs >>= readFileUnnamed strat . head

-- | Church booleans
--
-- >>> readFileUnnamed U.fullBetaEval "./test/bool.l"
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
-- >>> readFileUnnamed U.fullBetaEval "./test/num.l"
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
-- >>> readFileUnnamed U.fullBetaEval "./test/recur.l"
-- omega
-- twentyfour
--
main :: IO ()
main = readForFileUnnamed U.fullBetaEval

