module Untyped (
    NamedλTerm(..)
  , UnnamedλTerm(..)
  , EvalStrategy
  , namedλTermEval
  , callByValEval
  , fullBetaEval
  , eval
  , evalCommands
  , Command(..)
  , parseCommands
  ) where

import Untyped.Data
import Untyped.Parse
import Untyped.Eval
                       
