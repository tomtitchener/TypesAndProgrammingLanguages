module Untyped (
    Term1(..)
  , Term2(..)
  , eval1
  , EvalStrategy
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
                       
