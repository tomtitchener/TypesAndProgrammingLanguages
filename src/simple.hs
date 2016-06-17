module Simple (
    NamedTerm(..)
  , UnnamedTerm(..)
  , Command(..)
  , parseCommands
  , EvalStrategy(..)
  , fullBetaEval
  , evalCommands
  ) where

import Simple.Data
import Simple.Parse
import Simple.Eval
