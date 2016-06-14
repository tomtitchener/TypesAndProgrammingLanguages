module Simple (
    NamedTerm(..)
  , UnnamedTerm(..)
  , Command(..)
  , parseCommands
  , eval
  , fullBetaEval
  , evalCommands
  ) where

import Simple.Data
import Simple.Parse
import Simple.Eval
