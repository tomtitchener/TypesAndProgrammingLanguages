module Simple (
    NamedTerm(..)
  , UnnamedTerm(..)
  , Command(..)
  , parseCommands
  , evalCommands
  ) where

import Simple.Data
import Simple.Parse
import Simple.Eval
