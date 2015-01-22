-- | Interface to SMT solvers
module Synquid.SMTSolver where

import Synquid.Logic
import Control.Applicative

class (Monad s, Applicative s) => SMTSolver s where  
  initSolver :: s ()            -- ^ Initialize solver  
  isValid :: Formula -> s Bool  -- ^ 'isValid' @fml@: is @fml@ logically valid?