-- | Name generation
module NameGen where
import Control.Monad.State

import AST

data NameState = NameState
  { varNames  :: [Var]
  , tvarNames :: [TVar]
  }

initialNameState :: NameState
initialNameState = NameState
  { varNames  = map (Var . ('$':)) namelist
  , tvarNames = map (TypeVar . ('\'':)) namelist
  }
  where
    namelist = [1..] >>= flip replicateM ['a'..'z']

type NameGen a = State NameState a

evalNameGen :: NameGen a -> a
evalNameGen = flip evalState initialNameState

freshVar :: NameGen Var
freshVar = do
  v:vs <- gets varNames
  modify $ \s -> s {varNames = vs}
  return v

freshTVar :: NameGen TVar
freshTVar = do
  v:vs <- gets tvarNames
  modify $ \s -> s {tvarNames = vs}
  return v
