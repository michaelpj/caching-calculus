{-# LANGUAGE GADTs #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE OverloadedStrings #-}

module CC where

import Data.Map as M
import Data.Hashable
import Data.Monoid
import GHC.Generics (Generic)
import Control.Monad
import Control.Monad.State
import Control.Monad.Logger
import qualified Data.Text as T

type Name = String
type Value = Int

data Term = Const Value
          | Var Name
          | Abs Name Term
          | App Term Term
          | Plus Term Term
          deriving (Show, Eq, Generic)

instance Hashable Term

substitute :: Name -> Term -> Term -> Term
substitute v x (Var v') | v' == v = x
substitute v x (Abs arg t) = Abs arg (substitute v x t)
substitute v x (App t t2) = App (substitute v x t) (substitute v x t2)
substitute v x (Plus t t2) = Plus (substitute v x t) (substitute v x t2)
substitute _ _ t = t

type Cache v = M.Map Int v

class (Hashable t, Show t) => Evalable t where
  reduce :: t -> t
  normal :: t -> Bool
  hashS :: t -> Cache t -> Int

instance Evalable Term where
  reduce (App (Abs arg t) t2) = substitute arg t2 t
  reduce (App t1 t2) = App (reduce t1) t2
  reduce (Plus (Const i1) (Const i2)) = Const (i1 + i2)
  reduce (Plus t1 t2) | normal t1 && normal t2 = Plus t1 t2
                      | not (normal t2) = Plus t1 (reduce t2)
                      | not (normal t1) = Plus (reduce t1) t2
  reduce t = t

  normal (App (Abs arg t) t2) = False
  normal (App t1 t2) = normal t1
  normal (Plus (Const i1) (Const i2)) = False
  normal (Plus t1 t2) = normal t1 && normal t2
  normal _ = True

  hashS t@(Const i) cache = hash t
  hashS t@(Var v) cache = hash t
  hashS (Abs arg t) cache = 0 `hashWithSalt` (hash arg) `hashWithSalt` (cacheHash t cache)
  hashS (App t1 t2) cache = 1 `hashWithSalt` (cacheHash t1 cache) `hashWithSalt` (cacheHash t2 cache)
  hashS (Plus t1 t2) cache = 2 `hashWithSalt` (cacheHash t1 cache) `hashWithSalt` (cacheHash t2 cache)

cacheHash :: (Hashable t) => t -> Cache t -> Int
cacheHash t cache = let h = hash t
                    in case (M.lookup h cache) of
                         Just t2 -> hash t2
                         Nothing -> h

eval :: (Evalable t, MonadState (Cache t) m, MonadLogger m) => t -> m t
eval t = do
  c <- get
  let h = hashS t c
  logInfoN $ "About to evaluate: " <> T.pack (show t)
  logInfoN $ "Hash is: " <> T.pack (show h)
  case (M.lookup h c) of
    Just v -> do
      logInfoN $ "Cache hit!"
      pure v
    Nothing -> do
      logInfoN $ "Cache miss! Evaluating term."
      evaled <- if (normal t)
                then pure t
                else eval (reduce t)
      logInfoN $ "Evaluated. Storing: " <> T.pack (show h) <> " -> " <> T.pack (show evaled)
      modify $ M.insert h evaled
      pure evaled

type M a = LoggingT (StateT (Cache Term) IO) a

runM :: M a -> IO (a, Cache Term)
runM m = runStateT (runStdoutLoggingT m) M.empty

k = Abs "x" (Abs "y" (Var "x"))

t1 = k `App` (Const 1) `App` (Const 1)

t2 = (Const 1) `Plus` (Const 1)

t3 = t2 `Plus` t2

test = runM (eval t3)
