{-# LANGUAGE GADTs #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE ExplicitForAll #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}

module Lambda where

import Data.Map as M
import Data.Hashable
import Data.Hashable.Lifted
import Data.Functor.Classes
import Data.Functor.Foldable
import Data.Functor.Identity
import Text.Show.Deriving
import Data.Monoid
import GHC.Generics (Generic, Generic1)
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Logger
import qualified Data.Text as T

import qualified CachingEval as C

data Lambda e = Index Int | Abs e | Apply e e
  deriving (Functor)

type LambdaTerm = Fix Lambda

data Value m where
  Num  :: Int -> Value m
  Clos :: Monad m => [Value m] -> m (Value m) -> Value m

instance Show (Value m) where
  show (Num i) = show i
  show (Clos _ _) = "closure"

class Monad m => CBVMonad m where
  env  :: m [Value m]
  with :: [Value m] -> m (Value m) -> m (Value m)

evalAlgebra :: (CBVMonad m, MonadLogger m) => C.Algebra Lambda (m (Value m))
evalAlgebra term = case term of
  Index i -> do
    logInfoN ("Evaluating variable " <> T.pack (show i))
    e <- env
    pure $ e !! i
  Abs t -> do
    logInfoN ("Evaluating closure")
    e <- env
    pure $ Clos e t
  Apply f x -> do
    logInfoN ("Evaluating application")
    Clos ctx t <- f
    c <- x
    with (c:ctx) t

newtype EnvReader t = EnvReader {
  unEnv :: ReaderT ([Value EnvReader]) (LoggingT IO) t
  } deriving (Functor, Applicative, Monad, MonadLogger)

instance CBVMonad EnvReader where
  env = EnvReader ask
  with e comp = EnvReader (local (\_ -> e) (unEnv comp))

eval :: LambdaTerm -> [Value EnvReader] -> IO (Value EnvReader)
eval t initial = runStdoutLoggingT (runReaderT (unEnv (cata evalAlgebra t)) initial)

index :: Int -> LambdaTerm
index i = Fix $ Index i

abst :: LambdaTerm -> LambdaTerm
abst e = Fix $ Abs $ e

app :: LambdaTerm -> LambdaTerm -> LambdaTerm
app e1 e2 = Fix $ Apply e1 e2

i :: LambdaTerm
i = abst $ index 0

k :: LambdaTerm
k = abst $ abst $ index 1

s :: LambdaTerm
s = abst $ abst $ abst $ app (app (index 2) (index 0)) (app (index 1) (index 0))

testEnv1 :: [Value EnvReader]
testEnv1 = [ Num 1, Num 2 ]

testTerm2 :: LambdaTerm
testTerm2 = app (abst (index 0)) (index 0)
