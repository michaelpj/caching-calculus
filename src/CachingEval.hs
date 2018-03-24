{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE DeriveAnyClass #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TemplateHaskell #-}

module CachingEval where

import Data.Map as M
import Data.Hashable
import Data.Hashable.Lifted
import Data.Functor.Classes
import Data.Functor.Foldable
import Text.Show.Deriving
import Data.Monoid
import GHC.Generics (Generic, Generic1)
import Control.Monad.State
import Control.Monad.Logger
import qualified Data.Text as T

show1 :: (Show1 f, Show a) => f a -> String
show1 fa = showsPrec1 0 fa ""

defaultSalt :: Int
defaultSalt = 56

instance (Hashable1 f) => Hashable (Fix f) where
  hashWithSalt salt (Fix x) = hashWithSalt1 salt x

type Algebra f a = f a -> a
type MAlgebra f m a = f a -> m a

cataM :: (Traversable f, Monad m) => MAlgebra f m a -> (Fix f -> m a)
cataM f = c where c = f <=< mapM c . unfix

-- term functor

data TermF a = PlusF a a
             | MultF a a
             | IntConstF Int
             -- the Traversable instance dictates in which order we will
             -- evaluate subterms, for this we don't care
             deriving (Ord, Eq, Functor, Foldable, Traversable, Generic1)
$(deriveShow1 ''TermF)
instance Hashable1 TermF

instance Hashable a => Hashable (TermF a) where
  hashWithSalt = hashWithSalt1

type Term = Fix TermF

testTerm :: Term
testTerm = let x = (Fix $ MultF
                     (Fix $ IntConstF 2)
                     (Fix $ IntConstF 3))
               -- y is content-equivalent to x, but not structurally equivalent
               y = (Fix $ MultF
                     (Fix $ PlusF (Fix $ IntConstF 1) (Fix $ IntConstF 1))
                     (Fix $ IntConstF 3))
           in Fix $ PlusF x y

-- Basic evaluation

evalAlgebra :: (MonadLogger m) => MAlgebra TermF m Int
evalAlgebra t = do
  logInfoN ("Evaluating " <> T.pack (show1 t))
  case t of
    PlusF i1 i2 -> pure $ i1 + i2
    MultF i1 i2 -> pure $ i1 * i2
    IntConstF i -> pure i

eval :: (MonadLogger m) => Term -> m Int
eval t = cataM evalAlgebra t

type M a = LoggingT IO a
runM :: M a -> IO a
runM m = runStdoutLoggingT m

-- With attempt at value-based caching

type Hash = Int
type Cache v = M.Map Hash v

type CacheT v = StateT (Cache v)

type M2 a = (CacheT a) (LoggingT IO) a
runM2 :: M2 a -> IO (a, Cache a)
runM2 m = runStdoutLoggingT (runStateT m M.empty)

-- Generic cache before evaluation

withCaching :: (MonadLogger m,
               MonadState (Cache b) m,
               Hashable a) =>
               (a -> m b) -> a -> m b
withCaching reeval arg = do
  c <- get
  let h = hash arg :: Int
  logInfoN $ "Evaluating, hash is " <> (T.pack (show h))
  case (M.lookup h c) of
    Just v -> do
      logInfoN "Cache hit"
      pure v
    Nothing -> do
      logInfoN "Cache miss"
      evaled <- reeval arg
      modify $ M.insert h evaled
      pure evaled

cataMCache :: (Traversable f,
               Monad m,
               MonadLogger m,
               MonadState (Cache a) m,
               Hashable1 f) =>
              MAlgebra f m a -> (Fix f -> m a)
cataMCache alg = withCaching reeval
  where reeval (Fix x) = mapM (cataMCache alg) x >>= alg

testCache2 :: M2 Int
testCache2 = do
  i <- cataMCache evalAlgebra testTerm
  logInfoN ("Evaluated to " <> T.pack (show i))
  i2 <- cataMCache evalAlgebra testTerm
  logInfoN ("Evaluated to " <> T.pack (show i2))
  pure i2

-- Content caching passing up caches when necessary

data Caches a = Caches {
  contentCache :: Cache a,
  hashHashCache :: Cache Hash,
  treeHashCache :: Cache Hash
} deriving (Show)

type M3 a = (StateT (Caches a)) (LoggingT IO) a
runM3 :: M3 a -> IO (a, Caches a)
runM3 m = runStdoutLoggingT (runStateT m Caches { contentCache = M.empty, hashHashCache = M.empty, treeHashCache = M.empty } )

data Result m a =
  -- An actual value
  Value a
  -- A content hash and a computation we can run to get the value
  | Content Hash (m a)
instance Show a => Show (Result m a) where
  show (Value v) = show v
  show (Content h _) = show h

resultToHash :: (Hashable a) => Result m a -> Hash
resultToHash (Value a) = hash a
resultToHash (Content h _) = h

resultToValue :: (Hashable a, Monad m) => Result m a -> m a
resultToValue (Value a) = pure a
resultToValue (Content _ ma) = ma

algebraCacheGeneric :: (MonadState (Caches a) m,
                        MonadLogger m,
                        Hashable1 f,
                        Hashable a,
                        Traversable f,
                        Show1 f,
                        Show a) =>
                 MAlgebra f m a -> MAlgebra f m (Result m a)
algebraCacheGeneric algebra t = do
  let termHash = hashWithSalt1 defaultSalt $ fmap resultToHash t
  logInfoN $ "Considering " <> T.pack (show1 t) <> ", term hash is " <> T.pack (show termHash)
  hc <- gets hashHashCache
  let maybeContentHash = M.lookup termHash hc
  let computation = contentComputation algebra maybeContentHash (mapM resultToValue t)
  case maybeContentHash of
    Just contentHash -> do
      logInfoN $ "Hash cache hit for " <> T.pack (show termHash)
      pure $ Content contentHash computation
    Nothing -> do
      logInfoN $ "Hash cache miss for " <> T.pack (show termHash)
      evaled <- computation
      modify $ \c -> c {
        hashHashCache = M.insert termHash (hash evaled) (hashHashCache c)
      }
      pure $ Value evaled

contentComputation :: (MonadState (Caches a) m,
                   MonadLogger m,
                   Hashable1 f,
                   Hashable a,
                   Traversable f,
                   Show1 f,
                   Show a) =>
                  MAlgebra f m a -> Maybe Hash -> m (f a) -> m a
contentComputation algebra maybeContentHash t = do
  cc <- gets contentCache
  let maybeContent = do
        contentHash <- maybeContentHash
        M.lookup contentHash cc
  case maybeContent of
    Just value -> do
      logInfoN $ "Content cache hit for " <> T.pack (show maybeContentHash)
      pure value
    Nothing -> do
      logInfoN $ "Content cache miss for " <> T.pack (show maybeContentHash)
      evaled <- t >>= algebra
      modify $ \c -> c {
        contentCache = M.insert (hash evaled) evaled (contentCache c)
      }
      pure evaled

testCache3 :: M3 Int
testCache3 = do
  res <- do
    logInfoN ("ATTEMPT 1")
    i <- cataM (algebraCacheGeneric evalAlgebra) testTerm
    logInfoN ("Evaluated to " <> T.pack (show i))
    logInfoN ("ATTEMPT 2")
    i2 <- cataM (algebraCacheGeneric evalAlgebra) testTerm
    logInfoN ("Evaluated to " <> T.pack (show i2))
    pure i2
  resultToValue res
