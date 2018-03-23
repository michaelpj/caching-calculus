{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveFoldable #-}
{-# LANGUAGE DeriveTraversable #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}

module Simple where

import Data.Map as M
import Data.Hashable
import Data.Monoid
import GHC.Generics (Generic)
import Control.Monad.State
import Control.Monad.Logger
import qualified Data.Text as T

data TermF a = PlusF a a
             | MultF a a
             | IntConstF Int
             -- the Traversable instance dictates in which order we will
             -- evaluate subterms, for this we don't care
             deriving (Show, Ord, Eq, Functor, Foldable, Traversable, Generic)
instance (Hashable a) => Hashable (TermF a)

newtype Mu f = In { in_ :: f (Mu f)} deriving (Generic)

instance Eq (f (Mu f)) => Eq  (Mu f) where
  In x == In y = x == y
instance Ord (f (Mu f)) => Ord (Mu f) where
  In x `compare` In y = x `compare` y

type Term = Mu TermF

instance Hashable (Mu TermF)

testTerm :: Term
testTerm = let x = (In $ MultF
                     (In $ IntConstF 2)
                     (In $ IntConstF 3))
               y = (In $ MultF
                     (In $ PlusF (In $ IntConstF 1) (In $ IntConstF 1))
                     (In $ IntConstF 3))
           in In $ PlusF x y

type Algebra f a = f a -> a
type MAlgebra f m a = f a -> m a

cata :: Functor f => Algebra f a -> (Mu f -> a)
cata f (In x) = f (fmap (cata f) x)

cataM :: (Traversable f, Monad m) => MAlgebra f m a -> (Mu f -> m a)
cataM f (In x) = (mapM (cataM f) x) >>= f

-- With logging

evalAlgebra :: (MonadLogger m) => MAlgebra TermF m Int
evalAlgebra t = do
  logInfoN ("Evaluating " <> T.pack (show t))
  case t of
    PlusF i1 i2 -> do
      pure $ i1 + i2
    MultF i1 i2 -> do
      pure $ i1 * i2
    IntConstF i -> do
      pure i

evalLog :: (MonadLogger m) => Term -> m Int
evalLog t = cataM evalAlgebra t

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

evalAlgebraCache :: (MonadState (Cache Int) m, MonadLogger m) =>
                  MAlgebra TermF m Int
evalAlgebraCache t = case t of
  PlusF i1 i2 -> do
    logInfoN ("Evaluating plus")
    let h = hash (PlusF (hash i1) (hash i2))
    logInfoN ("Hash is " <> T.pack (show h))
    c <- get
    let maybeA = M.lookup h c
    case maybeA of
      Just v -> do
        logInfoN "Cache hit"
        pure v
      Nothing -> let evaled = i1 + i2 in do
        modify $ M.insert h evaled
        pure evaled
  MultF i1 i2 -> do
    logInfoN "Evaluating mult"
    let h = hash (MultF (hash i1) (hash i2))
    logInfoN ("Hash is " <> T.pack (show h))
    c <- get
    let maybeA = M.lookup h c
    case maybeA of
      Just v -> do
        logInfoN "Cache hit"
        pure v
      Nothing -> let evaled = i1 * i2 in do
        modify $ M.insert h evaled
        pure evaled
  IntConstF i -> do
    logInfoN "Evaluating constant"
    pure i

evalCache :: (MonadState (Cache Int) m, MonadLogger m) =>
             Term -> m Int
evalCache t = cataM evalAlgebraCache t

testCache :: M2 Int
testCache = do
  i <- evalCache testTerm
  logInfoN ("Evaluated to " <> T.pack (show i))
  i2 <- evalCache testTerm
  logInfoN ("Evaluated to " <> T.pack (show i2))
  pure i2

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
               Hashable (Mu f)) =>
              MAlgebra f m a -> (Mu f -> m a)
cataMCache alg = withCaching reeval
  where reeval (In x) = mapM (cataMCache alg) x >>= alg

testCache2 :: M2 Int
testCache2 = do
  i <- cataMCache evalAlgebra testTerm
  logInfoN ("Evaluated to " <> T.pack (show i))
  i2 <- cataMCache evalAlgebra testTerm
  logInfoN ("Evaluated to " <> T.pack (show i2))
  pure i2

-- Try to combine

data Caches a = Caches {
  contentCache:: Cache a,
  hashCache:: Cache Hash
} deriving (Show)

algebraCache2 :: (MonadState (Caches Int) m, MonadLogger m) =>
                 MAlgebra TermF m Int
algebraCache2 t = do
  logInfoN ("Considering " <> T.pack (show t))
  let termHash = hash $ fmap hash t
  logInfoN ("Hash is " <> T.pack (show termHash))
  caches <- get
  let maybeContent = do
        contentHash <- M.lookup termHash (hashCache caches)
        M.lookup contentHash (contentCache caches)
  case maybeContent of
    Just v -> do
      logInfoN "Cache hit"
      pure v
    Nothing -> do
      logInfoN "Cache miss"
      evaled <- evalAlgebra t
      let contentHash = hash evaled
      modify $ \c -> Caches {
        contentCache = M.insert contentHash evaled (contentCache c),
        hashCache = M.insert termHash contentHash (hashCache c)
      }
      pure evaled

type M3 a = (StateT (Caches a)) (LoggingT IO) a
runM3 :: M3 a -> IO (a, Caches a)
runM3 m = runStdoutLoggingT (runStateT m Caches { contentCache = M.empty, hashCache = M.empty } )

testCache3 :: M3 Int
testCache3 = do
  i <- cataM algebraCache2 testTerm
  logInfoN ("Evaluated to " <> T.pack (show i))
  i2 <- cataM algebraCache2 testTerm
  logInfoN ("Evaluated to " <> T.pack (show i2))
  pure i2

-- Try and propagate with just hashes

data Result m a = Value a | Content Hash (m a)
instance Show a => Show (Result m a) where
  show (Value v) = show v
  show (Content h _) = show h

resultToHash :: (Hashable a) => Result m a -> Hash
resultToHash (Value a) = hash a
resultToHash (Content h _) = h

resultToValue :: (Hashable a, Monad m) => Result m a -> m a
resultToValue (Value a) = pure a
resultToValue (Content _ ma) = ma

algebraCache3 :: (MonadState (Caches Int) m, MonadLogger m) =>
                 MAlgebra TermF m (Result m Int)
algebraCache3 t = do
  let termHash = hash $ fmap resultToHash t
  logInfoN ("Considering " <> T.pack (show t) <> ", hash is " <> T.pack (show termHash))
  caches <- get
  let maybeContentHash = M.lookup termHash (hashCache caches)
  let maybeContent = maybeContentHash >>= (\contentHash -> M.lookup contentHash (contentCache caches))
  let computation = case maybeContent of
        Just value -> do
          logInfoN "Content cache hit"
          pure value
        Nothing -> do
          logInfoN "Content cache miss"
          subtermsEvaled <- mapM resultToValue t
          evaled <- evalAlgebra subtermsEvaled
          let contentHash = hash evaled
          modify $ \c -> Caches {
            contentCache = M.insert contentHash evaled (contentCache c),
            hashCache = M.insert termHash contentHash (hashCache c)
          }
          pure evaled
  case maybeContentHash of
    Just contentHash -> do
      logInfoN "Hash cache hit"
      pure $ Content contentHash computation
    Nothing -> do
      logInfoN "Hash cache miss"
      value <- computation
      pure $ Value value

testCache4 :: M3 Int
testCache4 = do
  res <- do
    logInfoN ("ATTEMPT 1")
    i <- cataM algebraCache3 testTerm
    logInfoN ("Evaluated to " <> T.pack (show i))
    logInfoN ("ATTEMPT 2")
    i2 <- cataM algebraCache3 testTerm
    logInfoN ("Evaluated to " <> T.pack (show i2))
    pure i2
  resultToValue res
