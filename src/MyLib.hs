{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}

module MyLib where

import Control.Category
import Control.Monad ((>=>))
import Control.Monad.Bayes.Class (MonadDistribution (..))
import Data.Fin (Fin (..))
import Data.Profunctor (Profunctor (..))
import Data.Profunctor.Choice
import Data.Profunctor.Strong
import Data.Profunctor.Traversing
import Data.Vec.Lazy (Vec (..), itraverse)
import Prelude hiding (id, (.))
import Data.Nat (Nat(..))
import Data.Function ((&))
import Data.Vec.Lazy.Lens (ix)
import Control.Lens ((+~))
import Data.Functor ((<&>))

data Lens m a b where
  LensBayes :: BayesLens m a b -> Lens m a b
  LensBayes2 :: BayesLens2 m a b -> Lens m a b
  LensIso :: Iso a b -> Lens m a b

instance (Monad m) => Category (Lens m) where
  id = LensIso $ Iso id id
  LensBayes (BayesLens l1 u1) . LensBayes (BayesLens l2 u2) =
    LensBayes $
      BayesLens
        { likelihood = l1 >=> l2
        , update = \a mc -> do
            c <- mc
            b <- u2 a $ l1 c
            u1 b mc
        }
  LensIso (Iso f g) . LensBayes (BayesLens l u) =
    LensBayes
      BayesLens
        { likelihood = l . g
        , update = \a mc -> fmap f $ u a $ g <$> mc
        }
  LensIso (Iso f g)
    . LensBayes2
        BayesLens2{inferenceState, interpret, l, u} =
      LensBayes2
        BayesLens2
          { inferenceState
          , interpret
          , l = fmap f . l
          , u = u . g
          }
  LensBayes2
    BayesLens2{inferenceState, interpret, l, u}
    . LensIso (Iso f g) =
      LensBayes2
        BayesLens2{inferenceState, interpret = fmap g . interpret, l = l . f, u = u}
  _ . _ = error "to do"

data BayesLens m observation latent = BayesLens
  { likelihood :: latent -> m observation
  , update :: observation -> m latent -> m latent
  }

parBL :: (Applicative m) => BayesLens m a b -> BayesLens m c d -> BayesLens m (a, c) (b, d)
parBL (BayesLens l1 u1) (BayesLens l2 u2) =
  BayesLens
    { likelihood = \(b, d) -> (,) <$> l1 b <*> l2 d
    , -- FIXME this decorrelates b & d
      update = \(a, c) mbd -> (,) <$> u1 a (fst <$> mbd) <*> u2 c (snd <$> mbd)
    }

{-
gauss :: (MonadDistribution m) => BayesLens m Double Double
gauss =
  BayesLens
    { likelihood = (`normal` 1)
    , update = \x n -> _
    }
-}

{-
N(x, d) ~ exp(-1/2 * (x/d)^2)
p(theta) = N(theta - a, d)
p(x | theta) = N(x - theta, 1)
p(theta | x) = p(theta) * p(x | theta) / p(x)
~ N(theta - a, d) * N(x - theta, 1)
~ exp(-1/2 * (((theta-a)/d)^2 + (x - theta)^2))
~ ...
~ N(mu, sigma)
  sigma = 1/ (1 / d + 1) = d / (d + 1)

-}

data Iso a b = Iso
  { f :: a -> b
  , g :: b -> a
  }

instance Category Iso where
  id = Iso id id
  Iso f1 g1 . Iso f2 g2 = Iso (f1 . f2) (g2 . g1)

add :: (Num a) => a -> Iso a a
add a = Iso (+ a) (flip (-) a)

multiply :: (Fractional a) => a -> Iso a a
multiply a = Iso (* a) (/ a)

data BayesLens2 m a b = forall s.
  BayesLens2
  { inferenceState :: s
  , interpret :: s -> m a
  , l :: a -> m b
  , u :: b -> s -> m s
  }

gauss ::
  (MonadDistribution m) =>
  -- | Prior guess for mu, mean
  Double ->
  -- | Prior guess for mu, std dev
  Double ->
  -- | Standard deviation of gauss (fix, will not be inferred)
  Double ->
  BayesLens2 m Double Double
gauss mu0 sigma0 s =
  BayesLens2
    { inferenceState = (mu0, sigma0)
    , interpret = uncurry normal
    , l = (`normal` s)
    , u = \x (mu, sigma) ->
        let nominator = (sigma * sigma + s * s)
            sigma' = sqrt $ (sigma * sigma * s * s) / nominator
         in pure ((sigma * sigma * mu + s * s * x) / nominator, sigma')
    }

-- | A Bernoulli draw with a Beta prior
coin ::
  -- \| alpha of the Beta prior
  (MonadDistribution m) =>
  Double ->
  -- | beta of the Beta prior
  Double ->
  BayesLens2 m Double Bool
coin alpha0 beta0 =
  BayesLens2
    { inferenceState = (alpha0, beta0)
    , interpret = uncurry beta
    , l = bernoulli
    , u = \headsOrTails (alpha, beta_) -> pure $ if headsOrTails then (alpha + 1, beta_) else (alpha, beta_ + 1)
    }

compose2 :: (Monad m) => BayesLens2 m a b -> BayesLens2 m b c -> BayesLens2 m a c
compose2 (BayesLens2 s10 i1 l1 u1) (BayesLens2 s20 i2 l2 u2) =
  BayesLens2
    { inferenceState = (s10, s20)
    , interpret = \(s1, _s2) -> i1 s1
    , l = l1 >=> l2
    , u = \c (s1, s2) -> do
        s2' <- u2 c s2
        b <- i2 s2'
        s1' <- u1 b s1
        pure (s1', s2')
    }

upd2 :: (Functor m) => BayesLens2 m a b -> b -> m (BayesLens2 m a b)
upd2
  BayesLens2
    { inferenceState
    , interpret
    , l
    , u
    }
  b = do
    inferenceState' <- u b inferenceState
    pure
      BayesLens2
        { interpret
        , l
        , u
        , inferenceState = inferenceState'
        }

par2 :: (Applicative m) => BayesLens2 m a b -> BayesLens2 m c d -> BayesLens2 m (a, c) (b, d)
par2 (BayesLens2 s10 i1 l1 u1) (BayesLens2 s20 i2 l2 u2) =
  BayesLens2
    { inferenceState = (s10, s20)
    , interpret = \(s1, s2) -> (,) <$> i1 s1 <*> i2 s2
    , l = \(a, c) -> (,) <$> l1 a <*> l2 c
    , u = \(b, d) (s1, s2) -> (,) <$> u1 b s1 <*> u2 d s2
    }

-- TODO Generalise to heterogeneous product
-- TODO now we can apply an iso to a record, this should be done generiacally
-- | This doesn't combine the two inference states well though. It can't if we don't decide for a joint prior on a
fan :: (Applicative m, Monad m, MonadDistribution m) => BayesLens2 m a b -> BayesLens2 m a c -> BayesLens2 m a (b, c)
fan (BayesLens2 s10 i1 l1 u1) (BayesLens2 s20 i2 l2 u2) =
  BayesLens2
    { inferenceState = (s10, s20)
    , interpret = \(s1, s2) -> do
        bOrC <- bernoulli 0.5
        if bOrC then i1 s1 else i2 s2
    , l = \a -> (,) <$> l1 a <*> l2 a
    , u = \(b, c) (s1, s2) -> (,) <$> u1 b s1 <*> u2 c s2
    }

iid :: (Monad m) => BayesLens2 m a b -> BayesLens2 m a [b]
iid BayesLens2{inferenceState, interpret, l, u} =
  BayesLens2
    { inferenceState
    , interpret
    , l = traverse l . repeat
    , u = foldr (\b u' -> u' >=> u b) pure
    }

-- FIXME rather should have a beta in here as well. This is like a delta prior on p.
-- Ideally it would be possible to compose a Dirichlet/beta with other distributions
choose :: (Monad m, MonadDistribution m) => Double -> BayesLens2 m a b -> BayesLens2 m a c -> BayesLens2 m a (Either b c)
choose p (BayesLens2 s10 i1 l1 u1) (BayesLens2 s20 i2 l2 u2) =
  BayesLens2
    { inferenceState = (s10, s20)
    , interpret = \(s1, s2) -> do
        oneOrTwo <- bernoulli p
        if oneOrTwo then i1 s1 else i2 s2
    , l = \a -> do
        oneOrTwo <- bernoulli p
        if oneOrTwo then Left <$> l1 a else Right <$> l2 a
    , u = \case
        (Left b) -> \(s1, s2) -> (,s2) <$> u1 b s1
        (Right c) -> \(s1, s2) -> (s1,) <$> u2 c s2
    }

categorical :: (Monad m, MonadDistribution m) => Vec (S n) Double -> BayesLens2 m (Vec (S n) Double) (Fin (S n))
categorical alphas0 =
  BayesLens2
    { inferenceState = alphas0
    , interpret = \alphas -> do
        -- See https://en.wikipedia.org/wiki/Dirichlet_distribution#From_gamma_distribution
        weights <- mapM (`gamma` 1) alphas
        let totalWeight = sum weights
        return $ (/ totalWeight) <$> weights
    , l
    , u = \i v -> pure $ v & ix i +~ 1
    }
    where
      l :: MonadDistribution m => Vec (S n) Double -> m (Fin (S n))
      l (_p ::: VNil) = pure FZ -- Assume p = 1
      l (p ::: v@(_ ::: _)) = do
        drawThisPosition <- bernoulli p
        if drawThisPosition then pure FZ else FS <$> l v

sample :: Monad m => BayesLens2 m a b -> m b
sample BayesLens2 {inferenceState, interpret, l} = interpret inferenceState >>= l

sampleLatent :: Monad m => BayesLens2 m a b -> m a
sampleLatent BayesLens2 {inferenceState, interpret} = interpret inferenceState

process :: Functor m => s -> BayesLens2 m (a, s) (b, s) -> BayesLens2 m a b
process s0 BayesLens2 {inferenceState, interpret, l, u} = BayesLens2
  {inferenceState = (inferenceState, s0)
  , interpret = \(infState, _) -> fst <$> interpret infState
  , l = fmap fst . l . (, _)
  , u = \b (infState, s) -> _ <$> u (b, s) infState
  }

process' :: Monad m => s -> BayesLens2 m (a, s) (b, s) -> BayesLens2 m (a, s) b
process' s0 BayesLens2 {inferenceState, interpret, l, u} = BayesLens2
  {inferenceState = (inferenceState, s0)
  , interpret = interpret . fst
  , l = fmap fst . l
  , u = \b (infState, s) -> do
      -- FIXME missing a way to condition s
      infState' <- u (b, s) infState
      return (infState', _)
  }

crp :: MonadDistribution m => Double -> (a -> m b) -> BayesLens2 m a b
crp alpha f = BayesLens2
  {inferenceState = []
  , interpret = _
  , l = f
  , u = _
  }
  {-
  \inferenceState -> do
      drawNew <- bernoulli $ alpha / (alpha + fromIntegral (length inferenceState) - 1)
      if drawNew
        then _
        else _
  -}

-- Not sure what value crp adds like this
crp' :: MonadDistribution m => Double -> BayesLens2 m a b -> BayesLens2 m a b
crp' alpha BayesLens2 {inferenceState, interpret, l, u} = BayesLens2
  { inferenceState = []
  , interpret = \case
      [] -> interpret inferenceState
      s : ss -> _ -- FIXME choose one of those at random
  , l
  , u = \b ss -> do
      drawNew <- bernoulli $ alpha / (alpha + fromIntegral (length ss) - 1)
      if drawNew
        then u b inferenceState <&> (: ss)
        else _ -- Huh. Do i run u on all states? Look up how this is typically done
  }

-- TODO Generalise

data BayesLensH m a (bs :: [Type]) = BayesLensH ... -- TODO just like BayesLens or BayesLens2, but outputs an NP I bs, and inputs an HS I bs. Alternatively inputs an HP Maybe bs
-- TODO generically connect to higher kinded datatypes
-- Composing these is a multicategory. Is there a library for that?
-- Write down special cases to see whether this is usable

-- TODO find riht type classes for fan & par
-- TODO find type class or write one for composition with isos

-- But back doesn't work
to2 :: BayesLens m a b -> BayesLens2 m a b
to2 = _

-- FIXME generalies to heterogeneous
observe :: BayesLens2 m a b -> b -> BayesLens2 m a ()
-- This should fix a for all future samplings, maybe this can be used to implment delayed sampling
sample :: BayesLens2 m a b -> m (a, BayesLens2 m a b)

-- TODO  Is fan the right thing for delayed sampling?
