{-|
Description: annihilative semigroups
Copyright: (c) Keith Wygant, 2022
License: 0BSD
Stability: experimental
Portability: GHC (FlexibleContexts, UndecidableInstances)

This module provides the hierarchy 'LeftAnnihilative' => 'Annihilative'. Annihilative semigroups are like multiplication with the annihilative element ('nihil') being zero. The 'LeftAnnihilative' superclass is needed for instances that cannot undo actions that have already been performed. Consider @'Ap' 'IO' a@: Actions performed before executing 'nihil' cannot be undone.
-}
{-# LANGUAGE FlexibleContexts -- For Functor.Product
           , UndecidableInstances -- For Functor.Product
   #-}


module Data.Semigroup.Annihilative where


import Control.Monad
import Data.Semigroup
import Data.Monoid
import Data.Functor.Contravariant
import Data.Functor.Const
import Data.Functor.Identity
import qualified Data.Functor.Product as Functor
import Data.Proxy
import qualified GHC.Event as GHC
import qualified GHC.Generics as G


class (Semigroup a)=> LeftAnnihilative a where
{-^ Law:

prop> \ x -> leftNihil '<>' x  ==  leftNihil

(This law does not apply when @x@ is computationally bottom.)
If you think of '<>' as multiplication and 'mempty' as one, then @leftNihil@ is zero.
-}
    leftNihil :: a

class (LeftAnnihilative a)=> Annihilative a
{-^ Law:

prop> \ x -> x '<>' 'leftNihil' == 'leftNihil'

-}

nihil :: (Annihilative a)=> a
nihil = leftNihil
{-# INLINE nihil #-}


--- Instances ---

instance Annihilative ()
instance LeftAnnihilative () where leftNihil = ()

instance Annihilative (Proxy a)
instance LeftAnnihilative (Proxy a) where leftNihil = Proxy

instance Annihilative All
instance LeftAnnihilative All where leftNihil = All False

instance Annihilative Any
instance LeftAnnihilative Any where leftNihil = Any True


instance (Annihilative a)=> Annihilative (Maybe a)
instance (LeftAnnihilative a)=> LeftAnnihilative (Maybe a) where
    leftNihil = Just leftNihil

instance (Annihilative a)=> Annihilative (Identity a)
instance (LeftAnnihilative a)=> LeftAnnihilative (Identity a) where
    leftNihil = Identity leftNihil

instance (Annihilative a)=> Annihilative (Dual a)
instance (Annihilative a)=> LeftAnnihilative (Dual a) where
    leftNihil = Dual leftNihil

instance (Annihilative c)=> Annihilative (Const c a)
instance (LeftAnnihilative c)=> LeftAnnihilative (Const c a) where
    leftNihil = Const leftNihil

instance (Num a)=> LeftAnnihilative (Product a) where leftNihil = 0 -- ^ This is an assumption about 'Num' that may not hold for some instances.

instance (Ord a, Bounded a)=> Annihilative (Max a)
instance (Ord a, Bounded a)=> LeftAnnihilative (Max a) where leftNihil = maxBound
instance (Ord a, Bounded a)=> Annihilative (Min a)
instance (Ord a, Bounded a)=> LeftAnnihilative (Min a) where leftNihil = minBound

instance (Annihilative a, Annihilative b)=> Annihilative (a, b)
instance (LeftAnnihilative a, LeftAnnihilative b)=> LeftAnnihilative (a, b) where
    leftNihil = (leftNihil, leftNihil)

instance (Annihilative a, Annihilative b, Annihilative c)=> Annihilative (a, b, c)
instance (LeftAnnihilative a, LeftAnnihilative b, LeftAnnihilative c)=> LeftAnnihilative (a, b, c) where
    leftNihil = (leftNihil, leftNihil, leftNihil)

instance (Annihilative a, Annihilative b, Annihilative c, Annihilative d)=> Annihilative (a, b, c, d)
instance (LeftAnnihilative a, LeftAnnihilative b, LeftAnnihilative c, LeftAnnihilative d)=> LeftAnnihilative (a, b, c, d) where
    leftNihil = (leftNihil, leftNihil, leftNihil, leftNihil)

instance (Annihilative b)=> Annihilative (a -> b)
instance (LeftAnnihilative b)=> LeftAnnihilative (a -> b) where
    leftNihil = pure leftNihil

instance (Annihilative a)=> Annihilative (Op a b)
instance (LeftAnnihilative a)=> LeftAnnihilative (Op a b) where
    leftNihil = Op leftNihil

instance Annihilative (Predicate a)
instance LeftAnnihilative (Predicate a) where
    leftNihil = Predicate (pure False) -- ^ Predicate is Op All.

instance Annihilative (Equivalence a)
instance LeftAnnihilative (Equivalence a) where
    leftNihil = Equivalence (\ _ _ -> False)

instance (Semigroup (Functor.Product m n a), Annihilative (m a), Annihilative (n a))=> Annihilative (Functor.Product m n a)
instance (Semigroup (Functor.Product m n a), LeftAnnihilative (m a), LeftAnnihilative (n a))=> LeftAnnihilative (Functor.Product m n a) where
    leftNihil = Functor.Pair leftNihil leftNihil

instance (MonadPlus m, Semigroup a)=> LeftAnnihilative (Ap m a) where
{-^ This works for 'MonadPlus' and 'LeftAnnihilative', but not 'Alternative' or 'Annihilative'. 'MonadPlus' guarantees that actions are executed from left to right and stop at 'mzero', while with 'Alternative' they could be executed from right to left (which would be @RightAnnihilative@). -}
   leftNihil = Ap mzero

--- GHC Instances ---
instance Annihilative GHC.Lifetime
instance LeftAnnihilative GHC.Lifetime where leftNihil = GHC.MultiShot

--- Generics ---
instance Annihilative (G.U1 a)
instance LeftAnnihilative (G.U1 a) where leftNihil = G.U1

instance (Annihilative c)=> Annihilative (G.K1 i c p)
instance (LeftAnnihilative c)=> LeftAnnihilative (G.K1 i c p) where
    leftNihil = G.K1 leftNihil

instance (Annihilative (m a))=> Annihilative (G.Rec1 m a)
instance (LeftAnnihilative (m a))=> LeftAnnihilative (G.Rec1 m a) where
    leftNihil = G.Rec1 leftNihil

instance (Annihilative (m a), Annihilative (n a))=> Annihilative ((G.:*:) m n a) where
instance (LeftAnnihilative (m a), LeftAnnihilative (n a))=> LeftAnnihilative ((G.:*:) m n a) where
    leftNihil = leftNihil G.:*: leftNihil

instance (Annihilative (m (n a)))=> Annihilative ((G.:.:) m n a)
instance (LeftAnnihilative (m (n a)))=> LeftAnnihilative ((G.:.:) m n a) where leftNihil = G.Comp1 leftNihil

instance (Annihilative (m a))=> Annihilative (G.M1 i c m a)
instance (LeftAnnihilative (m a))=> LeftAnnihilative (G.M1 i c m a) where leftNihil = G.M1 leftNihil
