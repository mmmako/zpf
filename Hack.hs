{-# OPTIONS_GHC -W #-}
{-# LANGUAGE GADTs, DataKinds, KindSignatures, StandaloneDeriving, TypeFamilies, TypeOperators, ScopedTypeVariables, TypeApplications, AllowAmbiguousTypes, TemplateHaskell, QuasiQuotes, PolyKinds, FlexibleContexts, RankNTypes #-}

data PNat :: * where
    I :: PNat
    S :: PNat -> PNat deriving Show

data SPNat (n::PNat) where
    SI :: SPNat I
    SS :: SPNat n -> SPNat (S n)

deriving instance Show (SPNat n)

infixr 6 :>
data Vec :: PNat -> * -> * where
    V    :: a -> Vec I a
    (:>) :: a -> Vec n a -> Vec (S n) a

deriving instance Show a => Show (Vec n a)

instance Functor (Vec n) where
    fmap f (V a) = V (f a)
    fmap f (a :> as) = f a :> fmap f as

type family (m :: PNat) <~> (n :: PNat) :: Bool where
    n <~> n = True
    n <~> I = True
    I <~> n = True
    _ <~> _ = False

type family (m :: PNat) <~~> (n :: PNat) :: PNat where
    I <~~> n = n
    n <~~> I = n
    (S m) <~~> (S n) = S (m <~~> n)

head :: Vec n a -> a
head (V a) = a
head (a :> _) = a

match :: a -> Vec n b -> Vec n (a, b)
match a (V b) = V (a, b)
match a (b :> bs) = (a, b) :> match a bs

broadcastUnsafe :: Vec m a -> Vec n b -> Vec (m <~~> n) (a, b)
broadcastUnsafe (V a) bs = match a bs
broadcastUnsafe (a :> as) (b :> bs) = (a, b) :> broadcastUnsafe as bs
broadcastUnsafe as (V b) = (\(x, y) -> (y, x)) <$> match b as

broadcast :: m <~> n ~ True => Vec m a -> Vec n b -> Vec (m <~~> n) (a, b)
broadcast = broadcastUnsafe
