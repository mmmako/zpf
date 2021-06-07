{-# OPTIONS_GHC -W #-}
{-# LANGUAGE GADTs, DataKinds, KindSignatures, StandaloneDeriving, TypeFamilies, TypeOperators, ScopedTypeVariables, TypeApplications, AllowAmbiguousTypes, TemplateHaskell, QuasiQuotes, PolyKinds, FlexibleContexts #-}

import Data.Type.Equality

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

type family (a :: PNat) <~> (b :: PNat) :: Maybe PNat where
    n <~> n = Just n
    n <~> I = Just n
    I <~> n = Just n
    _ <~> _ = Nothing

vzip :: Vec n a -> Vec n b -> Vec n (a, b)
vzip = undefined

broadcast :: (m <~> n ~ Just k) => Vec m a -> Vec n b -> Vec k (a, b)
broadcast (V a) (V b) = V (a, b)
broadcast (V a) (b :> bs) = (a, b) :> (broadcast (V a) bs)
broadcast (a :> as) (V b) = (a, b) :> (broadcast as (V b))
broadcast as@(_ :> _) bs@(_ :> _) = vzip (castWith p1 as) (castWith p2 bs)
    where (p1, p2) = something as bs

something :: ((S m) <~> (S n) ~ Just k) => Vec (S m) a -> Vec (S n) b ->
    (Vec (S m) c :~: Vec k c, Vec (S n) d :~: Vec k d)
something = undefined

something' :: ((S m) <~> (S n) ~ Just k) => SPNat (S m) -> SPNat (S n) ->
    (SPNat (S m) :~: SPNat k, SPNat (S n) :~: SPNat k)
something' (SS m) (SS n) = (Refl, Refl)

