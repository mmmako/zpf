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

type family (a :: PNat) <~> (b :: PNat) :: PNat where
    n <~> n = n
    n <~> I = n
    I <~> n = n

broadcastSucc :: SPNat m -> SPNat n -> Vec (S (m <~> n)) a :~: Vec ((S m <~> S n)) a
broadcastSucc = undefined

vlength :: Vec n a -> SPNat n
vlength (V _) = SI
vlength (_ :> t) = SS (vlength t)

broadcast :: Vec m a -> Vec n b -> Vec (m <~> n) (a, b)
broadcast (V a) (V b) = V (a, b)
broadcast (V a) (b :> v) = (a, b) :> (broadcast (V a) v)
broadcast (a :> v) (V b) = (a, b) :> (broadcast v (V b))
-- broadcast (a :> as) (b :> bs) = (a, b) :> (broadcast as bs)
broadcast (a :> as) (b :> bs) = castWith (broadcastSucc (vlength as) (vlength bs)) $ (a, b) :> (broadcast as bs)
