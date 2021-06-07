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

something :: SPNat n -> SPNat m -> ((S n) <~> m) :~: (S n)
something _ SI = Refl
something n (SS m) = undefined -- gcastWith (something n m) Refl

-- broadcastSucc :: SPNat m -> SPNat n -> Vec (S (m <~> n)) a :~: Vec ((S m <~> S n)) a
-- broadcastSucc m n = apply Refl (apply Refl (broadcastSucc' m n))
broadcastSucc :: Vec m a -> Vec n b -> Vec (S (m <~> n)) c :~: Vec ((S m <~> S n)) c
broadcastSucc = undefined -- (V _) (V _) = Refl
-- broadcastSucc x@(V _) (_ :> xs) = apply (Refl @S) (broadcastSucc x xs)

{-
broadcastSucc' :: SPNat m -> SPNat n -> S (m <~> n) :~: (S m <~> S n)
broadcastSucc' SI SI = Refl
broadcastSucc' (SS n) (SS n') = apply Refl (broadcastSucc' n n')
-}

-- vlength :: Vec n a -> SPNat n
-- vlength (V _) = SI
-- vlength (_ :> t) = SS (vlength t)

broadcast' :: (m <~> n ~ Just k) => Vec m a -> Vec n b -> Vec k (a, b)
broadcast' = undefined

broadcast :: Vec m a -> Vec n b -> Vec (m <~> n) (a, b)
broadcast (V a) (V b) = V (a, b)
broadcast (V a) (b :> v) = (a, b) :> (broadcast (V a) v)
broadcast (a :> v) (V b) = (a, b) :> (broadcast v (V b))
-- broadcast (a :> as) (b :> bs) = (a, b) :> (broadcast as bs)
-- broadcast (a :> as) (b :> bs) = castWith (broadcastSucc (vlength as) (vlength bs)) $ (a, b) :> (broadcast as bs)
broadcast (a :> as) (b :> bs) = castWith (broadcastSucc as bs) $ (a, b) :> (broadcast as bs)
