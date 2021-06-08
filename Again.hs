{-# OPTIONS_GHC -W #-}
{-# LANGUAGE GADTs, DataKinds, KindSignatures, StandaloneDeriving, TypeFamilies, TypeOperators, ScopedTypeVariables, TypeApplications, AllowAmbiguousTypes, TemplateHaskell, QuasiQuotes, PolyKinds, FlexibleContexts, RankNTypes #-}
{-# LANGUAGE UndecidableInstances #-} -- TODO meh

-- import Data.Type.Equality

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

data CanInduce a = Yes a | No a | Inv

type family IfCanInduce (x :: CanInduce a) (f :: a -> b) :: CanInduce b where
    IfCanInduce (Yes a) f = Yes (f a)
    IfCanInduce (No a) f = Inv
    IfCanInduce Inv f = Inv

type family (a :: PNat) <~> (b :: PNat) :: CanInduce PNat where
    I <~> I = Yes I
    I <~> S n = No (S n)
    S n <~> I = No (S n)
    S m <~> S n = IfCanInduce (m <~> n) S

type family Ok (x :: CanInduce a) :: Maybe a where
    Ok Inv = Nothing
    Ok (No a) = Just a
    Ok (Yes a) = Just a

{-
broadcastOneL :: SPNat n -> ((I <~> n ~ n) => t) -> t
broadcastOneL (SS n) t = broadcastOneL n t
broadcastOneL _ t = t

broadcastOneR :: SPNat n -> ((n <~> I ~ n) => t) -> t
broadcastOneR (SS n) t = broadcastOneR n t
broadcastOneR _ t = t

broadcastEq :: SPNat n -> ((n <~> n ~ n) => t) -> t
broadcastEq (SS n) t = broadcastEq n t
broadcastEq _ t = t
-}

-- proof :: (Ok (S m <~> S n) ~ Just k) => SPNat (S m) -> SPNat (S n) -> SPNat (S n) :~: SPNat k
proof' :: (Ok ((S m) <~> (S n)) ~ Just k) => SPNat (S m) -> SPNat (S n) -> ((Ok (S m <~> S n) ~ Just (S m)) => t) -> t
proof' (SS SI) (SS SI) t = t
proof' (SS m) (SS n) t = (proof' m n) t

broadcast :: (Ok (m <~> n) ~ Just k) => SPNat m -> SPNat n -> SPNat k
broadcast SI SI = SI
broadcast SI (SS n) = SS n
broadcast (SS n) SI = SS n
-- broadcast (SS m) (SS n) = castWith (proof (SS m) (SS n)) (SS n)
broadcast (SS m) (SS n) = proof' (SS m) (SS n) (SS m)
