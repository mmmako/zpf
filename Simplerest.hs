{-# OPTIONS_GHC -W #-}
{-# LANGUAGE GADTs, DataKinds, KindSignatures, StandaloneDeriving, TypeFamilies, TypeOperators, ScopedTypeVariables, TypeApplications, AllowAmbiguousTypes, TemplateHaskell, QuasiQuotes, PolyKinds, FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-} -- TODO Meh

import Data.Type.Equality
import GHC.TypeLits
-- import Data.Proxy

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

data Broadcasts (m :: PNat) (n :: PNat) (k :: PNat) where
    Equal :: Broadcasts n n n
    LOne :: Broadcasts I n n
    ROne :: Broadcasts n I n

vzip :: Vec n a -> Vec n b -> Vec n (a, b)
vzip (V a) (V b) = V (a, b)
vzip (a :> as) (b :> bs) = (a, b) :> vzip as bs

broadcast :: Broadcasts m n k -> Vec m a -> Vec n b -> Vec k (a, b)
broadcast Equal as bs = vzip as bs
broadcast LOne (V a) (b :> bs) = (a, b) :> broadcast LOne (V a) bs
broadcast ROne (a :> as) (V b) = (a, b) :> broadcast ROne as (V b)
-- TODO i don't like these being here, but oh well
broadcast LOne (V a) (V b) = V (a, b)
broadcast ROne (V a) (V b) = V (a, b)

oneEq :: Broadcasts I n m -> n :~: m
oneEq Equal = Refl
oneEq LOne = Refl
oneEq ROne = Refl

eq :: Broadcasts (S m) (S n) k -> m :~: n
eq Equal = Refl

-- TODO this needs to be constrained somehow, and that needs... constraints, right?
-- getBroadcast :: Vec m a -> Vec n b -> Broadcasts m n k -- (Broadcasts m n k, Vec k (a, b))
getBroadcast :: CanBroadcast m n ~ k => SPNat m -> SPNat n -> Broadcasts m n k
getBroadcast SI _ = LOne
getBroadcast _ SI = ROne
getBroadcast (SS m@(SS _)) (SS n@(SS _)) = Equal

type family CanBroadcast (m :: PNat) (n :: PNat) :: PNat where
    CanBroadcast n n = n
    CanBroadcast I n = n
    CanBroadcast n I = n
    CanBroadcast m n = TypeError (Text "‘CanBroadcast’ didn't match"
                         :$$: Text "when applied to the types ‘"
                         :<>: ShowType m :<>: Text "’ and ‘" :<>: ShowType n :<>: Text "’") 
