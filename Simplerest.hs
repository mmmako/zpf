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
data Vec :: Maybe PNat -> * -> * where
    Inv  :: Vec Nothing a
    V    :: a -> Vec (Just I) a
    (:>) :: a -> Vec (Just n) a -> Vec (Just (S n)) a

deriving instance Show a => Show (Vec n a)

data Broadcasts (m :: PNat) (n :: PNat) (k :: Maybe PNat) where
    Equal :: Broadcasts n n (Just n)
    LOne :: Broadcasts I n (Just n)
    ROne :: Broadcasts n I (Just n)
    Nope :: Broadcasts m n Nothing

{-
vzip :: Vec n a -> Vec n b -> Vec n (a, b)
vzip (V a) (V b) = V (a, b)
vzip (a :> as) (b :> bs) = (a, b) :> vzip as bs

broadcast :: Broadcasts m n (Just k) -> Vec m a -> Vec n b -> Vec k (a, b)
broadcast Equal as bs = vzip as bs
broadcast LOne (V a) (b :> bs) = (a, b) :> broadcast LOne (V a) bs
broadcast ROne (a :> as) (V b) = (a, b) :> broadcast ROne as (V b)
-- TODO i don't like these being here, but oh well
broadcast LOne (V a) (V b) = V (a, b)
broadcast ROne (V a) (V b) = V (a, b)
-}

oneEq :: Broadcasts I n (Just m) -> n :~: m
oneEq Equal = Refl
oneEq LOne = Refl
oneEq ROne = Refl

eq :: Broadcasts (S m) (S n) (Just k) -> m :~: n
eq Equal = Refl

-- TODO this needs to be constrained somehow, and that needs... constraints, right?
-- getBroadcast :: Vec (Just m) a -> Vec (Just n) b -> Broadcasts m n k
getBroadcast :: SPNat m -> SPNat n -> Broadcasts m n k
getBroadcast SI SI = LOne
{-
getBroadcast _ SI = ROne
getBroadcast (SS m@(SS _)) (SS n@(SS _)) = Equal

type family CanBroadcast (m :: PNat) (n :: PNat) :: PNat where
    CanBroadcast n n = n
    CanBroadcast I n = n
    CanBroadcast n I = n
    CanBroadcast m n = TypeError (Text "‘CanBroadcast’ didn't match"
                         :$$: Text "when applied to the types ‘"
                         :<>: ShowType m :<>: Text "’ and ‘" :<>: ShowType n :<>: Text "’") 
-}
