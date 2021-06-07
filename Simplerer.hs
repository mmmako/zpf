{-# OPTIONS_GHC -W #-}
{-# LANGUAGE GADTs, DataKinds, KindSignatures, StandaloneDeriving, TypeFamilies, TypeOperators, ScopedTypeVariables, TypeApplications, AllowAmbiguousTypes, TemplateHaskell, QuasiQuotes, PolyKinds, FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-} -- TODO Meh

import Data.Type.Equality
import GHC.TypeLits

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

{-
type family Equal (a :: PNat) (b :: PNat) :: Maybe PNat where
    Equal I I = Just I
    Equal (S m) (S n) = Equal m n
    Equal _ _ = Nothing

type family LeftI (a :: PNat) (b :: PNat) :: Maybe PNat where
    LeftI I I = Just I
    LeftI I (S n) = S (LeftI I n)
    LeftI _ _ = Nothing

type family RightI (a :: PNat) (b :: PNat) :: Maybe PNat where
    RightI I I = Just I
    RightI (S n) I = S (RightI n I)
    RightI _ _ = Nothing
-}

type family (a :: PNat) <~> (b :: PNat) :: PNat where
    S n <~> S n = S (n <~> n)
    n <~> I = n
    I <~> n = n
    m <~> n = TypeError (Text "‘<~>’ didn't match"
                         :$$: Text "when applied to the types ‘"
                         :<>: ShowType m :<>: Text "’ and ‘" :<>: ShowType n :<>: Text "’") 

vzip :: Vec n a -> Vec n b -> Vec n (a, b)
vzip = undefined

broadcast :: (m <~> n ~ k) => Vec m a -> Vec n b -> Vec k (a, b)
broadcast (V a) (V b) = V (a, b)
broadcast (V a) (b :> bs) = (a, b) :> (broadcast (V a) bs)
broadcast (a :> as) (V b) = (a, b) :> (broadcast as (V b))
broadcast as@(_ :> _) bs@(_ :> _) = vzip (castWith p1 as) (castWith p2 bs)
    where (p1, p2) = something as bs

{-
something1 :: (I <~> n ~ Just k) => SPNat n -> n :~: k
something1 SI = Refl
something1 (SS _) = Refl
-}

{-
something2 :: ((S m) <~> (S n) ~ Just k) => SPNat m -> SPNat n -> SPNat k -> m :~: n
something2 (SS SI) (SS SI) (SS SI) = Refl
something2 (SS m) (SS n) (SS k) = apply (Refl @S) (something2 m n k)
-}

something :: ((S m) <~> (S n) ~ k) => Vec (S m) a -> Vec (S n) b ->
    (Vec (S m) c :~: Vec k c, Vec (S n) d :~: Vec k d)
something (_ :> V _) (_ :> V _) = (Refl, Refl)
{-
something as@(a :> as'@(_ :> _)) bs@(b :> bs'@(_ :> _)) = (p1', undefined)
    where (p1, p2) = something as' bs'
          p1' = apply Refl p1
-}

something' :: ((S m) <~> (S n) ~ (S k)) => SPNat (S m) -> SPNat (S n) -> SPNat (S k) ->
    (SPNat m :~: SPNat k, SPNat n :~: SPNat k)
something' (SS SI) (SS SI) (SS SI) = (Refl, Refl)
something' (SS m@(SS _)) (SS n@(SS _)) (SS k@(SS _)) = (p1', undefined)
    where (p1, p2) = something' m n k
          p1' = undefined
