{-# OPTIONS_GHC -W #-}
{-# LANGUAGE GADTs, DataKinds, KindSignatures, StandaloneDeriving, TypeFamilies, TypeOperators, ScopedTypeVariables, TypeApplications, AllowAmbiguousTypes, TemplateHaskell, QuasiQuotes, PolyKinds, FlexibleContexts, MultiParamTypeClasses, FlexibleInstances #-}
-- {-# LANGUAGE UndecidableInstances #-}

-- import Data.Type.Equality
-- import GHC.TypeLits
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

data Dir = Ld | Rd | Both

class Broadcast (m :: PNat) (n :: PNat) (d :: Dir) where
instance Broadcast I I Both where
instance Broadcast I (S n) Rd where
instance Broadcast (S n) I Ld where
instance Broadcast m n Both => Broadcast (S m) (S n) Both where

data Select :: PNat -> PNat -> * where
    L :: Broadcast m n Ld => Select m n
    R :: Broadcast m n Rd => Select m n
    B :: Broadcast m n Both => Select m n
    N :: Select m n

select :: SPNat m -> SPNat n -> Select m n
select SI SI = B
select SI (SS _) = R
select (SS _) SI = L
select (SS m) (SS n) =
    case (select m n) of
        N -> N
        L -> N
        R -> N
        B -> B
