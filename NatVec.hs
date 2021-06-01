{-# LANGUAGE GADTs, DataKinds, KindSignatures, StandaloneDeriving, TypeFamilies, TypeOperators, ScopedTypeVariables, TypeApplications, AllowAmbiguousTypes #-}

data Nat :: * where
  Z :: Nat
  S :: Nat -> Nat

-- Nat is a kind, and so is Nat -> * -> *
infixr 6 :>
data Vec :: Nat -> * -> * where
  V0   :: Vec 'Z a
  (:>) :: a -> Vec n a -> Vec ('S n) a

deriving instance (Show a) => Show (Vec n a)

vhead :: Vec (S n) a -> a
vhead (x:>_) = x

type family (n :: Nat) :+ (m :: Nat) :: Nat
type instance Z :+ m = m
type instance (S n) :+ m = S (n :+ m)

vapp :: Vec m a -> Vec n a -> Vec (m :+ n) a
vapp V0 ys = ys
vapp (x:>xs) ys = x:>(vapp xs ys)

-- SNat n ~~ Vec n ()
data SNat (n::Nat) where
  SZ :: SNat Z
  SS :: SNat n -> SNat (S n)
deriving instance Show(SNat n)

add :: (SNat m) -> (SNat n) -> SNat(m :+ n)
add SZ n = n
add (SS m) n = SS (add m n)
-- # Comparison
type family (m::Nat) :< (n::Nat) :: Bool
type instance m :< 'Z = 'False
type instance 'Z :< ('S n) = 'True
type instance ('S m) :< ('S n) = m :< n

-- nth
nth :: (m:<n) ~ 'True => SNat m -> Vec n a -> a
nth SZ (a:>_)  = a
nth (SS m') (_:>xs) = nth m' xs




-- | Nat Proxy
data NP :: Nat -> * where NP :: NP n

-- >>> let v = 1 :> (1 :> (1 :> V0)); two = SS(SS SZ) in vtake2 two NP v
-- 1 :> (1 :> V0)
vtake2 :: SNat m -> NP n -> Vec (m :+ n) a -> Vec m a
vtake2 SZ     _ _ = V0
vtake2 (SS m) n (x:>xs) = x :> vtake2 m n xs


vtake4 :: forall n m a. SNat m -> Vec (m :+ n) a -> Vec m a
vtake4 SZ _ = V0
vtake4 (SS m) (x:>xs) = x :> vtake4 @n m xs
