{-# OPTIONS_GHC -W #-}
{-# LANGUAGE GADTs, DataKinds, KindSignatures, StandaloneDeriving, TypeFamilies, TypeOperators, ScopedTypeVariables, TypeApplications, AllowAmbiguousTypes, TemplateHaskell, QuasiQuotes, PolyKinds, FlexibleContexts, RankNTypes #-}

data PNat :: * where
    I :: PNat
    S :: PNat -> PNat deriving Show

data SPNat (n::PNat) where
    SI :: SPNat I
    SS :: SPNat n -> SPNat (S n)

deriving instance Show (SPNat n)

data Dim = DNil PNat | DCons PNat Dim deriving Show

data SDim :: Dim -> * where
    SDNil  :: SPNat n -> SDim (DNil n)
    SDCons :: SPNat n -> SDim d -> SDim (DCons n d)

data Tensor :: Dim -> * -> * where
    L    :: a -> Tensor (DNil I) a
    (:|) :: Tensor d a -> Tensor (DCons n d) a -> Tensor (DCons (S n) d) a
    H    :: Tensor d a -> Tensor (DCons I d) a

type family Max (m :: PNat) (n :: PNat) :: PNat where
    Max I n = n
    Max n I = n
    Max (S m) (S n) = S (Max m n)

type family DimAppend (d1 :: Dim) (d2 :: Dim) :: Dim where
    DimAppend (DNil n) d = DCons n d
    DimAppend (DCons n d1) d = DCons n (DimAppend d1 d)

instance Functor (Tensor d) where
    fmap f (L x) = L (f x)
    fmap f (H t) = H (fmap f t)
    fmap f (t :| ts) = (fmap f t) :| (fmap f ts)

{-
mul :: Num a => Tensor (DCons m (DNil n)) a -> Tensor (DCons n (DNil k)) a -> Tensor (DCons m (DNil k)) a
-- 1xn * 1x1 -> 1xn
mul (H v) (H (L x)) = H ((x *) <$> v)
-- mxn * nxk -> mxk
mul m (c :| cs) = undefined
    where c'' = mul m _
-}

gmul :: Num a => Tensor (DimAppend d (DCons m (DNil n))) a -> Tensor (DimAppend d (DCons n (DNil k))) a -> Tensor (DimAppend d (DCons m (DNil k))) a
gmul = undefined

{-
data Which = WLeft | WRight | WBoth

type family Expand (d1 :: Dim) (d2 :: Dim) :: (Which, Dim) where
    Expand (DNil m) (DNil n) = (WBoth, DNil (Max m n))

needs UndecidableInstances, meh
type family Rev (d :: Dim) (a :: Dim) :: Dim where
    Rev (DNil n) a = DCons n a
    Rev (DCons n d) a = Rev d (DCons n a)
-}

{-
type family DMax (d1 :: Dim) (d2 :: Dim) :: Dim where
    DMax (DNil m) (DNil n) = DNil (Max m n)
    DMax (DCons m d1) (DCons n d2) = DCons (Max m n) (DMax d1 d2)

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

-- NB: more like bzipWith
bmap :: m <~> n ~ True => (a -> b -> c) -> Vec m a -> Vec n b -> Vec (m <~~> n) c
bmap f as bs = (\(a, b) -> f a b) <$> broadcast as bs

intToNat :: Int -> PNat
intToNat 1 = I
intToNat n = S (intToNat (n - 1))

data Ex (p :: k -> *) where
    Ex :: p i -> Ex p

data (p :: k -> *) :*: (q :: k -> *) :: k -> * where
    (:&:) :: p k -> q k -> (p :*: q) k

newtype Flip f a b = Flip {unFlip :: f b a}

type WLenVec a = Ex (SPNat :*: Flip Vec a)

wrapLenVec :: [a] -> WLenVec a
wrapLenVec [] = undefined
wrapLenVec [x] = Ex (SI :&: Flip (V x))
wrapLenVec (x : xs) = case wrapLenVec xs of
    Ex (n :&: Flip v) -> Ex (SS n :&: Flip (x :> v))

type WVec a = Ex (Flip Vec a)

wrapVec :: [a] -> WVec a
wrapVec [] = undefined
wrapVec [x]      = Ex (Flip (V x))
wrapVec (x:xs)  = case wrapVec xs of
  Ex (Flip v) -> Ex (Flip (x :> v))

vlength' :: Vec n a -> Integer
vlength' (V _) = 1
vlength' (_ :> v) = 1 + vlength' v

vlength :: Vec n a -> SPNat n
vlength (V _) = SI
vlength (_ :> v) = SS (vlength v)

type WPNat = Ex SPNat
-}
