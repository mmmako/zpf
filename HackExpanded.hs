{-# OPTIONS_GHC -W #-}
{-# LANGUAGE GADTs, DataKinds, KindSignatures, StandaloneDeriving, TypeFamilies, TypeOperators, ScopedTypeVariables, TypeApplications, AllowAmbiguousTypes, TemplateHaskell, QuasiQuotes, PolyKinds, FlexibleContexts, RankNTypes #-}
{-# LANGUAGE UndecidableInstances #-}

import TensorQuasi

-- import Data.Type.Equality

type Matrix m n a = Tensor (DCons m (DCons n DNil)) a

type family Max (m :: PNat) (n :: PNat) :: PNat where
    Max I n = n
    Max n I = n
    Max (S m) (S n) = S (Max m n)

type family DimAppend (d1 :: Dim) (d2 :: Dim) :: Dim where
    DimAppend DNil d = d -- TODO make sure it's not DCons I d
    DimAppend (DCons n d1) d = DCons n (DimAppend d1 d)

type family (d1 :: Dim) <~> (d2 :: Dim) :: Dim where
    DNil <~> DNil = DNil
    DCons m d1 <~> DCons n d2 = DCons (Max m n) (d1 <~> d2)

type family CanBroadcast (d1 :: Dim) (d2 :: Dim) :: Bool where
    CanBroadcast DNil DNil = True
    CanBroadcast (DCons I d1) (DCons n d2) = CanBroadcast d1 d2
    CanBroadcast (DCons n d1) (DCons I d2) = CanBroadcast d1 d2
    CanBroadcast (DCons n d1) (DCons n d2) = CanBroadcast d1 d2
    CanBroadcast _ _ = False

{-
type family SameDepth (d1 :: Dim) (d2 :: Dim) :: Bool where
    SameDepth DNil DNil = True
    SameDepth (DCons _ d1) (DCons _ d2) = SameDepth d1 d2
    SameDepth _ _ = False
-}

data Longer = LeftBy PNat | RightBy PNat | Equal

data SLonger (l :: Longer) where
    SEqual :: SLonger Equal
    SLeftBy :: SPNat n -> SLonger (LeftBy n)
    SRightBy :: SPNat n -> SLonger (RightBy n)

deriving instance Show (SLonger l)

type family LongerS (l :: Longer) :: Longer where
    LongerS Equal = Equal
    LongerS (LeftBy n) = LeftBy (S n)
    LongerS (RightBy n) = RightBy (S n)

-- sadly this requires UndecidableInstances
type family DepthDiff (d1 :: Dim) (d2 :: Dim) :: Longer where
    DepthDiff DNil DNil = Equal
    DepthDiff (DCons _ d1) (DCons _ d2) = DepthDiff d1 d2
    DepthDiff (DCons _ DNil) DNil = LeftBy I
    DepthDiff DNil (DCons _ DNil) = RightBy I
    DepthDiff (DCons _ d) DNil = LongerS (DepthDiff d DNil)
    DepthDiff DNil (DCons _ d) = LongerS (DepthDiff DNil d)

type family Reverse (d :: Dim) (a :: Dim) :: Dim where
    Reverse DNil a = a
    Reverse (DCons n d) a = Reverse d (DCons n a)

type family RPad (d :: Dim) (n :: PNat) :: Dim where
    RPad d I = DCons I d
    RPad d (S n) = DCons I (RPad d n)

type family ElongateInternalLeft (d1 :: Dim) (d2 :: Dim) (diff :: Longer) :: Dim where
    ElongateInternalLeft d1 d2 Equal = d1
    ElongateInternalLeft d1 d2 (RightBy n) = RPad d1 n
    ElongateInternalLeft d1 d2 (LeftBy n) = d1
type family ElongateInternalRight (d1 :: Dim) (d2 :: Dim) (diff :: Longer) :: Dim where
    ElongateInternalRight d1 d2 Equal = d2
    ElongateInternalRight d1 d2 (RightBy n) = d2
    ElongateInternalRight d1 d2 (LeftBy n) = RPad d2 n

type family ElongateLeft (d1 :: Dim) (d2 :: Dim) :: Dim where
    ElongateLeft d1 d2 = ElongateInternalLeft d1 d2 (DepthDiff d1 d2)
type family ElongateRight (d1 :: Dim) (d2 :: Dim) :: Dim where
    ElongateRight d1 d2 = ElongateInternalRight d1 d2 (DepthDiff d1 d2)

longerS :: SLonger l -> SLonger (LongerS l)
longerS SEqual = SEqual
longerS (SLeftBy n) = SLeftBy (SS n)
longerS (SRightBy n) = SRightBy (SS n)

-- mmmmm this is a nice function
-- wait, but shouldn't it be on SDim? meh
depthDiff :: Tensor d1 a -> Tensor d2 a -> SLonger (DepthDiff d1 d2)
-- DepthDiff DNil DNil = Equal
depthDiff (L _) (L _) = SEqual
-- DepthDiff (DCons _ DNil) DNil = LeftBy I
depthDiff (H (L _)) (L _) = SLeftBy SI
depthDiff ((L _) :- _) (L _) = SLeftBy SI
-- DepthDiff DNil (DCons _ DNil) = RightBy I
depthDiff (L _) (H (L _)) = SRightBy SI
depthDiff (L _) ((L _) :- _) = SRightBy SI
-- DepthDiff (DCons _ d) DNil = LongerS (DepthDiff d DNil)
depthDiff (H a@(H _)) (L b) = longerS (depthDiff a (L b))
depthDiff (H a@(_ :- _)) (L b) = longerS (depthDiff a (L b))
depthDiff (a@(H _) :- _) (L b) = longerS (depthDiff a (L b))
depthDiff (a@(_ :- _) :- _) (L b) = longerS (depthDiff a (L b))
-- DepthDiff DNil (DCons _ d) = LongerS (DepthDiff d DNil)
depthDiff (L a) (H b@(H _)) = longerS (depthDiff (L a) b)
depthDiff (L a) (H b@(_ :- _)) = longerS (depthDiff (L a) b)
depthDiff (L a) (b@(H _) :- _) = longerS (depthDiff (L a) b)
depthDiff (L a) (b@(_ :- _) :- _) = longerS (depthDiff (L a) b)
-- DepthDiff (DCons _ d1) (DCons _ d2) = DepthDiff d1 d2
depthDiff (H a) (H b) = depthDiff a b
depthDiff (a :- _) (H b) = depthDiff a b
depthDiff (H a) (b :- _) = depthDiff a b
depthDiff (a :- _) (b :- _) = depthDiff a b

rpad :: Tensor d a -> SPNat n -> Tensor (RPad d n) a
rpad t SI = H t
rpad t (SS n) = H (rpad t n)

elongateInternal :: Tensor d1 a -> Tensor d2 b -> SLonger l -> (Tensor (ElongateInternalLeft d1 d2 l) a, Tensor (ElongateInternalRight d1 d2 l) b)
elongateInternal t1 t2 SEqual = (t1, t2)
elongateInternal t1 t2 (SRightBy n) = (rpad t1 n, t2)
elongateInternal t1 t2 (SLeftBy n) = (t1, rpad t2 n)

-- TODO why `a` in both places????????
elongate :: Tensor d1 a -> Tensor d2 a -> (Tensor (ElongateLeft d1 d2) a, Tensor (ElongateRight d1 d2) a)
elongate t1 t2 = elongateInternal t1 t2 (depthDiff t1 t2)

proof :: Tensor d1 a -> Tensor d2 b -> (DepthDiff (ElongateLeft d1 d2) (ElongateRight d1 d2) ~ Equal => t) -> t
proof (L _) (L _) t = t
proof (H (L _)) (L a) t = proof m (L a) t

{-
proof1 :: Tensor d1 a -> Tensor d2 b -> (DepthDiff (ElontageL
-}

-- TODO why (a, a) again?
strongerUnsafeBroadcast :: Tensor d1 a -> Tensor d2 a -> Tensor (ElongateLeft d1 d2 <~> ElongateRight d1 d2) (a, a)
strongerUnsafeBroadcast t1 t2 = proof t1 t2 $ unsafeBroadcast t1' t2'
-- strongerUnsafeBroadcast t1 t2 = unsafeBroadcast t1' t2'
    where (t1', t2') = elongate t1 t2

strongerUnsafestBroadcast :: CanBroadcast (ElongateLeft d1 d2) (ElongateRight d1 d2) ~ True => Tensor d1 a -> Tensor d2 a -> Tensor (ElongateLeft d1 d2 <~> ElongateRight d1 d2) (a, a)
strongerUnsafestBroadcast t1 t2 = unsafestBroadcast t1' t2'
    where (t1', t2') = elongate t1 t2

instance Functor (Tensor d) where
    fmap f (L x) = L (f x)
    fmap f (H t) = H (fmap f t)
    fmap f (t :- ts) = (fmap f t) :- (fmap f ts)

mul :: Num a => Matrix m n a -> Matrix n k a -> Matrix m k a
-- 1x1 * 1x1 -> 1x1
mul (H (H (L x))) m = (x *) <$> m
-- 1x(n+1) * (n+1)x1 -> 1x1
mul (H ((L x) :- xs)) ((H (L y)) :- ys) = H (H (L (x*y + z)))
    where H (H (L z)) = mul (H xs) ys
-- 1xn * nxk -> 1xk
mul v@(H _) t@((_ :- _) :- _) = H ((L x) :- t'')
    where (H (H (L x))) = mul v r
          (r, t') = tear t
          H t'' = mul v t'
-- (m+1)xn * nxk -> (m+1)xk
mul (r :- rs) m = r' :- rs'
    where H r' = mul (H r) m -- TODO does this go through pattern match checks?
          rs' = mul rs m

tear :: Matrix m (S n) a -> (Matrix m I a, Matrix m n a)
tear (H ((L a) :- as)) = (H (H (L a)), H as)
tear ((a :- r) :- rs) = ((H a) :- as, r :- rs')
    where (as, rs') = tear rs

unsafeBroadcast :: DepthDiff d1 d2 ~ Equal => Tensor d1 a -> Tensor d2 b -> Tensor (d1 <~> d2) (a, b)
unsafeBroadcast (L a) (L b) = L (a, b)
unsafeBroadcast (H as) (H bs) = H (unsafeBroadcast as bs)
unsafeBroadcast (a :- as) (b :- bs) = ((unsafeBroadcast a b) :- (unsafeBroadcast as bs))
unsafeBroadcast (a :- as) (H bs) = (unsafeBroadcast a bs) :- (unsafeBroadcast as (H bs))
unsafeBroadcast (H as) (b :- bs) = (unsafeBroadcast as b) :- (unsafeBroadcast (H as) bs)

unsafestBroadcast :: Tensor d1 a -> Tensor d2 b -> Tensor (d1 <~> d2) (a, b)
unsafestBroadcast (L a) (L b) = L (a, b)
unsafestBroadcast (H as) (H bs) = H (unsafestBroadcast as bs)
unsafestBroadcast (a :- as) (b :- bs) = ((unsafestBroadcast a b) :- (unsafestBroadcast as bs))
unsafestBroadcast (a :- as) (H bs) = (unsafestBroadcast a bs) :- (unsafestBroadcast as (H bs))
unsafestBroadcast (H as) (b :- bs) = (unsafestBroadcast as b) :- (unsafestBroadcast (H as) bs)

-- TODO shouldn't CanBroadcast imply SameDepth?
weakBroadcast :: (DepthDiff d1 d2 ~ Equal, CanBroadcast d1 d2 ~ True) => Tensor d1 a -> Tensor d2 b -> Tensor (d1 <~> d2) (a, b)
weakBroadcast = unsafeBroadcast

infixl 6 |+|
a |+| b = uncurry (+) <$> weakBroadcast a b

infixl 7 |*|
a |*| b = uncurry (*) <$> weakBroadcast a b

data Ex (p :: k -> *) where
    Ex :: p i -> Ex p

data (p :: k -> *) :*: (q :: k -> *) :: k -> * where
    (:&:) :: p k -> q k -> (p :*: q) k

data (p :: iota -> *) :**: (q :: kappa -> *) :: (iota, kappa) -> * where
    (:&&:) :: p iota -> q kappa -> (p :**: q) '(iota, kappa)

type Size = SPNat :**: SPNat

data Ex2 (p :: k -> i -> *) where
    Ex2 :: p j l -> Ex2 p

newtype Matrix1 a m n = Matrix1 (Tensor (DCons m (DCons n DNil)) a)

main = do
    str <- getContents
    let ll = map (map (read :: String -> Integer) . words) $ lines str
        m = (\(Just x) -> x) $ fromLL ll
        m' = mapEx2 m
    putStrLn $ showEx (Just m')

qwe str = let ll = map (map (read :: String -> Integer) . words) $ lines str in ll

showEx :: Maybe (Ex2 (Matrix1 Integer)) -> String
showEx (Just (Ex2 (Matrix1 m))) = show m
showEx Nothing = "Nothing"

mapEx2 :: Ex2 (Matrix1 Integer) -> Ex2 (Matrix1 Integer)
mapEx2 (Ex2 (Matrix1 m)) = Ex2 (Matrix1 (fmap (2*) m))

fromLL :: [[Integer]] -> Maybe (Ex2 (Matrix1 Integer))
fromLL [l] = case fromL l of
    Ex (Matrix1 m) -> Just (Ex2 (Matrix1 m))
fromLL (l:ls) = case fromLL ls of
    Nothing -> Nothing
    Just m -> addLine (fromL l) m

fromL :: [Integer] -> Ex (Matrix1 Integer I)
fromL [x] = Ex (Matrix1 (H (H (L x))))
fromL (x:xs) = case fromL xs of
    Ex (Matrix1 (H v)) -> Ex (Matrix1 (H (L x :- v)))

addLine :: Ex (Matrix1 Integer I) -> Ex2 (Matrix1 Integer) -> Maybe (Ex2 (Matrix1 Integer))
addLine (Ex (Matrix1 m@(H _))) (Ex2 (Matrix1 m'@(H _))) =
    case sameLength m m' of
        Nothing -> Nothing
        Just (H m'') -> Just (Ex2 (Matrix1 (m'' :- m')))
addLine (Ex (Matrix1 m@(H _))) (Ex2 (Matrix1 m''@(m' :- ms))) =
    case sameLength m (H m') of
        Nothing -> Nothing
        Just (H m''') -> Just (Ex2 (Matrix1 (m''' :- m'')))

sameLength :: Matrix I n a -> Matrix I m b -> Maybe (Matrix I m a)
sameLength (H (H (L a))) (H (H (L _))) = Just $ H (H (L a))
sameLength (H (H (L _))) (H (_ :- _)) = Nothing
sameLength (H (_ :- _)) (H (H (L _))) = Nothing
sameLength (H (a :- v)) (H (_ :- v')) =
    case sameLength (H v) (H v') of
        Nothing -> Nothing
        Just (H v'') -> Just (H (a :- v''))

-- testSumA :: Num a => Matrix m n a -> Matrix I n a
testSumA :: Num a => Tensor (DCons m d) a -> Tensor (DCons I d) a
testSumA = undefined
testDivA m = (uncurry (/)) <$> weakBroadcast m (testSumA m)

-- testSumA' :: Num a => Matrix m n a -> Tensor (DCons n DNil) a
testSumA' :: Num a => Tensor (DCons m d) a -> Tensor (DCons I d) a
testSumA' = undefined

testDivA' m = (uncurry (/)) <$> strongerUnsafestBroadcast m (testSumA' m)

testSumB :: Num a => Matrix m n a -> Matrix m I a
testSumB = undefined
testDivB m = (uncurry (/)) <$> weakBroadcast m (testSumB m)

testSumB' :: Num a => Matrix m n a -> Tensor (DCons m DNil) a
testSumB' = undefined
testDivB' m = (uncurry (/)) <$> strongerUnsafestBroadcast m (testSumB' m)

{-
infixr 6 :>
data Vec :: PNat -> * -> * where
    V    :: a -> Vec I a
    (:>) :: a -> Vec n a -> Vec (S n) a

deriving instance Show a => Show (Vec n a)

toVector :: [Integer] -> Ex (Flip Vec Integer)
toVector [x] = Ex $ Flip $ V x
toVector (x:xs) =
    case toVector xs of
        Ex (Flip xs') -> Ex (Flip (x :> xs'))

readImage :: String -> Maybe (Ex (Flip Tensor Integer))
readImage s = Just $ Ex $ Flip $ L 123
    where ll = map (map (read :: String -> Integer) . words) $ lines s
-}

{-
gmul m'@(H ((L _) :- _)) m@((H (L _)) :- _) = mul m' m
gmul v@(H _) t@((_ :- _) :- _) = mul v t
gmul m'@(r :- rs) m = mul m' m
-}

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
