{-# OPTIONS_GHC -W #-}
{-# LANGUAGE GADTs, DataKinds, KindSignatures, StandaloneDeriving, TypeFamilies, TypeOperators, ScopedTypeVariables, TypeApplications, AllowAmbiguousTypes, TemplateHaskell, QuasiQuotes, PolyKinds, FlexibleContexts, RankNTypes, FlexibleInstances, UndecidableInstances #-}

module Arrays where

import ArrayQuasi

type Matrix m n a = Array (DCons m (DCons n DNil)) a

type family Max (m :: PNat) (n :: PNat) :: PNat where
    Max I n = n
    Max n I = n
    Max (S m) (S n) = S (Max m n)

type family DimAppend (d1 :: Dim) (d2 :: Dim) :: Dim where
    DimAppend DNil d = d
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

type family SameDepth (d1 :: Dim) (d2 :: Dim) :: Bool where
    SameDepth DNil DNil = True
    SameDepth (DCons _ d1) (DCons _ d2) = SameDepth d1 d2
    SameDepth _ _ = False

data Longer = LeftBy PNat | RightBy PNat | Equal

data SLonger (l :: Longer) where
    SEqual :: SLonger Equal
    SLeftBy :: SPNat n -> SLonger (LeftBy n)
    SRightBy :: SPNat n -> SLonger (RightBy n)

type family LongerS (l :: Longer) :: Longer where
    LongerS Equal = Equal
    LongerS (LeftBy n) = LeftBy (S n)
    LongerS (RightBy n) = RightBy (S n)

type family DepthDiff (d1 :: Dim) (d2 :: Dim) :: Longer where
    DepthDiff DNil DNil = Equal
    DepthDiff (DCons _ d1) (DCons _ d2) = DepthDiff d1 d2
    DepthDiff (DCons _ DNil) DNil = LeftBy I
    DepthDiff DNil (DCons _ DNil) = RightBy I
    DepthDiff (DCons _ d) DNil = LongerS (DepthDiff d DNil)
    DepthDiff DNil (DCons _ d) = LongerS (DepthDiff DNil d)

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
depthDiff :: Array d1 a -> Array d2 b -> SLonger (DepthDiff d1 d2)
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

rpad :: Array d a -> SPNat n -> Array (RPad d n) a
rpad a SI = H a
rpad a (SS n) = H (rpad a n)

elongateInternal :: Array d1 a -> Array d2 b -> SLonger l -> (Array (ElongateInternalLeft d1 d2 l) a, Array (ElongateInternalRight d1 d2 l) b)
elongateInternal a1 a2 SEqual = (a1, a2)
elongateInternal a1 a2 (SRightBy n) = (rpad a1 n, a2)
elongateInternal a1 a2 (SLeftBy n) = (a1, rpad a2 n)

elongate :: Array d1 a -> Array d2 b -> (Array (ElongateLeft d1 d2) a, Array (ElongateRight d1 d2) b)
elongate a1 a2 = elongateInternal a1 a2 (depthDiff a1 a2)

broadcast :: (SameDepth (ElongateLeft d1 d2) (ElongateRight d1 d2) ~ True, CanBroadcast (ElongateLeft d1 d2) (ElongateRight d1 d2) ~ True)
    => Array d1 a -> Array d2 b -> Array (ElongateLeft d1 d2 <~> ElongateRight d1 d2) (a, b)
broadcast a1 a2 = unsafeBroadcast a1' a2'
    where (a1', a2') = elongate a1 a2

instance Functor (Array d) where
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
mul v@(H _) t@((_ :- _) :- _) = H ((L x) :- a'')
    where (H (H (L x))) = mul v r
          (r, a') = tear t
          H a'' = mul v a'
-- (m+1)xn * nxk -> (m+1)xk
mul (r :- rs) m = r' :- rs'
    where H r' = mul (H r) m
          rs' = mul rs m

tear :: Matrix m (S n) a -> (Matrix m I a, Matrix m n a)
tear (H ((L a) :- as)) = (H (H (L a)), H as)
tear ((a :- r) :- rs) = ((H a) :- as, r :- rs')
    where (as, rs') = tear rs

unsafeBroadcast :: SameDepth d1 d2 ~ True => Array d1 a -> Array d2 b -> Array (d1 <~> d2) (a, b)
unsafeBroadcast (L a) (L b) = L (a, b)
unsafeBroadcast (H as) (H bs) = H (unsafeBroadcast as bs)
unsafeBroadcast (a :- as) (b :- bs) = ((unsafeBroadcast a b) :- (unsafeBroadcast as bs))
unsafeBroadcast (a :- as) (H bs) = (unsafeBroadcast a bs) :- (unsafeBroadcast as (H bs))
unsafeBroadcast (H as) (b :- bs) = (unsafeBroadcast as b) :- (unsafeBroadcast (H as) bs)

-- TODO shouldn't CanBroadcast imply SameDepth?
weakBroadcast :: (SameDepth d1 d2 ~ True, CanBroadcast d1 d2 ~ True) => Array d1 a -> Array d2 b -> Array (d1 <~> d2) (a, b)
weakBroadcast = unsafeBroadcast

data Ex (p :: k -> *) where
    Ex :: p i -> Ex p
data Ex2 (p :: k -> i -> *) where
    Ex2 :: p j l -> Ex2 p

newtype Matrix1 a m n = Matrix1 (Array (DCons m (DCons n DNil)) a)
newtype Vec1 a n = Vec1 (Array (DCons n DNil) a)

type family ToList (d :: Dim) (a :: *) :: * where
    ToList DNil a = a
    ToList (DCons n d) a = [ToList d a]

fromLL :: [[a]] -> Maybe (Ex2 (Matrix1 a))
fromLL [] = Nothing
fromLL [l] = (\(Ex (Matrix1 m)) -> Ex2 (Matrix1 m)) <$> fromL l
fromLL (l:ls) = do
    ls' <- fromLL ls
    l' <- fromL l
    addLine l' ls'

toLL' :: Array d a -> ToList d a
toLL' (L a) = a
toLL' (H as) = [toLL' as]
toLL' (a :- as) = toLL' a:toLL' as

toL :: Array (DCons n DNil) a -> [a]
toL (H (L a)) = [a]
toL ((L a) :- as) = a:toL as

fromL :: [a] -> Maybe (Ex (Matrix1 a I))
fromL [] = Nothing
fromL [x] = Just $ Ex (Matrix1 (H (H (L x))))
fromL (x:xs) = case fromL xs of
    Nothing -> Nothing
    Just (Ex (Matrix1 (H v))) -> Just (Ex (Matrix1 (H (L x :- v))))

addLine :: Ex (Matrix1 a I) -> Ex2 (Matrix1 a) -> Maybe (Ex2 (Matrix1 a))
addLine (Ex (Matrix1 m@(H _))) (Ex2 (Matrix1 m'@(H _))) =
    (\(H m'') -> Ex2 (Matrix1 (m'' :- m'))) <$> sameLength m m'
addLine (Ex (Matrix1 m@(H _))) (Ex2 (Matrix1 m''@(m' :- _))) =
    (\(H m''') -> Ex2 (Matrix1 (m''' :- m''))) <$> sameLength m (H m')

sameLength :: Matrix I n a -> Matrix I m b -> Maybe (Matrix I m a)
sameLength (H (H (L a))) (H (H (L _))) = Just $ H (H (L a))
sameLength (H (H (L _))) (H (_ :- _)) = Nothing
sameLength (H (_ :- _)) (H (H (L _))) = Nothing
sameLength (H (a :- v)) (H (_ :- v')) = (\(H v'') -> H (a :- v'')) <$> sameLength (H v) (H v')

maxNN :: Array (DCons n d) a -> (Max n n ~ n => t) -> t
maxNN (H _) a = a
maxNN (_ :- as) a = maxNN as a

unsplit :: Array d (Array d' a) -> Array (DimAppend d d') a
unsplit (L a) = a
unsplit (H a) = H (unsplit a)
unsplit (a :- a') = unsplit a :- unsplit a'

split :: SDim d -> Array (DimAppend d d') a -> Array d (Array d' a)
split SDNil a = L a
split (SDCons _ d) (H a) = H (split d a)
split (SDCons (SS n) d) (a :- as) = (split d a) :- (split (SDCons n d) as)

splitOne :: Array (DCons n d) a -> Array (DCons n DNil) (Array d a)
splitOne (H a) = H (L a)
splitOne (a :- as) = L a :- splitOne as

toSDim :: Array d a -> SDim d
toSDim (L _) = SDNil
toSDim (H a) = SDCons SI (toSDim a)
toSDim (_ :- as) = case toSDim as of
    SDCons n d -> SDCons (SS n) d

range :: Num a => SPNat n -> Array (DCons n DNil) a
range n = f n 0
    where f :: Num a => SPNat n -> a -> Array (DCons n DNil) a
          f SI x = H (L x)
          f (SS n) x = L x :- f n (x + 1)

infixl 6 |+|
infixl 6 |-|
infixl 7 |*|
infixl 7 |/|
a |+| b = uncurry (+) <$> broadcast a b
a |-| b = uncurry (-) <$> broadcast a b
a |*| b = uncurry (*) <$> broadcast a b
a |/| b = uncurry (/) <$> broadcast a b
