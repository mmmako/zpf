{-# OPTIONS_GHC -W #-}
{-# LANGUAGE GADTs, DataKinds, KindSignatures, StandaloneDeriving, TypeFamilies, TypeOperators, ScopedTypeVariables, TypeApplications, AllowAmbiguousTypes, TemplateHaskell, QuasiQuotes, PolyKinds, FlexibleContexts, RankNTypes, FlexibleInstances #-}
{-# LANGUAGE UndecidableInstances #-}

module HackExpanded where

import TensorQuasi
import System.Environment

-- import Data.Type.Equality

type Matrix m n a = Tensor (DCons m (DCons n DNil)) a

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
depthDiff :: Tensor d1 a -> Tensor d2 b -> SLonger (DepthDiff d1 d2)
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

elongate :: Tensor d1 a -> Tensor d2 b -> (Tensor (ElongateLeft d1 d2) a, Tensor (ElongateRight d1 d2) b)
elongate t1 t2 = elongateInternal t1 t2 (depthDiff t1 t2)

{-
proof :: Tensor d1 a -> Tensor d2 b -> (DepthDiff (ElongateLeft d1 d2) (ElongateRight d1 d2) ~ Equal => t) -> t
proof (L _) (L _) t = t
proof (H (L _)) (L a) t = proof m (L a) t

proof1 :: Tensor d1 a -> Tensor d2 b -> (DepthDiff (ElontageL
-}

broadcast :: (SameDepth (ElongateLeft d1 d2) (ElongateRight d1 d2) ~ True, CanBroadcast (ElongateLeft d1 d2) (ElongateRight d1 d2) ~ True)
    => Tensor d1 a -> Tensor d2 b -> Tensor (ElongateLeft d1 d2 <~> ElongateRight d1 d2) (a, b)
broadcast t1 t2 = unsafeBroadcast t1' t2'
    where (t1', t2') = elongate t1 t2

{-
strongerUnsafestBroadcast :: CanBroadcast (ElongateLeft d1 d2) (ElongateRight d1 d2) ~ True => Tensor d1 a -> Tensor d2 a -> Tensor (ElongateLeft d1 d2 <~> ElongateRight d1 d2) (a, a)
strongerUnsafestBroadcast t1 t2 = unsafestBroadcast t1' t2'
    where (t1', t2') = elongate t1 t2
-}

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

unsafeBroadcast :: SameDepth d1 d2 ~ True => Tensor d1 a -> Tensor d2 b -> Tensor (d1 <~> d2) (a, b)
unsafeBroadcast (L a) (L b) = L (a, b)
unsafeBroadcast (H as) (H bs) = H (unsafeBroadcast as bs)
unsafeBroadcast (a :- as) (b :- bs) = ((unsafeBroadcast a b) :- (unsafeBroadcast as bs))
unsafeBroadcast (a :- as) (H bs) = (unsafeBroadcast a bs) :- (unsafeBroadcast as (H bs))
unsafeBroadcast (H as) (b :- bs) = (unsafeBroadcast as b) :- (unsafeBroadcast (H as) bs)

{-
unsafestBroadcast :: Tensor d1 a -> Tensor d2 b -> Tensor (d1 <~> d2) (a, b)
unsafestBroadcast (L a) (L b) = L (a, b)
unsafestBroadcast (H as) (H bs) = H (unsafestBroadcast as bs)
unsafestBroadcast (a :- as) (b :- bs) = ((unsafestBroadcast a b) :- (unsafestBroadcast as bs))
unsafestBroadcast (a :- as) (H bs) = (unsafestBroadcast a bs) :- (unsafestBroadcast as (H bs))
unsafestBroadcast (H as) (b :- bs) = (unsafestBroadcast as b) :- (unsafestBroadcast (H as) bs)
-}

-- TODO shouldn't CanBroadcast imply SameDepth?
weakBroadcast :: (SameDepth d1 d2 ~ True, CanBroadcast d1 d2 ~ True) => Tensor d1 a -> Tensor d2 b -> Tensor (d1 <~> d2) (a, b)
weakBroadcast = unsafeBroadcast

{-
infixl 6 |+|
a |+| b = uncurry (+) <$> weakBroadcast a b

infixl 7 |*|
a |*| b = uncurry (*) <$> weakBroadcast a b
-}

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
newtype Vec1 a n = Vec1 (Tensor (DCons n DNil) a)

{-
main = do
    [cnt] <- getArgs
    let cnt' = read cnt
    putStrLn $ mapEx (makeLong' cnt')
    {-
    putStrLn $ mapEx $ makeLong' n'
    let ll = [[i..i+2] | i <- [0,3..100]]
        long = fromLL ll
        small = [m|[[1 2 3] [3 4 5] [5 6 7]]|]
    putStrLn $ showEx long
    str <- getContents
    let ll = map (map (read :: String -> Integer) . words) $ lines str
        m = (\(Just x) -> x) $ fromLL ll
        m' = mapEx2 m
    putStrLn $ showEx (Just m')
    -}
-}

qwe str = let ll = map (map (read :: String -> Integer) . words) $ lines str in ll

showEx :: Maybe (Ex2 (Matrix1 Integer)) -> String
showEx (Just (Ex2 (Matrix1 m))) = show m
showEx Nothing = "Nothing"

{-
makeLong :: Integer -> Ex (Vec1 (Tensor (DCons (S (S I)) DNil) Integer))
makeLong n = Ex2 (Matrix1 (f <$> m))
    where -- v = [m|[1 2 3]|]
          l = [(i, i+1, i+2) | i <- [0,3..3*n]]
          f (x, y, z) = L (L x :- L y :- H (L z))
          Just (Ex2 (Matrix1 m)) = fromL l
-}

makeLong' :: Integer -> Ex2 (Matrix1 (Tensor (DCons (S (S I)) DNil) Integer))
makeLong' n = case fromLL l of
          Just (Ex2 (Matrix1 m)) -> Ex2 (Matrix1 (f <$> m))
    where l = [[(i, i+1, i+2) | i <- [3*j,3*j+3..3*j+n]] | j <- [0,3*n..3*n*n]]
          f (x, y, z) = L x :- L y :- H (L z)

-- mapEx :: Ex2 (Matrix1 (Tensor (DCons (S (S I)) DNil) Integer)) -> String -- Ex2 (Matrix1 (Tensor (DCons (S (S I)) DNil) Integer))
mapEx :: Ex2 (Matrix1 (Tensor (DCons (S (S I)) DNil) Integer)) -> String
mapEx (Ex2 (Matrix1 v)) = show m'''
    where m' = unsplit v
          -- small = [m|[[1 2 3] [3 4 5] [5 6 7]]|]
          small = [m|[[1 2 3 3] [3 4 5 5] [5 6 7 7]]|]
          m'' = splitOne m'
          m''' = unsplit $ (\x -> mul x small) <$> m''

mapEx2 :: Ex2 (Matrix1 Integer) -> Ex2 (Matrix1 Integer)
mapEx2 (Ex2 (Matrix1 m)) = Ex2 (Matrix1 (fmap (2*) m))

-- TODO use Maybe monad
fromLL :: [[a]] -> Maybe (Ex2 (Matrix1 a))
fromLL [] = Nothing
fromLL [l] = case fromL l of
    Just (Ex (Matrix1 m)) -> Just (Ex2 (Matrix1 m))
    Nothing -> Nothing
fromLL (l:ls) = case fromLL ls of
    Nothing -> Nothing
    Just m -> case fromL l of
        Just l -> addLine l m
        Nothing -> Nothing

type family ToList (d :: Dim) (a :: *) :: * where
    ToList DNil a = a
    ToList (DCons n d) a = [ToList d a]

toLL' :: Tensor d a -> ToList d a
toLL' (L a) = a
toLL' (H as) = [toLL' as]
toLL' (a :- as) = toLL' a:toLL' as

toL :: Tensor (DCons n DNil) a -> [a]
toL (H (L a)) = [a]
toL ((L a) :- as) = a:toL as

toLL :: Matrix m n a -> [[a]]
toLL (H as) = [toL as]
toLL (a :- as) = toL a:toLL as

fromL :: [a] -> Maybe (Ex (Matrix1 a I))
fromL [] = Nothing
fromL [x] = Just $ Ex (Matrix1 (H (H (L x))))
fromL (x:xs) = case fromL xs of
    Nothing -> Nothing
    Just (Ex (Matrix1 (H v))) -> Just (Ex (Matrix1 (H (L x :- v))))

{-
fromL' :: [(Integer, Integer, Integer)] -> Maybe (Ex (Vec1 (Tensor (DCons (S (S I)) DNil) Integer)))
fromL' [] = Nothing
fromL' [(x, y, z)] = Just $ Ex (Vec1 (H (L (L x :- L y :- H (L z)))))
fromL' ((x, y, z):xs) = case fromL' xs of
    Nothing -> Nothing
    Just (Ex (Vec1 v)) -> Just (Ex (Vec1 (L (L x :- L y :- H (L z)) :- v)))
-}

addLine :: Ex (Matrix1 a I) -> Ex2 (Matrix1 a) -> Maybe (Ex2 (Matrix1 a))
addLine (Ex (Matrix1 m@(H _))) (Ex2 (Matrix1 m'@(H _))) =
    case sameLength m m' of
        Nothing -> Nothing
        Just (H m'') -> Just (Ex2 (Matrix1 (m'' :- m')))
addLine (Ex (Matrix1 m@(H _))) (Ex2 (Matrix1 m''@(m' :- _))) =
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
testSumA' (H m) = H m
testSumA' (m :- ms) = (uncurry (+)) <$> mp
    where m' = testSumA' (H m)
          ms' = testSumA' ms
          mp = asd m' ms'

asd :: Tensor d a -> Tensor d a -> Tensor d (a, a)
asd t1 t2 = brDD t1 $ depthDD t1 $ unsafeBroadcast t1 t2

maxNN :: Tensor (DCons n d) a -> (Max n n ~ n => t) -> t
maxNN (H _) t = t
maxNN (_ :- as) t = maxNN as t

maxNN' :: Tensor (DCons m (DCons n d)) a -> (Max n n ~ n => t) -> t
maxNN' (H (H _)) t = t
maxNN' (H (_ :- as)) t = maxNN' (H as) t
maxNN' ((H _) :- _) t = t
maxNN' ((_ :- as) :- _) t = maxNN' (H as) t

depthDD :: Tensor d a -> (SameDepth d d ~ True => t) -> t
depthDD (L _) t = t
depthDD (H m) t = depthDD m t
depthDD (m :- _) t = depthDD m t

brDD :: Tensor d a -> (d <~> d ~ d => t) -> t 
brDD (L _) t = t
brDD (H m) t = brDD m t
brDD (_ :- ms) t = brDD ms t

-- testDivA' :: Fractional a => Matrix m n a -> Matrix m (Max n n) a
testDivA' :: Fractional a => Matrix m n a -> Matrix m n a
testDivA' m = maxNN' m ((uncurry (/)) <$> broadcast m (testSumA' m))

testSumB :: Num a => Matrix m n a -> Matrix m I a
testSumB = undefined
testDivB m = (uncurry (/)) <$> weakBroadcast m (testSumB m)

testSumB' :: Num a => Matrix m n a -> Tensor (DCons m DNil) a
testSumB' = undefined
-- testDivB' m = (uncurry (/)) <$> strongerUnsafestBroadcast m (testSumB' m)

unsplit :: Tensor d (Tensor d' a) -> Tensor (DimAppend d d') a
unsplit (L t) = t
unsplit (H t) = H (unsplit t)
unsplit (t :- t') = unsplit t :- unsplit t'

{-
diffApp :: DepthDiff (DimAppend d d') d' ~ Equal => Tensor d' a -> Tensor (DimAppend d d') a -> (d ~ DNil => t) -> t
diffApp = undefined

split :: forall d d' a. Tensor d' a -> Tensor (DimAppend d d') a -> Tensor d (Tensor d' a)
split small big = case depthDiff big small of
    SEqual -> diffApp @d small big $ L small
-}

-- TODO this is nice and easy, but it works like vtake and needs the left "ruler", while we would like to do it from the right
split :: SDim d -> Tensor (DimAppend d d') a -> Tensor d (Tensor d' a)
split SDNil t = L t
split (SDCons _ d) (H t) = H (split d t)
split (SDCons (SS n) d) (t :- ts) = (split d t) :- (split (SDCons n d) ts)

splitOne :: Tensor (DCons n d) a -> Tensor (DCons n DNil) (Tensor d a)
splitOne (H t) = H (L t)
splitOne (t :- ts) = L t :- splitOne ts

toSDim :: Tensor d a -> SDim d
toSDim (L _) = SDNil
toSDim (H t) = SDCons SI (toSDim t)
toSDim (_ :- ts) = case toSDim ts of
    SDCons n d -> SDCons (SS n) d

range :: Num a => SPNat n -> Tensor (DCons n DNil) a
-- range SI = H (L 0)
range n = f n 0
    where f :: Num a => SPNat n -> a -> Tensor (DCons n DNil) a
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
