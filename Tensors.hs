{-# OPTIONS_GHC -W #-}
{-# LANGUAGE GADTs, DataKinds, KindSignatures, StandaloneDeriving, TypeFamilies, TypeOperators, ScopedTypeVariables, TypeApplications, AllowAmbiguousTypes, TemplateHaskell, QuasiQuotes, PolyKinds, FlexibleContexts #-}

{-
import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import Language.Haskell.TH.Quote
import Control.Monad
import Text.ParserCombinators.Parsec
import ParseTensor
-}

data PNat :: * where
    I :: PNat
    S :: PNat -> PNat deriving Show

data SPNat (n::PNat) where
    SI :: SPNat I
    SS :: SPNat n -> SPNat (S n)

deriving instance Show (SPNat n)

data Dim = DNil | DCons Dim PNat deriving Show

data DimS :: Dim -> * where
    DNilS  :: DimS DNil
    DConsS :: DimS d -> SPNat n -> DimS (DCons d n)

infixr 6 :|
data Tensor :: Dim -> * -> * where
    L    :: a -> Tensor DNil  a
    (:|) :: Tensor d a -> Tensor (DCons d n) a -> Tensor (DCons d (S n)) a
    H    :: Tensor d a -> Tensor (DCons d I) a

-- deriving instance (Show a) => Show (Tensor d a)
instance Show a => Show (Tensor d a) where
    show (L a) = show a
    show (H t) = "[" ++ show t ++ "]"
    show t = "[" ++ f t ++ "]"
        where f :: Tensor d' a -> String
              f (h :| t) = show h ++ " " ++ f t
              f (H t) = show t

class GetSPNat (n :: PNat) where
    getSPNat :: SPNat n
instance GetSPNat I where
    getSPNat = SI
instance GetSPNat n => GetSPNat (S n) where
    getSPNat = SS getSPNat

class GetDimS (d :: Dim) where
    getDimS :: DimS d
instance GetDimS DNil where
    getDimS = DNilS
instance (GetSPNat n, GetDimS d) => GetDimS (DCons d n) where
    getDimS = DConsS getDimS getSPNat 

{-
replicate :: SPNat n -> Tensor d a -> Tensor (DCons d n) a
replicate SI t = H t
replicate (SS n) t = t :| (Main.replicate n t)
-}

replicate' :: DimS (DCons d n) -> Tensor d a -> Tensor (DCons d n) a
replicate' (DConsS d SI) t = H t
replicate' (DConsS d (SS n)) t = t :| (replicate' (DConsS d n) t)

type family (a :: Dim) <~> (b :: Dim) :: Dim where
    (DCons d n) <~> (DCons d' n) = DCons (d <~> d') n
    (DCons d I) <~> (DCons d' n) = DCons (d <~> d') n
    (DCons d n) <~> (DCons d' I) = DCons (d <~> d') n
    DNil <~> d = d
    d <~> DNil = d
{-
type instance (DCons d (S n)) <~> (DCons d' (S n)) = DCons (d <~> d') (S n)
type instance (DCons d I) <~> (DCons d' (S n)) = DCons (d <~> d') (S n)
type instance (DCons d (S n)) <~> (DCons d' I) = DCons (d <~> d') (S n)
type instance (DCons d I) <~> (DCons d' I) = DCons (d <~> d') I
-}
{-
type instance (DCons d I) <~> (DCons d' n) = DCons (d <~> d') n
type instance (DCons d n) <~> (DCons d' I) = DCons (d <~> d') n
type instance (DCons d n) <~> (DCons d' n) = DCons (d <~> d') n
type instance DNil <~> d = d
type instance d <~> DNil = d
-}

-- broadcast :: Tensor d a -> Tensor d' b -> Tensor (d <~> d') (a, b)
-- broadcast :: GetDimS (d <~> d') => Tensor d a -> Tensor d' b -> Tensor (d <~> d') (a, b)
-- broadcast :: Tensor d a -> Tensor d' b -> DimS (d <~> d') -> Tensor (d <~> d') (a, b)
{-
broadcast (L a) (L b) _ = L (a, b)
broadcast l@(L _) (H t) (DConsS d _) = H (broadcast l t d)
broadcast l@(L _) (h :| t) (DConsS d (SS n)) = (broadcast l h d) :| (broadcast l t (DConsS d n))
broadcast (H t1) (H t2) (DConsS d SI) = H (broadcast t1 t2 d)
broadcast (H t1) (t2 :| t3) (DConsS d (SS n)) = (broadcast t1 t2 d) :| (broadcast (H t1) t3 (DConsS d n))
broadcast (h1 :| t1) (h2 :| t2) (DConsS d (SS n)) = (broadcast h1 h2 d) :| undefined -- (broadcast t1 t2 (DConsS d (SS n)))
-}
-- broadcast :: Tensor d a -> Tensor d' b -> DimS d -> DimS d' -> Tensor (d <~> d') (a, b)
broadcast :: d'' ~ (d <~> d') => Tensor d a -> Tensor d' b -> DimS d -> DimS d' -> Tensor d'' (a, b)
broadcast (L a) (L b) _ _ = L (a, b)
broadcast l@(L _) (H t) d (DConsS d' _) = H (broadcast l t d d')
broadcast l@(L _) (h :| t) d (DConsS d' (SS n)) = (broadcast l h d d') :| (broadcast l t d (DConsS d' n))
broadcast (H t1) (H t2) (DConsS d SI) (DConsS d' SI) = H (broadcast t1 t2 d d')
broadcast (H t1) (t2 :| t3) (DConsS d SI) (DConsS d' (SS n)) = (broadcast t1 t2 d d') :| (broadcast (H t1) t3 (DConsS d SI) (DConsS d' n))
broadcast (h1 :| t1) (h2 :| t2) (DConsS d (SS n)) (DConsS d' (SS n')) = (broadcast h1 h2 d d') :| undefined -- (broadcast t1 t2 (DConsS d n) (DConsS d' n'))

{-
infixr 6 :>
data Vec :: PNat -> * -> * where
    V    :: a -> Vec 'I a
    (:>) :: a -> Vec n a -> Vec ('S n) a

deriving instance (Show a) => Show (Vec n a)

data Dim = DNil | DCons Dim PNat deriving Show

class HasDim d where
    type Dimensions d :: Dim

instance HasDim Double where
    type Dimensions Double = DCons DNil I

instance HasDim a => HasDim (Vec n a) where
    type Dimensions (Vec n a) = DCons (Dimensions a) n


type family (m :: PNat) <~> (n :: PNat) :: PNat
    where (S n) <~> (S n) = S n
          I <~> (S n) = S n
          (S n) <~> I = S n
          I <~> I = I

type family (v1 :: Vec m a) <~~> (v2 :: Vec n b) :: Vec (m <~> n) c
type instance (V a) <~~> (V b) = V (a <~~> b)

n = QuasiQuoter { quoteExp = return . f . read }
    where f 1 = ConE 'SI
          f n = AppE (ConE 'SS) (f (n-1))

m = QuasiQuoter { quoteExp = f }
    where f s = case parse finalNt "" s of
                    Left _ -> error "error while parsing tensor"
                    Right nt -> case shape nt of
                        Nothing -> error "wrong shape of tensor"
                        Just _ -> ntToT nt

ntToT :: NT Integer -> Q Exp
ntToT (NTL n) = liftData n
ntToT (NT nts') = let (nt:nts) = reverse nts' in
        do a <- AppE (ConE 'V) <$> ntToT nt
           foldM f a (reverse nts)
    where f e' nt = do
            e <- ntToT nt
            return (AppE (AppE (ConE '(:>)) e) e')
-}
