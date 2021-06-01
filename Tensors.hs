{-# OPTIONS_GHC -W #-}
{-# LANGUAGE GADTs, DataKinds, KindSignatures, StandaloneDeriving, TypeFamilies, TypeOperators, ScopedTypeVariables, TypeApplications, AllowAmbiguousTypes, TemplateHaskell, QuasiQuotes #-}

import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import Language.Haskell.TH.Quote
import Control.Monad
import Text.ParserCombinators.Parsec
import ParseTensor

data PNat :: * where
    I :: PNat
    S :: PNat -> PNat deriving Show

infixr 6 :>
data Vec :: PNat -> * -> * where
    V    :: a -> Vec 'I a
    (:>) :: a -> Vec n a -> Vec ('S n) a

deriving instance (Show a) => Show (Vec n a)

data Dim = DNil | DCons Dim PNat deriving Show

type family (a :: Dim) <~> (b :: Dim) :: Dim
type instance (DCons d n) <~> (DCons d' n) = DCons (d <~> d') n
type instance (DCons d I) <~> (DCons d' n) = DCons (d <~> d') n
type instance (DCons d n) <~> (DCons d' I) = DCons (d <~> d') n
type instance DNil <~> d = d
type instance d <~> DNil = d

class HasDim d where
    type Dimensions d :: Dim

instance HasDim Double where
    type Dimensions Double = DCons DNil I

instance HasDim a => HasDim (Vec n a) where
    type Dimensions (Vec n a) = DCons (Dimensions a) n

broadcastable :: (HasDim a, HasDim b, HasDim c, Dimensions a <~> Dimensions b ~ Dimensions c) => a -> b -> c -> ()
broadcastable a b c = ()

data SPNat (n::PNat) where
    SI :: SPNat I
    SS :: SPNat n -> SPNat (S n)

deriving instance Show (SPNat n)

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
