{-# OPTIONS_GHC -W #-}
{-# LANGUAGE GADTs, DataKinds, KindSignatures, StandaloneDeriving, TypeFamilies, TypeOperators, ScopedTypeVariables, TypeApplications, AllowAmbiguousTypes, TemplateHaskell, QuasiQuotes #-}

-- TODO disambiguate whether columns or rows

import Language.Haskell.TH
import Language.Haskell.TH.Quote

data PNat :: * where
  I :: PNat
  S :: PNat -> PNat

-- PNat is a kind, and so is PNat -> * -> *
infixr 6 :>
data Vec :: PNat -> * -> * where
  V    :: a -> Vec 'I a
  (:>) :: a -> Vec n a -> Vec ('S n) a

-- deriving instance (Show a) => Show (Vec n a)

instance Show a => Show (Vec n a) where
    showsPrec _ v = showString "[" . show' v . showString "]"

show' :: Show a => Vec n a -> String -> String
show' (V x) = shows x
show' (x :> xs) = shows x . showString " " . show' xs

data SPNat (n::PNat) where
  SI :: SPNat I
  SS :: SPNat n -> SPNat (S n)
deriving instance Show(SPNat n)

data NP :: PNat -> * where NP :: NP n deriving Show

infixr 5 :|
data Mat :: PNat -> PNat -> * -> * where
  M    :: Vec m a -> Mat m I a
  (:|) :: Vec m a -> Mat m n a -> Mat m ('S n) a

instance Show a => Show (Mat m n a) where
    showsPrec _ m = showString "[" . show'' m . showString "]"

show'' :: Show a => Mat m n a -> String -> String
show'' (M v) = shows v
show'' (c :| cs) = shows c . showString "\n" . show'' cs

rip :: Mat ('S m) n a -> (Vec n a, Mat m n a)
rip (M (x :> xs)) = (V x, M xs)
rip ((x :> xs) :| cols) = (x :> ys, xs :| m)
    where (ys, m) = rip cols

transpose :: Mat m n a -> Mat n m a
transpose (M (V x)) = M (V x)
transpose (M (x :> xs)) = (V x) :| transpose (M xs)
transpose ((V x) :| cols) = M (x :> cols')
    where M cols' = transpose cols -- TODO is this exhaustive?
transpose m@((_ :> _) :| _) = r :| (transpose m')
    where (r, m') = rip m

dot :: Num a => Vec n a -> Vec n a -> a
dot (V x) (V y) = x*y
dot (x :> xs) (y :> ys) = x*y + dot xs ys

instance Functor (Vec m) where
    fmap f (V x) = V (f x)
    fmap f (x :> xs) = (f x) :> (fmap f xs)

multiply :: Num a => Mat m n a -> Mat n k a -> Mat m k a
multiply (M v) (M (V x)) = M ((x *) <$> v)
multiply m@(_:>_ :| _) (M v) = M (x :> xs)
    where (r, rs) = rip m
          x = dot r v
          M xs = multiply rs (M v)
multiply m@((V _) :| _) (M v) = M (V (dot v' v))
    where M v' = transpose m
multiply m (c :| cs) = c' :| cs'
    where M c' = multiply m (M c)
          cs' = multiply m cs

fromListKinda' :: [a] -> SPNat m -> (Vec m a, [a])
fromListKinda' (x:xs) (SS n) = (x :> v, xs')
    where (v, xs') = fromListKinda' xs n
fromListKinda' (x:xs) SI = (V x, xs)
    
fromListKinda :: [a] -> SPNat m -> SPNat n -> Mat m n a
fromListKinda l m SI = M $ fst $ fromListKinda' l m
fromListKinda l m (SS n) = c :| fromListKinda l' m n
    where (c, l') = fromListKinda' l m

type family (m::PNat) :< (n::PNat) :: Bool
type instance m :< 'I = 'False
type instance 'I :< ('S n) = 'True
type instance ('S m) :< ('S n) = m :< n

-- TODO 1-indexing... meh
nth :: (m:<n) ~ 'True => SPNat m -> Vec n a -> a
nth SI (V a)  = a
nth SI (a:>_)  = a
nth (SS m') (_:>xs) = nth m' xs

testerino v1 v2 n = nth n v1 + nth n v2

n = QuasiQuoter { quoteExp = return . f . read }
    where f 1 = ConE 'SI
          f n = AppE (ConE 'SS) (f (n-1))
