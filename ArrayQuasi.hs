{-# OPTIONS_GHC -W #-}
{-# LANGUAGE GADTs, DataKinds, KindSignatures, StandaloneDeriving, TemplateHaskell, FlexibleInstances #-}

module ArrayQuasi where
import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import Language.Haskell.TH.Quote
import ParseArray
import Text.ParserCombinators.Parsec
import Control.Monad

data PNat :: * where
    I :: PNat
    S :: PNat -> PNat deriving Show

data SPNat (n::PNat) where
    SI :: SPNat I
    SS :: SPNat n -> SPNat (S n)

deriving instance Show (SPNat n)

data Dim = DNil | DCons PNat Dim deriving Show

data SDim :: Dim -> * where
    SDNil  :: SDim DNil
    SDCons :: SPNat n -> SDim d -> SDim (DCons n d)

infixr 6 :-
data Array :: Dim -> * -> * where
    L    :: a -> Array DNil a
    (:-) :: Array d a -> Array (DCons n d) a -> Array (DCons (S n) d) a
    H    :: Array d a -> Array (DCons I d) a

instance Show a => Show (Array d a) where
    show (L a) = show a
    show (H a) = "[" ++ show a ++ "]"
    show a = "[" ++ f a ++ "]"
        where f :: Show a => Array d' a -> String
              f (h :- t) = show h ++ " " ++ f t
              f (H a) = show a

m = QuasiQuoter { quoteExp = f , quotePat = g}
    where f s = case parse finalNt "" s of
                    Left _ -> error "error while parsing tensor"
                    Right nt -> ntToT nt
          g s = case parse finalNt "" s of
                    Left _ -> error "error while parsing tensor"
                    Right nt -> ntToTp nt

n = QuasiQuoter { quoteExp = f }
    where f s = return $ g $ read s
          g n | n < 1 = error "positive interger must be at least 1"
          g 1 = ConE 'SI
          g n = AppE (ConE 'SS) (g (n - 1))

ntToT :: NA Integer -> Q Exp
ntToT (NAL n) = AppE (ConE 'L) <$> liftData n
ntToT (NAV v) = return $ VarE $ mkName v
ntToT (NALV v) = return $ AppE (ConE 'L) $ VarE $ mkName v
ntToT (NA nts') = let (nt:nts) = reverse nts' in
        do a <- AppE (ConE 'H) <$> ntToT nt
           foldM f a nts
    where f e' nt = do
            e <- ntToT nt
            return (AppE (AppE (ConE '(:-)) e) e')

ntToTp :: NA Integer -> Q Pat
ntToTp (NAL n) = return $ ConP 'L [LitP $ IntegerL n]
ntToTp (NAV v) = return $ VarP $ mkName v
ntToTp (NALV v) = return $ ConP 'L [VarP $ mkName v]
ntToTp (NA nts') = let (nt:nts) = reverse nts' in
        do a <- ConP 'H <$> (:[]) <$> ntToTp nt
           foldM f a (reverse nts)
    where f p' nt = do
            p <- ntToTp nt
            return $ ConP '(:-) [p, p']
