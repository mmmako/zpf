{-# OPTIONS_GHC -W #-}
{-# LANGUAGE GADTs, DataKinds, KindSignatures, StandaloneDeriving, TemplateHaskell #-}

module TensorQuasi where
import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import Language.Haskell.TH.Quote
import ParseTensor
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
data Tensor :: Dim -> * -> * where
    L    :: a -> Tensor DNil a
    (:-) :: Tensor d a -> Tensor (DCons n d) a -> Tensor (DCons (S n) d) a
    H    :: Tensor d a -> Tensor (DCons I d) a

-- deriving instance Show a => Show (Tensor d a)
instance Show a => Show (Tensor d a) where
    show (L a) = show a
    show (H t) = "[" ++ show t ++ "]"
    show t = "[" ++ f t ++ "]"
        where f :: Show a => Tensor d' a -> String
              f (h :- t) = show h ++ " " ++ f t
              f (H t) = show t

m = QuasiQuoter { quoteExp = f , quotePat = g}
    where f s = case parse finalNt "" s of
                    Left _ -> error "error while parsing tensor"
                    -- Right nt -> case shape nt of
                        -- Nothing -> error "wrong shape of tensor"
                        -- Just _ -> ntToT nt
                    Right nt -> ntToT nt
          g s = case parse finalNt "" s of
                    Left _ -> error "error while parsing tensor"
                    Right nt -> ntToTp nt

n = QuasiQuoter { quoteExp = f }
    where f s = return $ g $ read s
          g n | n < 1 = error "positive interger must be at least 1"
          g 1 = ConE 'SI
          g n = AppE (ConE 'SS) (g (n - 1))

ntToT :: NT Integer -> Q Exp
ntToT (NTL n) = AppE (ConE 'L) <$> liftData n
ntToT (NTV v) = return $ VarE $ mkName v
ntToT (NTLV v) = return $ AppE (ConE 'L) $ VarE $ mkName v
ntToT (NT nts') = let (nt:nts) = reverse nts' in
        do a <- AppE (ConE 'H) <$> ntToT nt
           foldM f a nts
    where f e' nt = do
            e <- ntToT nt
            return (AppE (AppE (ConE '(:-)) e) e')

ntToTp :: NT Integer -> Q Pat
ntToTp (NTL n) = return $ ConP 'L [LitP $ IntegerL n]
ntToTp (NTV v) = return $ VarP $ mkName v
ntToTp (NTLV v) = return $ ConP 'L [VarP $ mkName v]
ntToTp (NT nts') = let (nt:nts) = reverse nts' in
        do a <- ConP 'H <$> (:[]) <$> ntToTp nt
           foldM f a (reverse nts)
    where f p' nt = do
            p <- ntToTp nt
            return $ ConP '(:-) [p, p']

