module ParseTensor where
import Text.ParserCombinators.Parsec
import Control.Monad

-- non-dependent tensor (sounds very smart)
data NT a = NTL a | NTV String | NTLV String | NT [NT a] deriving Show

{-
shape :: NT a -> Maybe [Int]
shape (NTL _) = Just [1]
shape (NT (nt:nts)) =
    do
        sh <- shape nt
        foldM (\sh nt ->
            do
                sh' <- shape nt
                if sh == sh'
                    then return sh
                    else mzero) sh nts
        return $ (length (nt:nts)):sh
-}

finalNt :: Parser (NT Integer)
finalNt = nt <* end

nt :: Parser (NT Integer)
nt = (NTL <$> int) <|> (NTLV <$> (char 'L' >> many1 letter)) <|> (NTV <$> many1 letter) <|> (NT <$> (char '[' >> many1 (skipMany (char ' ') >> nt) <* skipMany (char ' ') <* char ']'))

-- TODO probably a better way to do it
end :: Parser ()
end = do
    chars <- many anyChar
    case chars of
        [] -> return ()
        _ -> fail "expected end of string"

nat :: Parser Integer
nat = read <$> many1 digit

int :: Parser Integer
int = negative nat <|> nat where
  negative :: (Num a) => Parser a -> Parser a
  negative p = fmap negate (char '-' >> p)
