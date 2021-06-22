module ParseArray where
import Text.ParserCombinators.Parsec
import Control.Monad

data NA a = NAL a | NAV String | NALV String | NA [NA a] deriving Show

finalNt :: Parser (NA Integer)
finalNt = nt <* end

nt :: Parser (NA Integer)
nt = (NAL <$> int) <|> (NALV <$> (char 'L' >> many1 letter)) <|> (NAV <$> many1 letter)
     <|> (NA <$> (char '[' >> many1 (skipMany (char ' ') >> nt) <* skipMany (char ' ') <* char ']'))

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
