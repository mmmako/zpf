{-# OPTIONS_GHC -W #-}
{-# LANGUAGE TypeApplications #-}

loadPbm :: String -> [[(Double, Double, Double)]]
loadPbm str = parsePbm w h max $ threes vals
    where lns = filter (not . ignore) $ lines str
          ignore "" = True
          ignore ('#':_) = True
          ignore _ = False
          [w, h] = read @Integer <$> words (lns !! 1)
          [max] = read @Integer <$> words (lns !! 2)
          vals = concat $ (map (read @Integer)) <$> words <$> drop 3 lns
          threes [] = []
          threes (x:y:z:t) = (x, y, z):threes t

parsePbm :: Integer -> Integer -> Integer -> [(Integer, Integer, Integer)] -> [[(Double, Double, Double)]]
parsePbm w _ max vals = (map f) <$> links w vals
    where links :: Integer -> [a] -> [[a]]
          links n [] = []
          links n l = take (fromIntegral n) l : links n (drop (fromIntegral n) l)
          f (x, y, z) = (fromInteger x / max', fromInteger y / max', fromInteger z / max')
          max' = fromInteger max

savePbm :: [[(Double, Double, Double)]] -> String
savePbm l = unlines $ ["P3", unwords [show (length (l !! 0)), show (length l)], "255"] ++ lns
    where lns = concat $ map f $ concat l
          f (x, y, z) = map (\x -> show $ round $ 255*x) [x, y, z]

main = do
    file <- readFile "io-monad.pnm"
    let l = loadPbm file
    putStrLn "saving 1"
    writeFile "io-monad1.pnm" $ savePbm l
    putStrLn "saving 2"
    writeFile "io-monad2.pnm" $ savePbm l
