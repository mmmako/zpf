{-# OPTIONS_GHC -W -fno-max-relevant-binds #-}
{-# LANGUAGE QuasiQuotes, TypeApplications, GADTs, DataKinds #-}

import HackExpanded
import TensorQuasi
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

-- image:     m x n x 3
-- want:  5 x m x n x 3
-- interp:5 x 1 x 3 x 3
main' :: (Ex2 (Matrix1 (Double, Double, Double))) -> String -- [[(Double, Double, Double)]]
main' (Ex2 (Matrix1 mat)) = show $ const 0 <$> trans' -- toLL matfour
    where f (x, y, z) = L x :- L y :- H (L z)
          mat' = unsplit $ f <$> mat
          trans1 = fromInteger <$> [m|[[1 0 0] [0 1 0] [0 0 1]]|]
          trans2 = fromInteger <$> [m|[[0 1 0] [0 0 1] [1 0 0]]|]
          {-
          trans3 = ([m|[3]|] |*| trans1 |+| [m|[7]|] |*| trans2) |/| [m|[10]|]
          mat'' = splitOne mat'
          mat''' = unsplit $ (\x -> mul x trans3) <$> mat''
          matfour = g <$> (unsplit $ splitOne <$> splitOne mat''')
          -}
          g :: Tensor (DCons (S (S I)) DNil) a -> (a, a, a)
          g (L x :- L y :- H (L z)) = (x, y, z)
          -- 5 x 1 x 1 x 1
          interpA = unsplit $ (H . H . H . L) <$> range [n|5|] |/| [m|[4]|]
          interpB = [m|[1]|] |-| interpA
          -- 5 x 1 x 3 x 3
          trans = trans1 |*| interpB |+| trans2 |*| interpA
          -- 5 x 1 x (3 x 3)
          trans' = unsplit $ splitOne <$> splitOne trans
          mat'' = splitOne mat'
          -- qwe = broadcast trans' mat''

main = do
    file <- readFile "io-monad.pnm"
    let l = loadPbm file
        mat = fromLL l
    case mat of
        Nothing -> putStrLn "failed to parse"
        Just mat ->
            -- writeFile "io-monad1.pnm" $ savePbm $ main' mat
            putStrLn $ main' mat
    {-
    putStrLn "saving 1"
    putStrLn "saving 2"
    writeFile "io-monad2.pnm" $ savePbm l
    -}
