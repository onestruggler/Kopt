{-# LANGUAGE TemplateHaskell #-}
module Main where

import U4Di hiding (I, II)
import qualified U4Di as UD
import qualified SO6 as SO6
import Language.Haskell.TH
import Language.Haskell.TH.Syntax
import qualified Quantum.Synthesis.MultiQubitSynthesis as MS
import Quantum.Synthesis.MultiQubitSynthesis
import Quantum.Synthesis.EuclideanDomain
import Quantum.Synthesis.Ring
import qualified Quantum.Synthesis.Matrix as SM
import Quantum.Synthesis.Matrix
import Data.List
import Clifford
import Test.QuickCheck hiding (label)
import Glaudell hiding (main' , lde , H1, H0)
import Translations
import System.IO
import System.Environment

import Control.Concurrent (threadDelay)

import Control.Monad(void)
import Graphics.Rendering.Chart
import Graphics.Rendering.Chart.Easy
import Graphics.Rendering.Chart.Grid
--import Graphics.Rendering.Chart.Backend.Diagrams(toFile, renderableToFile)

import Kopt

import System.Environment (getArgs)
import System.Exit (exitFailure)

main = main_ok

main_data = do
  sequence_ $ map g100 $ [1..120]


c15_skcz = [[],[K0],[K1],[K0,S0],[K0,K1],[K1,S1],[K0,S0,K1],[K0,K1,S1],[K0,K1,CZ],[K0,S0,K1,S1],[K0,S0,K1,CZ],[K0,K1,S1,CZ],[K0,K1,CZ,K0],[K0,S0,K1,S1,CZ],[K0,S0,K1,CZ,K1]]

c15_6 = [[K0],[K1],[K0,S0],[K0,CX],[K1,S1],[K0,S0,CX]]
c15_6i' = [c ++ d | c <- c15_6, d <- [[],[CS]]]
c15_6i = [c ++ d | c <- c15_6, d <- [[CS]]]

main_consecutive_cs_in_P_8 = do
  sequence_ $ map print  $ filter (\(x, (a,b,c)) -> b == 8) $ nubBy (\(x, (a,b,c)) (x', (a',b',c')) -> a == a' &&  b == b' && take 2 c == take 2 c') $ zip [1..] $ map (\x -> let x' = synth (u4of x) in (csc x', kc x', x)) $ [p0 ++ p1 ++ p2 ++ p3 ++ p4 ++ p5 ++ p6  ++ p7 |  p0 <- c15_6i, p1 <- c15_6i, p2 <- c15_6i, p3 <- c15_6i, p4 <- c15_6i, p5 <- c15_6i, p6 <- c15_6i, p7 <- c15_6i]

  

main_23 = do
  sequence_ $ map print $ nubBy (\(x, (a,b,c)) (x', (a',b',c')) -> a == a' &&  b == b' &&take 2 c == take 2 c') $ zip [1..] $ map (\x -> (csc x, kc x, x)) $ map synth $ map u4of [[K1]++p1++[K1] ++ p2 ++ [K1] |  p1 <- gperms_mphase, p2 <- gperms_mphase]


diag_cirs_mod_phase = [f b0 Z0 ++ f b1 Z1 ++ f b2 S0 ++ f b3 S1 ++ f b4 CZ  ++ f b5 CS | b0 <- [0,1], b1 <- [0,1], b2 <- [0,1], b3 <- [0,1], b4 <- [0,1], b5 <- [0,1], let f = replicate ]

gperms_mphase = [p ++ d | p <- map snd perm_cirs', d <- diag_cirs_mod_phase]



main_1 = do
  args <- getArgs
  let k = read (head args) :: Int
  ms1 <- generate $ vectorOf 100000 (arbitrary :: Gen U4Di)
  let ms = map product $ grouping (k) ms1
  print $ map lde $ take 10 ms
  -- print (u4of cir ==  u4of (synth $ u4of cir))
  -- print (synthGlaudell $ u4of (concat $ replicate k [CK,KC]))

main_ok :: IO ()
main_ok = do
  args <- getArgs
  case args of
    ["-data", k] -> do
      mat <- readMatrixFromFile (read k)
      print_output True mat
      
    ["-data", k, "-glaudell"] -> do
      mat <- readMatrixFromFile (read k)
      print_output False mat

    [matrix] -> do
      let mat = readMatrix matrix
      print_output True mat
      
    [matrix, "-glaudell"] -> do
      let mat = readMatrix matrix
      print_output False mat
      
    _ -> do
      putStrLn "Usage: ./Main -data k [-glaudell] | ./Main matrix [-glaudell]"
      exitFailure


print_output b mat= do
  pm mat
  print cir
  print (lde mat, csc cir, kc cir, length cir )
  where
    cir = if b then synth mat else synthGlaudell mat


synthGlaudell m = x''
  where
    x' = synth m
    x'' = synthcs (map t2_of_t2' x')


readMatrix x = x''
  where
    (k,es) = read x :: (Integer, [[(Integer, Integer)]])
    x'' :: U4Di
    x'' = matrix_of_rows (map (map (parse_Di k)) es)


readMatrixFromFile lk = do
  content <- readFile "experiment_data.dat"
  let linesOfFiles = lines content
  let pts0 = (map read linesOfFiles) :: [((Integer, [[(Integer, Integer)]]) , Int, Int, Int, Int)]
  let (k,es) = (\(a,b,c,d,e) -> a) (pts0 !! lk)
  let x'' = matrix_of_rows (map (map (parse_Di k)) es)
  return x''



-- instance Arbitrary (U4 DComplex) where
--   arbitrary = do
--     w1 <- vectorOf 1 (arbitrary :: Gen [CliffordT2])
--     return $ u4of $ concat w1

c15_lde2 = [[K0,K1],[K0,S0,K1],[K0,CX,K0],[K0,K1,S1],[K0,S0,CX,K0],[K0,S0,CX,K1],[K0,S0,K1,S1],[K0,S0,K1,XC]]

gen_matk :: Integer -> Gen U4Di
gen_matk k
  | k < 0 = error "gen_matk: k<0"
  | k == 1 = do
      n <- choose (0,6143)
      return $ u4of $ gperms !! n
  | k == 2 = do
      n <- choose (0,6143)
      n' <- choose (0,7)
      return $ u4of $ (gperms !! n) ++ (c15_lde2 !! n')
  | k == 3 = do
      n <- choose (0,11519)
      return $ u4of $ cli_2k_mod_phase !! n
  | otherwise = undefined
  where
    (a,b,c) = undefined --get_three_squares (2 ^ k- 1)


(====) :: U4Di -> U4Di -> Bool
(====) x y = or [x == y * u4of (replicate k UD.II) | k <- [0..3]]

parse_Di :: Integer -> (Integer, Integer) -> DComplex
parse_Di k (x, y) = inv_gamma ^ k * from_whole (Cplx x y)

parse_mat :: (Integer, [[(Integer, Integer)]]) -> U4Di
parse_mat = undefined

main_check_data = do
  content <- readFile "experiment_data.dat"
  let linesOfFiles = lines content
  print $ length linesOfFiles
  let pts0 = take 1000 $ drop 4400 $ (map read linesOfFiles) :: [((Integer, [[(Integer, Integer)]]) , Int, Int, Int, Int)]
  let pts1 = map (\((k,es), mycs , jcs, mykc, jkc) ->
                    (matrix_of_rows (map (map (parse_Di k)) es) :: U4Di, mycs, jcs, mykc, jkc)) pts0

  let lrs = map (\(m, mycs , jcs, mykc, jkc) -> let x' = synth m in (m, x', synthcs (map t2_of_t2' x'))) pts1
  print ("lde" , "mycs", "ocs", "mykc", "Julien's kc")
  let nc = map (\(x, a,b) -> (lde x, csc a, csc b, kc a, kc b)) lrs
  let vs = zipWith (\((k,es), mycs , jcs, mykc, jkc) (lde, mycs' , jcs', mykc', jkc') -> k == lde && mycs == mycs' && mykc == mykc' && jkc == jkc' && jcs == jcs') pts0 nc
  sequence_ $  map  print $  filter (\(a,b) -> not b) $ zip [1..] vs


-- main_bar kk = do
--   content <- readFile "experiment_data.dat"
--   let linesOfFiles = lines content
--   print $ length linesOfFiles
--   let pts0 = (map read linesOfFiles) :: [((Integer, [[(Integer, Integer)]]) , Int, Int, Int, Int)]
--   let pts = map (\(x,y) -> (fromIntegral x, fromIntegral y)) $  map (\((k,m),a,b,mykc, jkc) -> (k,jkc-mykc)) pts0

--   let values = compute_distr kk pts

--   toFile def "mychart.svg" $ do
--     layout_title .= ("K-count reduction percentage distribution for lde between " ++ show kk ++ " and " ++ (show (kk + 5)) )
--     layout_title_style . font_size .= 10
--     layout_x_axis . laxis_generate .= autoIndexAxis (map fst values)
--     plot $ fmap plotBars $ bars ["# of input that acheives K-count reduction x"] (addIndexes (map snd values))

    

-- main_grid = do
--   renderableToFile def "example13_big.png" $ fillBackground def $ gridToRenderable $  grid

compute_distr :: Integer -> [(Integer, Int)] -> [(String, [Double])]
compute_distr k xs = zip [show x | x <- lr] dis
  where
    kxs = filter (\(x, y) -> x `elem` [k..k+5]) xs
    xr = map snd kxs
    xrl = minimum xr
    xrr = maximum xr
    lr = [xrl..xrr]
    tt = fromIntegral $ length kxs
    dis = [[fromIntegral (length $ filter (\(x, y) -> fromIntegral y == red) kxs) / tt ] | red <- lr]


-- main_chart_read = do
--   args <- getArgs
--   content <- readFile "experiment_data.dat"
--   let linesOfFiles = lines content
--   print $ length linesOfFiles
--   let pts0 = (map read linesOfFiles) :: [((Integer, [[(Integer, Integer)]]) , Int, Int, Int, Int)]
--   let pts1 = map (\(x,y) -> (fromIntegral x, fromIntegral y)) $ map (\((k,m),a,b,mykc, jkc) -> (k,mykc)) pts0
--   let pts2 = map (\(x,y) -> (fromIntegral x, fromIntegral y)) $ map (\((k,m),a,b,mykc, jkc) -> (k,jkc)) pts0
--   let pts = map (\(x,y) -> (fromIntegral x, fromIntegral y)) $  map (\((k,m),a,b,mykc, jkc) -> (k,jkc-mykc)) pts0
--   let pts' = map (\(x,y) -> (fromIntegral x,  y)) $  map (\((k,m),a,b,mykc, jkc) -> (k,fromIntegral (a-b)/ fromIntegral a)) pts0
-- --  let pts = pts1 ++ pts2
  
--   toFile def "mychart.svg" $ do

--     layout_title .= "Experiments"
--     setColors [opaque blue, opaque red]
--     layout_x_axis . laxis_generate .= scaledAxis def (0::Float,100::Float)
--     layout_y_axis . laxis_generate .= scaledAxis def (-10::Float,100::Float)

-- --    plot (line "x=y" [[(0.0::Float,0.0::Float),(100.0,100.0)]])
--     -- plot (points "(lde, our rkc)" (pts1))
--     -- plot (points "(lde, Glaudell et al's rkc)" (pts2))
--     plot (points "(lde, Glaudell et al's rkc - our rkc)" (pts))


test_synthcs = do
  ms1 <- generate $ vectorOf 1000 (arbitrary :: Gen U4Di)
  let ms = map product $ grouping 70 ms1
  let lrs = map (\x -> let x' = synth x in (x, x', synthcs (map t2_of_t2' x'))) ms
  print ("test if the input and output of the implementation of Julien's algoritm match")
  sequence_ $ map print $ map (\(x, a,b) -> (lde x, x ==== u4of b)) lrs



data_of_mat :: U4Di -> (Integer, [[(Integer, Integer)]])
data_of_mat x = let (x', k) = lamdenomexp_decompose x in (k, (map (map f) (rows_of_matrix x')))
  where
    f (Cplx a b) = (a, b)

g100 gf = do
  ms1 <- generate $ vectorOf 100000 (arbitrary :: Gen U4Di)
  let ms = take 100 $ map product $ grouping gf ms1
  let lrs = map to_data ms
  h <- openFile "experiment_data.dat" AppendMode
  hPutStrLn h $ concat $ intersperse "\n" (map show lrs)
  hClose h




write_file = do
  sequence_ $ [g100 k | k <- [1..100]]
  


blackScholesCall :: Double -> Double -> Double -> Double -> Double -> Double
blackScholesCall s x t r v = s * normcdf d1 - x*exp (-r*t) * normcdf d2
  where
    d1 = ( log(s/x) + (r+v*v/2)*t )/(v*sqrt t)
    d2 = d1 - v*sqrt t

normcdf :: Double -> Double
normcdf x | x < 0 = 1 - w
          | otherwise = w
  where
    w = 1.0 - 1.0 / sqrt (2.0 * pi) * exp(-l*l / 2.0) * (a1 * k + a2 * (k**2) + a3 * (k**3) + a4 * (k**4) + a5 * (k**5))
    k = 1.0 / (1.0 + 0.2316419 * l)
    l = abs x
    a1 = 0.31938153
    a2 = -0.356563782
    a3 = 1.781477937
    a4 = -1.821255978
    a5 = 1.330274429


-- Construct a single chart for the grid
bsChart :: Double -> Double -> Double -> Layout Double Double
bsChart t r v = execEC $ do
    layout_y_axis . laxis_generate .= scaledAxis def (-10,80)
    plot $ line "" [ [(s,blackScholesCall s 100 0.001 r v) | s <- ss] ]
    plot $ line lbl [ [(s,blackScholesCall s 100 t r v) | s <- ss] ]
  where    
    ss = [50,51..150]
    lbl = "t = " ++ show t ++ ", r = " ++ show r

-- Construct a grid of charts, with a single title accross the top
grid = title `wideAbove` aboveN [ besideN [ layoutToGrid (bsChart t r v) | t <-ts ] | r <- rs ]
  where
    ts = [1,2,5]
    rs = [0.05,0.10,0.20]
    v = 0.10
    title = setPickFn nullPickFn $ label ls HTA_Centre VTA_Centre "Black Scholes Option Values"
    ls = def { _font_size   = 15 , _font_weight = FontWeightBold }

to_data :: U4Di -> ((Integer, [[(Integer, Integer)]]), Int, Int, Int, Int)
to_data m = (data_of_mat m, mycs, optcs, mykc, bestknownkc)
  where
    m' = synth m
    -- Note the matrix semantic of (map t2_of_t2' m') is m.
    m'' = synthcs (map t2_of_t2' m')
    mycs = csc m'
    mykc = kc m'
    optcs = csc m''
    bestknownkc = kc m''



mod3res :: [ZComplex]
mod3res = [1,-1,i,-i,0,1+i, 1-i,2]

mod3adj :: [Z2] -> [Z2]
mod3adj [a,b,c] = [a, b, (c + b)]

check_mod3adj = [res 3 (adj x) == mod3adj (res 3 x) | x <- mod3res]


main_read_write = do
  content <- readFile "experiment_data.dat"
  let linesOfFiles = lines content
  print $ length linesOfFiles
  let pts0 = (map read linesOfFiles) :: [((Integer, [[(Integer, Integer)]]) , Int, Int, Int, Int)]
  let pts = map (\((k,e), a, b, c, d) -> (k, a,b,c,d)) pts0
  let lgc = filter (\(line, (k,a,b,c,d)) -> 2 * k - fromIntegral c >= 2) (zip [1..] pts)
  let lgc' = map (\xx -> filter (\(line, (k,a,b,c,d)) -> 2 * k - fromIntegral c == xx) (zip [1..] pts)) [-2, -1, 0,1,2]
--  let lgc' = map ( (\(line, (k,a,b,c,d)) -> (line, k - fromIntegral a))) lgc
--  print $ maximum $ map (\(k,a,b,c,d) -> (fromIntegral a - fromIntegral k) / fromIntegral k) $ filter (\(k,a,b,c,d) -> k >=25) pts
  sequence_ $ map print $ map length lgc'

  -- h <- openFile "experiment_data_nomat.dat" AppendMode
  -- hPutStrLn h $ concat $ intersperse "\n" (map show pts)
  -- hClose h

main_cli_patterns = do
  sequence_ $ map print $ nub $ map cof $  map u4of cli_2k_mod_phase


chec_dec1p px = do
  m <- generate $ vectorOf 1000 (arbitrary :: Gen U4Di)
  let ps = filter (\x -> let (p,l,r) = lemma_six x in p == px) m
  let lrs = map (\x -> (decrease1_lde x, x)) ps
  let h = head ps
  print $ cof h
  print $ cof (dagger h)
  sequence_ $ map print $ nub $  map (\((ll,rr),x) -> (cof x, cof (u4of ll * x * u4of rr), lde x, lde (u4of ll * x * u4of rr), lde (u4of ll * x * u4of rr) == lde x -1)) lrs
