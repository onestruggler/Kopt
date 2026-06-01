module ThreeSquares (get_three_squares) where

import Quantum.Synthesis.StepComp
import Quantum.Synthesis.EuclideanDomain
import Quantum.Synthesis.Diophantine 
import Quantum.Synthesis.Matrix
import Quantum.Synthesis.Ring hiding (i)
import Data.List
import System.Random
import Lagarias

import Data.Number.FixedPrec
import System.Environment


-- main :: IO ()
-- main = do 
--   args <- getArgs
--   let numstr = head args
--   let num' = read numstr :: Integer
--   let num = abs num'
--   let (a, b, c) = get_three_squares num
--   putStrLn $"= " ++ (show $abs a) ++ "^2 <br>+ " ++ (show $abs b) ++ "^2 <br>+ " ++ (show $abs c) ++ "^2 <br> "





get_three_squares :: Integer -> (Integer,Integer, Integer)
get_three_squares = three_squares (mkStdGen 8) 

factor4e n
  | n `mod` 4 /= 0  = (0,n)
  | otherwise  = (1+e', n1)
  where (e', n1) = factor4e (n`div`4)



-- myArgs = Args
--   { replay          = Nothing
--   , maxSuccess      = 10000
--   , maxDiscardRatio = 10
--   , maxSize         = 9223372036854775807
--   , chatty          = True
--   , maxShrinks      = 0
--   }

-- threeS :: Integer -> Bool
-- threeS n | n ==0 = True
-- threeS ni = b where
--   n' = abs ni
--   n'' = n'^7 +1001
--   (e,n) = factor4e n''
--   b = case n `mod` 8 == 7 of
--     True -> True
--     False -> three_squares_sum (three_squares (mkStdGen 8) n) == n


-- cmat_prop :: Integer -> Bool
-- cmat_prop n | n == 0 = True
-- cmat_prop ni = b where
--   n' = abs ni
--   n'' = n'^7 - 1
--   (e,n) = factor4e n'
--   m = cmat n
--   (a,f) = qred m
--   at = matrix_transpose a
--   b = if n <=10 then True else case n `mod` 8 == 7 of
--     True -> True
--     False -> at*m*a == f && f == id33 && det33 a == -1
--       && det33 m == -1 && at*adjF a == id33

three_squares :: (RandomGen g) => g -> Integer -> (Integer, Integer, Integer)
three_squares g 0 = (0,0,0)
three_squares g n = (a',b',c') where
  (e,n') = factor4e n
  (a,b,c) =  three_squares' g n'
  (a',b',c') = (2^e*a, 2^e*b, 2^e*c )
  factor4e n
    | n `mod` 4 /= 0  = (0,n)
    | otherwise  = (1+e', n1)
    where (e', n1) = factor4e (n`div`4)


data Case = I | II | III | IV deriving (Show, Eq)

three_squares' :: (RandomGen g) => g -> Integer -> (Integer, Integer, Integer)
three_squares' g n | n < 100 = h
  where
    candis = [0..csqrt n]
    h = case null c3 of
      True -> error "This number cannot be written as a sum of 3 squares"
      False -> head c3
    c3 = [(a,b,c) | a <- candis, b <- candis, c <- candis, a^2+b^2+c^2 == n]
three_squares' g n = (r13',r23',r33') where
  (q,a,c) = case n `mod` 4 of
    2 -> (4*n, 2*n-1, I)
    _ -> case n `mod` 8 of
      7 -> error "This number cannot be written as a sum of 3 squares"
      1 -> (8*n, 6*n-1, II)
      3 -> (4*n, (5*n-1) `div` 2, III)
      5 -> (4*n, (3*n-1) `div` 2, IV)
  (p,d,a12') = run (step12 g n q a c)
  a12 = if c == I || c == II then a12' else
    if ((a12' + d) `mod` 2) == 0 then a12' else a12' + p
  a22 = d*n -1
  a11 = (d + a12^2) `div` a22
  matF :: Mat33
  matF = matrix [[a11,a12,1], [a12, a22, 0], [1, 0, n]]
  matA :: Mat33
  (matA, matF')  = qred matF
  matA_inv = adjF matA
  trdcol = (rows_of_matrix matA_inv) !! 2
  r13' = trdcol !! 0 
  r23' = trdcol !! 1 
  r33' = trdcol !! 2 



cmat n' = matF where
  (e1,n) = factor4e n'
  g = mkStdGen 8
  (q,a,c) = case n `mod` 4 of
    2 -> (4*n, 2*n-1, I)
    _ -> case n `mod` 8 of
      7 -> error "This number cannot be written as a sum of 3 squares"
      1 -> (8*n, 6*n-1, II)
      3 -> (4*n, (5*n-1) `div` 2, III)
      5 -> (4*n, (3*n-1) `div` 2, IV)
  (p,d,a12') = run (step12 g n q a c)
  a12 = if c == I || c == II then a12' else
    if ((a12' + d) `mod` 2) == 0 then a12' else a12' + p
  a22 = d*n -1
  a11 = (d + a12^2) `div` a22
  matF :: Mat33
  matF = matrix [[a11,a12,1], [a12, a22, 0], [1, 0, n]]
  matA :: Mat33
  (matA, matF')  = qred matF
  m' = rows_of_matrix matA
  r11 = m' !! 0 !! 0
  r12 = m' !! 0 !! 1
  r21 = m' !! 1 !! 0
  r22 = m' !! 1 !! 1
  r31 = m' !! 2 !! 0
  r32 = m' !! 2 !! 1
  r13' = det $ matrix [[r21,r22],[r31,r32]]
  r23' = - (det $ matrix [[r11,r12],[r31,r32]])
  r33' = det $ matrix [[r11,r12],[r21,r22]]
  factor4e n
    | n `mod` 4 /= 0  = (0,n)
    | otherwise  = (1+e', n1)
    where (e', n1) = factor4e (n`div`4)





det :: Mat22 -> Integer
det m = d where
  m' = rows_of_matrix m
  a11 = m' !! 0 !! 0
  a12 = m' !! 0 !! 1
  a21 = m' !! 1 !! 0
  a22 = m' !! 1 !! 1
  d = a11*a22 - a12*a21



-- | return A \in SL(Z)
-- lagarias :: Mat -> Mat
-- lagarias m = m

--  (k, g') = randomR (0, 2*q^2) g
--  p = q*k + a
--  let (d,a12') = 
  -- let cd = case c of
  --       I -> (p + 1) `div` n
  --       II -> (p + 1) `div` n
  --       III -> (2*p + 1) `div` n
  --       IV -> (2*p + 1) `div` n        
  -- let ca12 = calR cd p
  -- case ca12 of
  --   Just a12 -> return (cd, a12,0)
  --   Nothing ->  three_squares' g' n
  -- let r = case p `mod` 8 of
  --       3 -> power_mod (-d) ((p+1) `div` 4) p
  --       7 -> power_mod (-d) ((p+1) `div` 4) p        
  --       5 -> power_mod (-d) ((p+3) `div` 8) p
  -- let d = (p - 1) `div` n


calR :: Integer -> Integer -> Maybe Integer
calR d p | p `mod` 4 == 3 = r where
           r' = power_mod (-d) ((p+1) `div` 4) p
           r = if r'*r' `mod` p == (-d) `mod` p then Just r' else Nothing
calR d p | p `mod` 8 == 5 = r where
           r' = power_mod (-d) ((p+3) `div` 8) p
           rm = r'*r' `mod` p
           af = power_mod 2 ((p-1)`div` 4) p
           r1 = (r' * af) `mod` p
           r = if rm == (-d) `mod` p then  Just r' else if rm == d `mod` p then
             if r1*r1 `mod` p == -d `mod` p then Just r1 else Nothing
             else Nothing
             
-- take integer n, q, a, c,  find D and a12, as in (2)'
step12 :: (RandomGen g) => g -> Integer -> Integer ->  Integer -> Case -> StepComp (Integer, Integer, Integer)
step12 g n q a c = do
  tick
  let (k, g') = randomR (0, 2*q^2) g
  let p = q*k + a
  let cd = case c of
        I -> (p + 1) `div` n
        II -> (p + 1) `div` n
        III -> (2*p + 1) `div` n
        IV -> (2*p + 1) `div` n        
  let ca12 = calR cd p
  case ca12 of
    Just a12 -> return (p, cd, a12)
    Nothing ->  step12 g' n q a c
  
             
        
  -- let ssum = three_squares_sum
  -- let re = head $ [(a,b,c) | a <- [0..csqrt n], b <- [0..csqrt n], c <- [0..csqrt n], ssum (a,b,c) == n]
  -- return re



three_squares_sum :: (Integer, Integer, Integer) -> Integer
three_squares_sum (a,b,c) = a^2+b^2+c^2
    

-- | return ceiling of a sqrt
csqrt :: Integer -> Integer
csqrt n = ceiling (fromIntegral n)
