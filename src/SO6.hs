--{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TemplateHaskell #-}
module SO6 where
import System.Environment
import qualified Data.Matrix as DM
import qualified Quantum.Synthesis.MultiQubitSynthesis as MS
import Quantum.Synthesis.MultiQubitSynthesis
import Quantum.Synthesis.EuclideanDomain
import Quantum.Synthesis.Ring
import Quantum.Synthesis.Matrix
import Data.Complex
import Control.Monad
import Data.List
import Test.QuickCheck
import Math.NumberTheory.Roots
import Language.Haskell.TH
import Language.Haskell.TH.Syntax

import qualified Syllables as Syl
import qualified LookupTable as LUT
-- Unitarity is not checked. Speical Unitarity is not checked.
type SU2 = Matrix Two Two DOmega
type SU4 a = Matrix Four Four a
type U4 a = Matrix Four Four a
-- Othognality and Speical Othognality are not checked.
type SO4 = Matrix Four Four DOmega
type O4 a = Matrix Four Four a
type SO6 a = Matrix Six Six a

det :: (Nat n, Num a) => Matrix n n a -> a
det = DM.detLaplace . DM.fromLists . rows_of_matrix

m :: SO4
m = roothalf `scalarmult` matrix_of_rows
  [
    [1,  0,  0,  i],
    [0,  i,  1,  0],
    [0,  i , -1,  0], 
    [1,  0,  0 , -i]
  ]

idm :: SO4
idm = matrix_of_rows
  [
    [1,  0,  0,  0],
    [0,  1,  0,  0],
    [0,  0,  1,  0], 
    [0,  0,  0 , 1]
  ]

case1 :: (SO6 DRootTwo)
case1 = mpq 0 1

id2 :: SU2
id2 = 1

cx' :: SO4
cx' = matrix_of_rows
  [
    [1,  0,  0,  0],
    [0,  1,  0,  0],
    [0,  0,  0,  -1], 
    [0,  0,  1,  0]
  ]

cx :: SU4 DOmega
cx = matrix_of_rows
  [
    [1,  0,  0,  0],
    [0,  1,  0,  0],
    [0,  0,  0,  1], 
    [0,  0,  1,  0]
  ]

cs :: SO4
cs = matrix_of_rows
  [
    [1,  0,  0,  0],
    [0,  1,  0,  0],
    [0,  0,  1,  0],
    [0,  0,  0,  i]
  ]

cz :: SO4
cz = matrix_of_rows
  [
    [1,  0,  0,  0],
    [0,  1,  0,  0],
    [0,  0,  1,  0],
    [0,  0,  0,  -1]
  ]

xx :: SO4
xx = matrix_of_rows
  [
    [0,  1,  0,  0],
    [1,  0,  0,  0],
    [0,  0,  0,  1], 
    [0,  0,  1,  0]
  ]

zz :: SO4
zz = matrix_of_rows
  [
    [1,  0,  0,  0],
    [0,  -1,  0,  0],
    [0,  0,  1,  0], 
    [0,  0,  0,  -1]
  ]

zz' :: SO4
zz' = matrix_of_rows
  [
    [1,  0,  0,  0],
    [0,  1,  0,  0],
    [0,  0,  -1,  0], 
    [0,  0,  0,  -1]
  ]

xm :: SU2
xm = matrix_of_rows
  [
    [0,  1],
    [1,  0]
  ]

h :: U2 DOmega
h = let a = roothalf in matrix_of_rows [[a,a],[a,-a]]

mh :: U2 DRootTwo
mh = let a = roothalf in matrix_of_rows [[a,-a],[a,a]]

t :: U2 DOmega
t = matrix_of_rows [[1,0],[0,omega]]

s :: U2 DOmega
s = matrix_of_rows [[1,0],[0,i]]

z :: U2 DOmega
z = matrix_of_rows [[1,0],[0,-1]]

ht :: U2 DOmega
ht = h * t

sht :: U2 DOmega
sht = s * h * t


instance Arbitrary ZRootTwo where
  arbitrary = RootTwo <$> arbitrary <*> arbitrary

instance Arbitrary DRootTwo where
  arbitrary = RootTwo <$> arbitrary <*> arbitrary

instance Arbitrary DOmega where
  arbitrary = Omega <$> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary

instance Arbitrary ZOmega where
  arbitrary = Omega <$> arbitrary <*> arbitrary <*> arbitrary <*> arbitrary

instance Arbitrary Dyadic where
  arbitrary = Dyadic <$> arbitrary <*> arbitrary

{-
instance Arbitrary SU2 where
  arbitrary = do
    bs <- (arbitrary :: Gen [Bool])
    let (ts, fs) = partition (\x -> x) bs
    let a = length ts * 5 + length fs * 7
    let b = 8 - (a `mod` 8)
    let m = product (map shtht bs) * t ^ b
    return m
    where
      shtht True = ht
      shtht False = sht
-}

{-      
instance Arbitrary SO4 where
  arbitrary = do
    a <- (arbitrary :: Gen SU2)
    b <- (arbitrary :: Gen SU2)
    return (adj m * (a `tensor` b) * m)
-}

instance Arbitrary (SU4 DOmega) where
  arbitrary = do
    w1 <- (arbitrary :: Gen [CliffordT2])
    return $ su4of w1
    
data CliffordT2 =
  S0
  | S1
  | Z0
  | Z1
  | H0
  | H1
  | X0
  | X1
  | T0
  | T1
  | CS
  | CZ
  | WI
  | Ex

  | CX
  | XC

  deriving (Show, Eq, Ord, Read, Lift)

instance Arbitrary CliffordT2 where
  arbitrary = do
    -- temporarily disallow T
    n <- choose (0,11)
    return $ [S0,S1,H0,H1,CS,CZ,X0,X1,Ex,WI,Z0,Z1] !! n
    -- n <- choose (0,13)
    -- return $ [S0,S1,H0,H1,T0,T1,CS,CZ,X0,X1,Ex,WI,Z0,Z1] !! n

class SU4of a where
  su4of :: a -> SU4 DOmega

instance SU4of CliffordT2 where
  su4of S0 = s `tensor` id2
  su4of S1 = id2 `tensor` s
  su4of Z0 = z `tensor` id2
  su4of Z1 = id2 `tensor` z
  su4of H0 = h `tensor` id2
  su4of H1 = id2 `tensor` h
  su4of T0 = t `tensor` id2
  su4of T1 = id2 `tensor` t
  su4of CZ = cz
  su4of CS = cs
  su4of Ex = twolevel_matrix (0,1) (1,0) 1 2
  su4of X1 = id2 `tensor` xm
  su4of X0 = xm `tensor` id2
  su4of WI = omega `scalarmult` 1

  su4of CX = cx
  su4of XC = su4of Ex * cx * su4of Ex

instance SU4of a => SU4of [a] where
  su4of [] = 1
  su4of (h:t) = su4of h * su4of t

class SO6of a where
  so6of :: a -> (SO6 DRootTwo)

instance SO6of a => SO6of [a] where
  so6of [] = 1
  so6of (h:t) = so6of h * so6of t

instance SO6of CliffordT2 where
  so6of WI = -1 `scalarmult` 1
  so6of S0 = twolevel_matrix (0,-1) (1,0) 0 1
  so6of S1 = twolevel_matrix (0,-1) (1,0) 3 4
  so6of H0 = twolevel_matrix (0,1) (1,0) 0 2 * onelevel_matrix (-1) 1
  so6of H1 = twolevel_matrix (0,1) (1,0) 3 5 * onelevel_matrix (-1) 4
  so6of CZ = twolevel_matrix (0,-1) (1,0) 0 1 *
             twolevel_matrix (0,-1) (1,0) 2 5 *
             twolevel_matrix (0,-1) (1,0) 3 4
  so6of CS = roothalf `scalarmult` (twolevel_matrix (1,-1) (1,1) 0 1 *
             twolevel_matrix (1,-1) (1,1) 2 5 *
             twolevel_matrix (1,-1) (1,1) 3 4)
  so6of Ex = matrix_of_rows [[0, 0, 0, -1, 0, 0], [0, 0, 0, 0, -1, 0], [0, 0, 0, 0, 0, -1],
                               [1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0]]
  so6of X1 = matrix_of_rows [[-1, 0, 0, 0, 0, 0], [0, -1, 0, 0, 0, 0], [0, 0, -1, 0, 0, 0],
                             [0, 0, 0, -1, 0, 0], [0, 0, 0, 0, 1, 0], [0, 0, 0, 0, 0, 1]]
  so6of X0 = matrix_of_rows [[-1, 0, 0, 0, 0, 0], [0, 1, 0, 0, 0, 0], [0, 0, 1, 0, 0, 0],
                             [0, 0, 0, -1, 0, 0], [0, 0, 0, 0, -1, 0], [0, 0, 0, 0, 0, -1]]

  so6of T1 = let r = roothalf in (twolevel_matrix (r,-r) (r,r) 3 4)
  so6of T0 = let r = roothalf in (twolevel_matrix (r,-r) (r,r) 0 1)
  so6of Z0 = (1 :: U2 DRootTwo) `oplus` (-1 `scalarmult` 1)
  so6of Z1 = (-1 `scalarmult` (1 :: Matrix Three Three DRootTwo)) `oplus` (1 :: U2 DRootTwo) `oplus` (-1)


data Pauli = I | X | Y | Z deriving (Show, Eq, Ord)

type SignedPauli2 = (Bool, Pauli, Pauli)

mpq :: Int -> Int -> (SO6 DRootTwo)
mpq = MS.twolevel_matrix (roothalf, -roothalf) (roothalf, roothalf)

mpq' :: Int -> Int -> (SO6 DRootTwo)
mpq' j k = MS.twolevel_matrix (roothalf, -roothalf) (roothalf, roothalf) k j

rot :: SignedPauli2 -> (SO6 DRootTwo)
rot (True, I, I) = 1
rot (True, I, X) = mpq 4 5
rot (True, I, Y) = mpq 5 3
rot (True, I, Z) = mpq 3 4
rot (True, X, I) = mpq 1 2
rot (True, X, X) = mpq 3 0
rot (True, X, Y) = mpq 4 0
rot (True, X, Z) = mpq 5 0
rot (True, Y, I) = mpq 2 0
rot (True, Y, X) = mpq 3 1
rot (True, Y, Y) = mpq 4 1
rot (True, Y, Z) = mpq 5 1
rot (True, Z, I) = mpq 0 1
rot (True, Z, X) = mpq 3 2
rot (True, Z, Y) = mpq 4 2
rot (True, Z, Z) = mpq 5 2

rot (False, I, I) = 1
rot (False, I, X) = mpq' 4 5
rot (False, I, Y) = mpq' 5 3
rot (False, I, Z) = mpq' 3 4
rot (False, X, I) = mpq' 1 2
rot (False, X, X) = mpq' 3 0
rot (False, X, Y) = mpq' 4 0
rot (False, X, Z) = mpq' 5 0
rot (False, Y, I) = mpq' 2 0
rot (False, Y, X) = mpq' 3 1
rot (False, Y, Y) = mpq' 4 1
rot (False, Y, Z) = mpq' 5 1
rot (False, Z, I) = mpq' 0 1
rot (False, Z, X) = mpq' 3 2
rot (False, Z, Y) = mpq' 4 2
rot (False, Z, Z) = mpq' 5 2


unrot :: Int -> Int -> (Bool,Pauli, Pauli)
unrot  4 5 = (True,I, X)
unrot  5 3 = (True,I, Y)
unrot  3 4 = (True,I, Z)
unrot  1 2 = (True,X, I)
unrot  3 0 = (True,X, X)
unrot  4 0 = (True,X, Y)
unrot  5 0 = (True,X, Z)
unrot  2 0 = (True,Y, I)
unrot  3 1 = (True,Y, X)
unrot  4 1 = (True,Y, Y)
unrot  5 1 = (True,Y, Z)
unrot  0 1 = (True,Z, I)
unrot  3 2 = (True,Z, X)
unrot  4 2 = (True,Z, Y)
unrot  5 2 = (True,Z, Z)
unrot  j k = (False, p , q)
  where
    (s,p,q) = unrot k j

instance Arbitrary (SO6 DRootTwo) where
  arbitrary = do
    w1 <- (arbitrary :: Gen [(Int,Int)])
    w2 <- (arbitrary :: Gen [(Int,Int)])
    w3 <- (arbitrary :: Gen [(Int,Int)])
    w4 <- (arbitrary :: Gen [(Int,Int)])
    w5 <- (arbitrary :: Gen [(Int,Int)])
    w6 <- (arbitrary :: Gen [(Int,Int)])
    w7 <- (arbitrary :: Gen [(Int,Int)])
    w8 <- (arbitrary :: Gen [(Int,Int)])
    let w0 = w1 ++ w2 ++ w3 ++ w4 ++ w5 ++ w6 ++ w7 ++ w8
    let w1' = filter (\(j,k) -> j `mod` 6 /= k `mod` 6) w0
    ic <- chooseInt (0,11519)
    return $ product (map (\(j,k) -> mpq (j `mod` 6) (k `mod` 6)) w1') * so6of (clifford_nf2_reduced !! ic)


data Pattern =
  Case Int ([Int], [Int]) ([Int], [Int]) ([Int], [Int])
  deriving (Show, Eq, Ord)

fix_pattern :: Pattern -> ([(Index, Index)], [(Index, Index)])
fix_pattern (Case 1 (a,b) (c,d) (e,f)) = (reverse (concat $ map fixa $ zip [0,1] a), concat $ map fixa $ zip [0,1] b)
fix_pattern (Case 2 (a,b) (c,d) (e,f)) = (reverse (concat $ map fixa $ zip [0,1,2,3] a), concat $ map fixa $ zip [0,1,2,3] b)
  
fix_pattern (Case 3 (a,b) (c,d) (e,f)) = (reverse (concat $ map fixa $ zip [0,1,2,3] a), concat $ map fixa $ zip [0,1,2,3] b)
fix_pattern (Case 4 (a,b) (c,d) (e,f)) = (reverse (concat $ map fixa $ zip [0,1,2,3] a), concat $ map fixa $ zip [0,1,2,3] b)
fix_pattern (Case 5 (a,b) (c,d) (e,f)) =
  (reverse ((concat $ map fixa $ zip [0,1,2,3] a)), (concat $ map fixa $ zip [0,1,2,4] b) )
fix_pattern (Case 6 (a,b) (c,d) (e,f)) = (reverse ((concat $ map fixa $ zip [0,1] c) ++ (concat $ map fixa $ zip [2,3] e)), concat $ (map fixa $ zip [0,1] ([0..5]\\(d ++ f))) ++ (map fixa $ zip [2,3] []) ++ (map fixa $ zip [4,5] f))
fix_pattern (Case 7 (a,b) (c,d) (e,f)) = (reverse ((concat $ map fixa $ zip [0,1] a) ++ (concat $ map fixa $ zip [2,3] c) ++ (concat $ map fixa $ zip [4,5] e)), (concat $ map fixa $ zip [0,1] b) ++ (concat $ map fixa $ zip [2,3] d) ++ (concat $ map fixa $ zip [4,5] f))
fix_pattern (Case 8 (a,b) (c,d) (e,f)) = (nub (reverse ((concat $ map fixa $ zip [0,1] a) ++ (concat $ map fixa $ zip [2,3] c) ++ (concat $ map fixa $ zip [4,5] []))), (concat $ map fixa $ zip [0,1] b) ++ (concat $ map fixa $ zip [2,3] d) ++ (concat $ map fixa $ zip [4,5] []))

fix_pa = (\(a,b) -> (nub a, nub b)) . fix_pattern . (\(Case k (a,b) (c,d) (e,f)) -> Case k (sort a, sort b) (sort c, sort d) (sort e, sort f) )

mytlx :: Num a => (Index, Index) -> SO6 a
mytlx (a,b) = twolevel_matrix (0,1) (1,0) a b

fixa :: (Int, Int) -> [(Index, Index)]
fixa (a, b)
  | a == b = []
  | otherwise = if a <= b then (a,b) : [] else (b,a) : []

instance {-# OVERLAPS #-} Show (Z2, Z2) where
  show (Even, Even) = "00"
  show (Even, Odd) = "01"
  show (Odd, Even) = "10"
  show (Odd, Odd) = "11"

instance {-# OVERLAPS #-} Show (Z2, Z2, Z2) where
  show (Even, Even, Even) = "000"
  show (Even, Odd,Even) = "010"
  show (Odd, Even,Even) = "100"
  show (Odd, Odd,Even) = "110"
  show (Even, Even, Odd) = "001"
  show (Even, Odd,Odd) = "011"
  show (Odd, Even,Odd) = "101"
  show (Odd, Odd,Odd) = "111"

instance {-# OVERLAPS #-} Show (Z2, Z2, Z2,Z2) where
  show (Even, Even, Even, Even) = "0000"
  show (Even, Odd,Even, Even) = "0100"
  show (Odd, Even,Even, Even) = "1000"
  show (Odd, Odd,Even, Even) = "1100"
  show (Even, Even, Odd, Even) = "0010"
  show (Even, Odd,Odd, Even) = "0110"
  show (Odd, Even,Odd, Even) = "1010"
  show (Odd, Odd,Odd, Even) = "1110"
  show (Even, Even, Even, Odd) = "0001"
  show (Even, Odd,Even, Odd) = "0101"
  show (Odd, Even,Even, Odd) = "1001"
  show (Odd, Odd,Even, Odd) = "1101"
  show (Even, Even, Odd, Odd) = "0011"
  show (Even, Odd,Odd, Odd) = "0111"
  show (Odd, Even,Odd, Odd) = "1011"
  show (Odd, Odd,Odd, Odd) = "1111"

instance {-# OVERLAPS #-} Show (Z2, Z2, Z2,Z2,Z2) where
  show (a,b,c,d,e) = concat $ map show [a,b,c,d,e]

maxlde_index :: (SO6 DRootTwo) -> [(Index, Index)]
maxlde_index m = filter (\(j,k) -> denomexp (matrix_index m j k) == de) $
      [(j,k) | j <- [0..5], k <- [0..5]]
  where
    de = denomexp m

choosek :: (Eq a, Ord a) => Int -> [a] -> [[a]]
choosek _ [] = []
choosek 0 _ = []
choosek 1 xs = map (\x -> x : []) $ nub xs
choosek n xs' = let xs = nub xs' in nub $ map sort [y : ys | [y] <- choosek 1 xs, ys <- choosek (n-1) (xs \\ [y])]

find_blank1 :: [(Int, Int)] -> (([Int], [Int]), ([Int], [Int]))
find_blank1 jks = (ret1, ret2')
  where
    rows = nub $ map fst jks
    cols = nub $ map snd jks
    ret1 = (rows, cols)
    ret2 = filter (\(js, ks) -> sort jks == sort (cross rows cols \\ cross js ks)) [(js, ks) | js <- choosek 2 rows, ks <- choosek 2 cols]
    ret2' = case ret2 of
      [] -> ([],[])
      (h:t) -> h

find_blank2 :: [(Int, Int)] -> (([Int], [Int]), ([Int], [Int]), ([Int], [Int]))
find_blank2 jks = (ret1, ret2', ret3)
  where
    rows = nub $ map fst jks
    cols = nub $ map snd jks
    ret1 = (rows, cols)
    ret2 = filter (\((js, ks), (js', ks')) -> sort jks == sort ((cross rows cols \\ cross js ks) \\ cross js' ks')) [((js, ks), (js', ks')) | js <- choosek 2 rows, ks <- choosek 2 cols, js' <- choosek 2 (rows\\js), ks' <- choosek 2 (cols\\ks)]
    (ret2', ret3) = case ret2 of
      [] -> (([],[]), ([],[]))
      (h:t) -> h

find_blank3 :: [(Int, Int)] -> (([Int], [Int]), ([Int], [Int]), ([Int], [Int]), ([Int], [Int]))
find_blank3 jks = (ret1, ret2', ret3, ret4)
  where
    rows = nub $ map fst jks
    cols = nub $ map snd jks
    ret1 = (rows, cols)
    ret2 = filter (\((js, ks), (js', ks'), (js'', ks'')) -> sort jks == sort (((cross rows cols \\ cross js ks) \\ cross js' ks') \\ cross js'' ks'')) [((js, ks), (js', ks'), (js'', ks'')) | js <- choosek 2 rows, ks <- choosek 2 cols, js' <- choosek 2 (rows \\js), ks' <- choosek 2 (cols \\ks), js'' <- choosek 2 ((rows\\js)\\js'), ks'' <- choosek 2 ((cols \\ks) \\ks')]
    (ret2', ret3, ret4) = case ret2 of
      [] -> (([],[]), ([],[]), ([],[]))
      (h:t) -> h

find_blank3' :: [(Int, Int)] -> (([Int], [Int]), ([Int], [Int]), ([Int], [Int]))
find_blank3' jks = ( ret2', ret3, ret4)
  where
    rows = nub $ map fst jks
    cols = nub $ map snd jks
    ret1 = (rows, cols)
    ret2 = filter (\((js, ks), (js', ks'), (js'', ks'')) -> sort jks == sort (((cross js ks) ++ cross js' ks') ++ cross js'' ks''))  [((js, ks), (js', ks'), (js'', ks'')) | js <- choosek 2 rows, ks <- choosek 2 cols, js' <- choosek 2 (rows \\js), ks' <- choosek 2 (cols \\ks), js'' <- choosek 2 ((rows\\js)\\js'), ks'' <- choosek 2 ((cols \\ks) \\ks')]
    (ret2', ret3, ret4) = case ret2 of
      [] -> (([],[]), ([],[]), ([],[]))
      (h:t) -> h


--cross :: [Int] -> [Int] -> [(Int, Int)]
cross rows cols = [(j,k) | j <-rows, k <- cols]

pattern_of :: (SO6 DRootTwo) -> Pattern
pattern_of m = ret
  where
    jks = maxlde_index m
    rows = sort $ nub $ map fst jks
    cols = sort $ nub $ map snd jks
    
    ret = case sort jks == sort (cross rows cols) of
      True -> case (length rows, length cols) of
        (2,2) -> Case 1 (rows, cols) ([],[]) ([],[])
        (4,4) -> Case 3 (rows, cols) ([],[]) ([],[])
        (4,2) -> Case 2 (rows, cols) ([],[]) ([],[])
        (2,4) -> Case 2 (rows, cols) ([],[]) ([],[])
      False -> case find_blank1 jks of
        (cls, ([],[])) -> case find_blank2 jks of
          (cls, ([],[]), ([],[])) -> case find_blank3 jks of
            (cls, ([],[]), ([],[]), ([],[]) ) -> case find_blank3' jks of
              (([],[]), ([],[]), ([],[])) -> error "pattern_of: none of the eight patterns works."
              (cls1, cls2, cls3) -> Case 7 cls1 cls2 cls3
            (cls, ncls1, ncls2, ncls3) -> case (length rows, length cols) of
              (6,6) -> Case 8 ncls1 ncls2 ncls3
              _ -> error "pattern_of: none of the eight patterns works."
          (cls, ncls1, ncls2) -> case (length rows, length cols) of
            (4,4) -> Case 5 cls ncls1 ncls2
            (4,6) -> Case 6 cls ncls1 ncls2
            (6,4) -> Case 6 cls ncls1 ncls2
        (cls, ncls) -> Case 4 cls ncls ([],[])

prop_patterns_cover :: (SO6 DRootTwo) -> Bool
prop_patterns_cover m = denomexp m < 1 || elem (case_of (pattern_of m)) [1..8]

case_of :: Pattern -> Int
case_of (Case k _ _ _) = k

main3 = do
  quickCheckWithResult stdArgs {maxSuccess = 1000 , chatty = True} prop_simp
  print $ and $ map prop_simp clifford_nf2

main4 = do
  quickCheckWithResult stdArgs {maxSuccess = 10000 , chatty = True} prop_synth_u4b

t_count :: [CliffordT2] -> Int
t_count cir = t_count_t + 3 * t_count_cs
  where
    t_count_t = length $ filter (\x -> x == T1 || x == T0) cir
    t_count_cs = length $ filter (\x -> x == CS) cir

main0 = do
  cosetEnumA' eq_upto_gp_nf (map (\x -> [x]) [S0,S1,H0,H1,CZ,X0,X1,Ex,Z0,Z1]) ([[]],[[]])

main2 = do
  args <- getArgs
  let cir1 = read (args!!0) :: [CliffordT2]
  let cir = reverse cir1
--  quickCheckWithResult stdArgs {maxSuccess = 100 , chatty = True} prop_synth_u4
--  gm' <- replicateM 100 (gen_case k)
--  print gm'
  let t_c = t_count cir
  let cir' = synth_u4 cir
  let t_c' = t_count cir'
  let ret = show (reverse cir') ++ ".   T-count of input: " ++ show t_c ++ ".   T-count of output: " ++ show t_c' ++ "."
  putStrLn ret
  

  -- let rr = map (\m -> let (a,b) = decrease k m in (denomexp (so6ofii a * m * so6ofii b), denomexp m)) gm'
  -- print rr
  -- let ret = filter (\x -> x /= (0,0)) $ sort $ nub $ rr
  -- let retd = nub $ sort $ map (\(a,b) -> b - a) ret
  -- let nz = filter (\x -> fst x /=0 ) rr
  -- print $ length rr
  -- print $ length nz
  -- print "hello"
  -- print ret
  -- print retd

pm :: (Nat n , Show a) => Matrix n n a -> IO ()
pm m = sequence_ $ map print $ rows_of_matrix m

pm6 :: SO6 DRootTwo -> IO ()
pm6 m = do
  print k
  sequence_ $ map print $ rows_of_matrix m'
  where
    (m',k) = denomexp_decompose m

pm6p :: SO6 DRootTwo -> IO ()
pm6p m = do
  print k
  sequence_ $ map print $ rows_of_matrix $ matrix_map res1 m'
  where
    pa = pattern_of m
    (l,r) = fix_pa pa
    ll = product $ map mytlx l
    rr = product $ map mytlx r
    mm = ll * m * rr
    (m',k) = denomexp_decompose mm

pmat :: SO6 DRootTwo -> Int -> IO ()
pmat m re = do
  let resn = if re == 1 then show . res1 else if re == 2 then show . res2 else show . res3
  print k
  sequence_ $ map print $ rows_of_matrix $ matrix_map resn m'
  where
    (m',k) = denomexp_decompose m

pmatf1 :: SO6 DRootTwo -> Bool ->  IO ()
pmatf1 m fb = do
  print k
  sequence_ $ map print $ rows_of_matrix $ matrix_map res1 $ if fb then m' else m''
  where
    pa = pattern_of m
    (l,r) = fix_pa pa
    ll = product $ map mytlx l
    rr = product $ map mytlx r
    mm = ll * m * rr
    (m',k) = denomexp_decompose mm
    (m'',k'') = denomexp_decompose m

pmatf2 :: SO6 DRootTwo -> Bool -> IO ()
pmatf2 m fb = do
  print k
  sequence_ $ map print $ rows_of_matrix $ matrix_map res2 $ if fb then m' else m''
  where
    pa = pattern_of m
    (l,r) = fix_pa pa
    ll = product $ map mytlx l
    rr = product $ map mytlx r
    mm = ll * m * rr
    (m',k) = denomexp_decompose mm
    (m'',k'') = denomexp_decompose m

pmatf3 :: SO6 DRootTwo -> Bool ->  IO ()
pmatf3 m fb = do
  print k
  sequence_ $ map print $ rows_of_matrix $ matrix_map res3  $ if fb then m' else m''
  where
    pa = pattern_of m
    (l,r) = fix_pa pa
    ll = product $ map mytlx l
    rr = product $ map mytlx r
    mm = ll * m * rr
    (m',k) = denomexp_decompose mm
    (m'',k'') = denomexp_decompose m

pmatf4 :: SO6 DRootTwo -> Bool ->  IO ()
pmatf4 m fb = do
  print k
  sequence_ $ map print $ rows_of_matrix $ matrix_map res4 $ if fb then m' else m''
  where
    pa = pattern_of m
    (l,r) = fix_pa pa
    ll = product $ map mytlx l
    rr = product $ map mytlx r
    mm = ll * m * rr
    (m',k) = denomexp_decompose mm
    (m'',k'') = denomexp_decompose m

pmatf5 :: SO6 DRootTwo -> Bool ->  IO ()
pmatf5 m fb = do
  print k
  sequence_ $ map print $ rows_of_matrix $ matrix_map res5 $ if fb then m' else m''
  where
    pa = pattern_of m
    (l,r) = fix_pa pa
    ll = product $ map mytlx l
    rr = product $ map mytlx r
    mm = ll * m * rr
    (m',k) = denomexp_decompose mm
    (m'',k'') = denomexp_decompose m


ff x = do
  pm $ matrix_map (snd . (\x -> divmod x (roottwo))) $ fst $ denomexp_decompose x
  putStrLn ""

ff2 x = do
  pm $ matrix_map (snd . (\x -> divmod x (fromInteger 2))) $ fst $ denomexp_decompose x
  putStrLn ""

ff3 x = do
  pm $ matrix_map (snd . (\x -> divmod x (roottwo ^ 3))) $ fst $ denomexp_decompose x
  putStrLn ""

--gen_case :: Int -> (SO6 DRootTwo)
gen_case k = do
  m <- generate (arbitrary :: Gen (SO6 DRootTwo))
  case denomexp m < 1 of
    True -> gen_case k
    False -> case case_of (pattern_of m) == k of
      True -> return m
      False -> gen_case k


--gen_case :: Int -> (SO6 DRootTwo)
gen_denom k = do
  m <- generate (arbitrary :: Gen (SO6 DRootTwo))
  case denomexp m == k of
    False -> gen_denom k
    True -> return m

res_table = map (\(a,b,c) -> (a + b * roottwo + c * 2 :: ZRootTwo) ) [(a,b,c) | a <- [0,1], b <- [0,1], c <- [0,1]]
res_table2 = map (\(a,b) -> (a + b * roottwo :: ZRootTwo) ) [(a,b) | a <- [0,1], b <- [0,1]]

res_table_sq = map (\x -> res3 (x^2)) res_table
res_table_sq2 = map (\x -> res2 (x^2)) res_table2

res1 :: ZRootTwo -> Z2
res1 x
  | roottwo `euclid_divides` (x - 0)  = Even
  | roottwo `euclid_divides` (x - 1)  = Odd

res2 :: ZRootTwo -> (Z2,Z2)
res2 x
  | 2 `euclid_divides` (x - 0)  = (Even, Even)
  | 2 `euclid_divides` (x - (0+roottwo))  = (Even, Odd )
  | 2 `euclid_divides` (x - 1)  = (Odd, Even )
  | 2 `euclid_divides` (x - (1+roottwo))  = (Odd, Odd )

res3 :: ZRootTwo -> (Z2,Z2,Z2)
res3 x
  | (roottwo^3) `euclid_divides` (x - 0)  = (Even, Even, Even)
  | (roottwo^3) `euclid_divides` (x - (0+roottwo))  = (Even, Odd, Even)
  | (roottwo^3) `euclid_divides` (x - (0+2))  = (Even, Even, Odd)
  | (roottwo^3) `euclid_divides` (x - (0+roottwo +2))  = (Even, Odd, Odd)
  | (roottwo^3) `euclid_divides` (x - 1)  = (Odd, Even, Even)
  | (roottwo^3) `euclid_divides` (x - (1+roottwo))  = (Odd, Odd, Even)
  | (roottwo^3) `euclid_divides` (x - (1+2))  = (Odd, Even, Odd)
  | (roottwo^3) `euclid_divides` (x - (1+roottwo +2))  = (Odd, Odd, Odd)

res4 :: ZRootTwo -> (Z2,Z2,Z2,Z2)
res4 x
  | (roottwo^4) `euclid_divides` (x - 0)  = (Even, Even, Even,Even)
  | (roottwo^4) `euclid_divides` (x - (0+roottwo))  = (Even, Odd, Even,Even)
  | (roottwo^4) `euclid_divides` (x - (0+2))  = (Even, Even, Odd,Even)
  | (roottwo^4) `euclid_divides` (x - (0+roottwo +2))  = (Even, Odd, Odd,Even)
  | (roottwo^4) `euclid_divides` (x - 1)  = (Odd, Even, Even,Even)
  | (roottwo^4) `euclid_divides` (x - (1+roottwo))  = (Odd, Odd, Even,Even)
  | (roottwo^4) `euclid_divides` (x - (1+2))  = (Odd, Even, Odd,Even)
  | (roottwo^4) `euclid_divides` (x - (1+roottwo +2))  = (Odd, Odd, Odd,Even)
  | (roottwo^4) `euclid_divides` (x - roottwo^3)  = (Even, Even, Even,Odd)
  | (roottwo^4) `euclid_divides` (x - (0+roottwo+roottwo^3))  = (Even, Odd, Even,Odd)
  | (roottwo^4) `euclid_divides` (x - (0+2+roottwo^3))  = (Even, Even, Odd,Odd)
  | (roottwo^4) `euclid_divides` (x - (0+roottwo +2+roottwo^3))  = (Even, Odd, Odd,Odd)
  | (roottwo^4) `euclid_divides` (x - (1+roottwo^3))  = (Odd, Even, Even,Odd)
  | (roottwo^4) `euclid_divides` (x - (1+roottwo+roottwo^3))  = (Odd, Odd, Even,Odd)
  | (roottwo^4) `euclid_divides` (x - (1+2+roottwo^3))  = (Odd, Even, Odd,Odd)
  | (roottwo^4) `euclid_divides` (x - (1+roottwo +2+roottwo^3))  = (Odd, Odd, Odd,Odd)


residue_m :: Int -> ZRootTwo -> [Z2]
residue_m 0 _ = []
residue_m 1 (RootTwo a b) = [if a `mod` 2 == 1 then Odd else Even]
residue_m k x
  | k < 0 = error "k should be greater than or equal to 0"
  | k > 0 = ih ++ [rk]
  where
    ih = residue_m (k-1) x
    
    zrt_of_z2 :: Z2 -> ZRootTwo
    zrt_of_z2 Even = 0
    zrt_of_z2 Odd = 1

    res = sum $ zipWith (*) (map zrt_of_z2 ih) [roottwo ^ l | l <- [0..k-2]]
    RootTwo a b = (x - res) `euclid_div` (roottwo ^ (k-1))
    rk = if a `mod` 2 == 1 then Odd else Even

res5 x = let [a,b,c,d,e] = residue_m 5 x in (a,b,c,d,e)

scalar_omega = [S0,H0,S0,H0,S0,H0]
scalar_i = [WI]

class ToCliffordT2 a where
  to_ct2 :: a -> CliffordT2


a_box0 = [[],[H0], [H0,S0,H0]]
a_box1 = [[],[H1], [H1,S1,H1]]

b_box = [
  [H1,CZ,H0,H1,CZ,H0,H1,CZ],
  [CZ,H0,H1,CZ],
  [H0,S0,CZ,H0,H1,CZ],
  [H0,CZ,H0,H1,CZ]
  ]

c_box0 = [[], [H0,S0,S0,H0]]  
c_box1 = [[], [H1,S1,S1,H1]]

d_box = [
  [CZ,H0,H1,CZ,H0,H1,CZ,H1],
  [H0,CZ,H0,H1,CZ,H1],
  [H0,H1,S1,CZ,H0,H1,CZ,H1],
  [H0,H1,CZ,H0,H1,CZ,H1]
  ]

e_box0 = [replicate k S0 | k <- [0..3]]
e_box1 = [replicate k S1 | k <- [0..3]]

l_stair2 = [a ++ b ++ c | a <- a_box1, b <- b_box, c <- c_box0] ++ l_stair1
r_stair2 = [d ++ e | d <- d_box, e <- e_box1]

l_stair1 = [a  ++ c | a <- a_box0, c <- c_box0]
r_stair1 = [e | e <- e_box0]

all_scalars = [(replicate k WI) | k <- [0..3]]

clifford_nf2 =  map reverse [s ++ l2 ++ r2 ++ l1 ++ r1 | s <- all_scalars, l2 <- l_stair2, r2 <- r_stair2, l1 <- l_stair1, r1 <- r_stair1 ]
clifford_nf2_modscalar =  map reverse [l2 ++ r2 ++ l1 ++ r1 | l2 <- l_stair2, r2 <- r_stair2, l1 <- l_stair1, r1 <- r_stair1 ]
clifford_nf2_reduced = sortBy (\x y -> compare (length x) (length y)) $ map simp clifford_nf2_modscalar

myeven :: ZRootTwo -> Bool
myeven (RootTwo a b) = even b

myodd :: ZRootTwo -> Bool
myodd (RootTwo a b) = odd b

prop_case k = do
  m <- gen_case k
  return undefined

find_case3_2x2_block :: (SO6 ZRootTwo) -> ([Int],[Int]) -> Maybe ([Int],[Int])
find_case3_2x2_block xm (rows, cols) = ret
  where
    candi_rs = choosek 2 rows
    candi_cs = choosek 2 cols
    ret = find (\(rs,cs) -> let entries = [matrix_index xm j k | j <- rs, k <-cs] in all myeven entries || all myodd entries) [(rs,cs) | rs <- candi_rs, cs <- candi_cs]
        

pred1 :: (SO6 a) -> (Int, Int) -> (a -> Bool) -> Bool
pred1 m (j,k) p = p (matrix_index m j k)

pred2 :: (SO6 a) -> (Int, Int) -> (Int, Int) -> (a -> a -> Bool) -> Bool
pred2 m (j,k) (j', k') p = p (matrix_index m j k) (matrix_index m j' k')

equal_res :: SO6 ZRootTwo -> (Int, Int) -> (Int, Int) -> Bool
equal_res m jk jk' = pred2 m jk jk' (\x y -> res2 x == res2 y)

equal_res3 :: SO6 ZRootTwo -> (Int, Int) -> (Int, Int) -> Bool
equal_res3 m jk jk' = pred2 m jk jk' (\x y -> res3 x == res3 y)

unJust (Just a) = a

same_dk_cond :: SO6 DRootTwo -> (Int, Int) -> (Int, Int) -> Bool
same_dk_cond m' (f1,k1) (f2,k2) = (denomexp(matrix_index m' f1 k1) == lde-1 && denomexp (matrix_index m' f2 k2)==lde-1) || (denomexp(matrix_index m' f1 k1) < lde-1 && denomexp (matrix_index m' f2 k2) < lde-1)
  where
    (m,lde) = denomexp_decompose m'


find_v5jk :: Bool -> SO6 DRootTwo -> [Int] -> [Int] -> (Int, Int)
find_v5jk b m' rs cs = ret'
  where
    (m,lde) = denomexp_decompose m'
    fi = head $ [0..5]\\rs
    fic = head $ [0..5]\\cs
    candis = choosek 2 cs
    candis' = choosek 2 rs
    ret = if b
      then unJust $ find (\[k1,k2] -> same_dk_cond m' (fi,k1) (fi,k2)) candis
      else unJust $ find (\[k1,k2] -> equal_res m (k1, fic) (k2, fic) || equal_res3 m (k1, fic) (k2, fic)) candis'
    ret' = (ret !! 0, ret !! 1)

find_121324 :: Bool -> SO6 DRootTwo -> [Int] -> [Int] -> Maybe (Int, Int)
find_121324 b m' rs cs = ret'
  where
    (m,lde) = denomexp_decompose m'
    col x = map (\j -> matrix_index m j x) rs
    row x = map (\k -> matrix_index m x k) cs
    candis = choosek 2 cs
    candis' = choosek 2 rs
    fi = ([0..5]\\rs)!!0
    fi' = ([0..5]\\cs)!!0
    good_cpairs = filter (\[k1,k2] -> length (filter (\(a,b) -> res2 a == res2 b) (zip (col k1) (col k2))) == 2 && same_dk_cond m' (fi,k1) (fi,k2)) candis
    good_rpairs = filter (\[k1,k2] -> length (filter (\(a,b) -> res2 a == res2 b) (zip (row k1) (row k2))) == 2 && same_dk_cond m' (k1,fi') (k2,fi')) candis'
    ret = if b
      then good_cpairs
      else good_rpairs
    ret' = case ret of
      (h:t) -> Just (h!!0,h!!1)
      [] -> Nothing    

find_1234_1324 :: Bool -> SO6 ZRootTwo -> [Int] -> [Int] -> ((Int, Int),(Int, Int))
find_1234_1324 b m rs cs = ret
  where
    col x = map (\j -> matrix_index m j x) rs
    ccs = ([0..5]\\cs)
    drow = filter (\j -> res2 (matrix_index m j (ccs!!0)) == (Even, Odd) && res2 (matrix_index m j (ccs!!1)) == (Even, Odd)) rs
    krow = rs \\ drow
    dkrow = if b then drow else krow
    ret' = unJust $ find (\[k1,k2] -> res2 (matrix_index m (dkrow!!0) k1) == res2 (matrix_index m (dkrow!!0) k2) && res2 (matrix_index m (dkrow!!1) k1) == res2 (matrix_index m (dkrow!!1) k2)) $ choosek 2 cs
    ret2 = cs \\ ret'
    ret = ((ret' !! 0 , ret' !! 1), (ret2 !! 0, ret2 !! 1))


find_1234_1324b :: Bool -> SO6 ZRootTwo -> [Int] -> [Int] -> (Int, Int)
find_1234_1324b b m rs cs = ret
  where
    col x = map (\j -> matrix_index m j x) rs
    ccs = ([0..5]\\cs)
    drow = filter (\j -> res2 (matrix_index m j (ccs!!0)) == (Even, Odd) && res2 (matrix_index m j (ccs!!1)) == (Even, Odd)) rs
    ret = (drow !! 0, drow !! 1)

find_1324 :: Bool -> SO6 DRootTwo -> [Int] -> [Int] -> ((Int, Int),(Int, Int))
find_1324 b m' rs cs = ret
  where
    (m,lde) = denomexp_decompose m'
    row x = map (\k -> matrix_index m x k) cs
    candis = choosek 2 cs
    good_cpairs = filter (\[k1,k2] -> equal_res m (rs!!0, k1) (rs!!0,k2)) candis
    ret' = case good_cpairs of
      [] -> error $ "find_1324 " ++ show b
      (h:t) -> h
    ret2 = cs \\ ret'
    ret = ((ret' !! 0 , ret' !! 1), (ret2 !! 0, ret2 !! 1))


find_4 :: Bool -> SO6 DRootTwo -> [Int] -> [Int] -> ((Int, Int),(Int, Int))
find_4 b m' rs cs = ret
  where
    (m,lde) = denomexp_decompose m'
    row x = map (\k -> matrix_index m x k) cs
    candis = choosek 2 rs
    good_cpairs = filter (\[k1,k2] -> length (filter (\(a,b) -> res2 a == res2 b && (res2 a == (Odd,Even) || res2 a == (Odd,Odd))) (zip (row k1) (row k2))) == 4) candis
    ret' = case good_cpairs of
      [] -> error "find_4"
      (h:t) -> h
    ret2 = cs \\ ret'
    ret = ((ret' !! 0 , ret' !! 1), (ret2 !! 0, ret2 !! 1))


-- decrease in the lexicographical order of (lde, N_lde, # reducible pair of rows (columns)).
decrease_step_opt :: (SO6 DRootTwo) -> ([(Int,Int)],[(Int,Int)])
decrease_step_opt xm
  | denomexp xm == 0 = ([],[])
  | otherwise = case ck of
    1 -> ([],[(jc,kc)])
    2 -> if length r1 == 4
      then ([],[(jc,kc)])
      else ([(jr,kr)], [])
    3 -> case find_case3_2x2_block xm' (r1,c1) of
      Just (rs2,cs2) -> let (rs2', cs2') = (r1\\rs2, c1\\cs2) in case equal_res xm' (rs2'!!0, cs2!!0) (rs2'!!0, cs2!!1) of
        True -> ([],[(cs2!!0, cs2!!1)])
        False -> case equal_res xm' (rs2'!!0, cs2'!!0) (rs2'!!1, cs2'!!0) of
            True -> ([(rs2'!!0,rs2'!!1)], [])
            False -> let (j, k) = find_v5jk True xm r1 c1 in ([],[(j, k)])
      Nothing -> case (find_121324 False xm r1 c1, find_121324 True xm r1 c1) of
        (_, Just (jr, kr)) -> ([],[(jr, kr)])
        (Just (jr, kr), _) -> ([(jr, kr)], [])
        (_,_) -> case res2 (matrix_index xm' (head $ [0..5]\\r1) (head $ [0..5]\\c1)) == (Even,Even) of
--          True -> let ((j1,k1), (j2,k2)) = find_1234_1324 True xm' r1 c1 in ([],[(j1,k1),(j2,k2)])
          True -> let (j1,k1) = find_1234_1324b True xm' r1 c1 in ([(j1,k1)], [])
          False -> let ((j1,k1), (j2,k2)) = find_1234_1324 False xm' r1 c1 in ([],[(j1,k1),(j2,k2)])
    4 -> let ccs = c1 \\ c2 in ([],[(ccs!!0,ccs!!1)])
    5 -> ([],[(c2!!0,c2!!1)])
    6 -> if length r1 == 6
      then ([],[(c2!!0,c2!!1)])
      else ([(r2!!0,r2!!1)], [])
    7 -> ([], [(c1!!0, c1!!1)])
    8 -> if equal_res xm' (r1!!0, c3!!0) (r1!!0, c3!!1)
      then ([], [(c1!!0, c1!!1),(c2!!0, c2!!1),(c3!!0, c3!!1)])
      else if equal_res xm' (r1!!0, c3!!0) (r1!!1, c3!!0)
      then ([(r1!!0, r1!!1),(r2!!0, r2!!1),(r3!!0, r3!!1)], [])
      else let (m13,m24) = find_1324 True xm (r1) (c3++c2) in
        --  let (m13',m24') = find_4 True (xm * so6ofii [m13,m24]) (r3++r2) (c3++c2) in
        -- ([m13',m24'],[m13,m24])

        let (m13b,m24b) = find_1324 True xm (r3) (c1++c2) in
        let (m13c,m24c) = find_1324 True xm (r2) (c1++c3) in
        let (m13',m24') = find_4 True (xm * so6ofii [m13,m24]) (r3++r2) (c3++c2) in
        let (m13'b,m24'b) = find_4 True (xm * so6ofii [m13b,m24b]) (r1++r2) (c1++c2) in
        let (m13'c,m24'c) = find_4 True (xm * so6ofii [m13c,m24c]) (r1++r3) (c1++c3) in
        let Case cka _ _ _ = pattern_of (so6ofii [m13',m24'] * xm * so6ofii [m13,m24]) in
        let Case ckb _ _ _ = pattern_of (so6ofii [m13'b,m24'b] * xm * so6ofii [m13b,m24b]) in
        let Case ckc _ _ _ = pattern_of (so6ofii [m13'c,m24'c] * xm * so6ofii [m13c,m24c]) in
          if ckb == 2 || ckb == 5
          then ([m13'b,m24'b],[m13b,m24b])
          else if ckc == 2 || ckc == 5 then ([m13'c,m24'c],[m13c,m24c])
          else if cka == 2 || cka == 5 then ([m13',m24'],[m13,m24])
          else
            error "cannot reduce to case 5 or 2."

  where
    Case ck (r1,c1) (r2,c2) (r3,c3) = pattern_of xm
    [jc,kc,lc,mc] = map (\x -> c1!!x) [0..3]
    [jr,kr,lr,mr] = map (\x -> r1!!x) [0..3]
    (xm', lde) = denomexp_decompose xm


-- decrease in the lexicographical order of (lde, N_lde, # reducible pair of rows (columns)).
decrease_step :: (SO6 DRootTwo) -> ([(Int,Int)],[(Int,Int)])
decrease_step xm
  | denomexp xm == 0 = ([],[])
  | otherwise = case ck of
    1 -> ([],[(jc,kc)])
    2 -> if length r1 == 4
      then ([],[(jc,kc)])
      else ([(jr,kr)], [])
    3 -> case find_case3_2x2_block xm' (r1,c1) of
      Just (rs2,cs2) -> let (rs2', cs2') = (r1\\rs2, c1\\cs2) in case equal_res xm' (rs2'!!0, cs2!!0) (rs2'!!0, cs2!!1) of
        True -> ([],[(cs2!!0, cs2!!1)])
        False -> case equal_res xm' (rs2'!!0, cs2'!!0) (rs2'!!1, cs2'!!0) of
            True -> ([(rs2'!!0,rs2'!!1)], [])
            False -> let (j, k) = find_v5jk True xm r1 c1 in ([],[(j, k)])
      Nothing -> case (find_121324 False xm r1 c1, find_121324 True xm r1 c1) of
        (_, Just (jr, kr)) -> ([],[(jr, kr)])
        (Just (jr, kr), _) -> ([(jr, kr)], [])
        (_,_) -> case res2 (matrix_index xm' (head $ [0..5]\\r1) (head $ [0..5]\\c1)) == (Even,Even) of
          True -> let ((j1,k1), (j2,k2)) = find_1234_1324 True xm' r1 c1 in ([],[(j1,k1),(j2,k2)])
          False -> let ((j1,k1), (j2,k2)) = find_1234_1324 False xm' r1 c1 in ([],[(j1,k1),(j2,k2)])
    4 -> let ccs = c1 \\ c2 in ([],[(ccs!!0,ccs!!1)])
    5 -> ([],[(c2!!0,c2!!1)])
    6 -> if length r1 == 6
      then ([],[(c2!!0,c2!!1)])
      else ([(r2!!0,r2!!1)], [])
    7 -> ([], [(c1!!0, c1!!1)])
    8 -> if equal_res xm' (r1!!0, c3!!0) (r1!!0, c3!!1)
      then ([], [(c1!!0, c1!!1),(c2!!0, c2!!1),(c3!!0, c3!!1)])
      else if equal_res xm' (r1!!0, c3!!0) (r1!!1, c3!!0)
      then ([(r1!!0, r1!!1),(r2!!0, r2!!1),(r3!!0, r3!!1)], [])
      else let (m13,m24) = find_1324 True xm (r1) (c3++c2) in
        let (m13',m24') = find_4 True (xm * so6ofii [m13,m24]) (r3++r2) (c3++c2) in
        ([m13',m24'],[m13,m24])

  where
    Case ck (r1,c1) (r2,c2) (r3,c3) = pattern_of xm
    [jc,kc,lc,mc] = map (\x -> c1!!x) [0..3]
    [jr,kr,lr,mr] = map (\x -> r1!!x) [0..3]
    (xm', lde) = denomexp_decompose xm


so6ofii lm = product $ map (\(a, b) -> mpq a b) lm
  
decrease :: Int -> (SO6 DRootTwo) -> ([(Int,Int)],[(Int,Int)])
decrease 0 xm = ([],[])
decrease n xm = (lm' ++ lm , rm ++ rm')
  where
    (lm, rm) = decrease_step xm
    lmm = so6ofii lm
    rmm = so6ofii rm
    xm' = lmm * xm * rmm
    (lm', rm') = if denomexp xm' == 0 then ([],[]) else decrease (n-1) xm'

decrease1 :: Int -> (SO6 DRootTwo) -> ([(Int,Int)],[(Int,Int)])
decrease1 0 xm = ([],[])
decrease1 n xm = (lm' ++ lm , rm ++ rm')
  where
    (lm, rm) = decrease_step xm
    lmm = so6ofii lm
    rmm = so6ofii rm
    xm' = lmm * xm * rmm
    (lm', rm') = if denomexp xm' == denomexp xm - 1 then ([],[]) else decrease1 (n-1) xm'

decrease_opt :: Int -> (SO6 DRootTwo) -> ([(Int,Int)],[(Int,Int)])
decrease_opt 0 xm = ([],[])
decrease_opt n xm = (lm' ++ lm , rm ++ rm')
  where
    (lm, rm) = decrease_step_opt xm
    lmm = so6ofii lm
    rmm = so6ofii rm
    xm' = lmm * xm * rmm
    (lm', rm') = if denomexp xm' == 0 then ([],[]) else decrease_opt (n-1) xm'

decrease_opt1 :: Int -> (SO6 DRootTwo) -> ([(Int,Int)],[(Int,Int)])
decrease_opt1 0 xm = ([],[])
decrease_opt1 n xm = (lm' ++ lm , rm ++ rm')
  where
    (lm, rm) = decrease_step_opt xm
    lmm = so6ofii lm
    rmm = so6ofii rm
    xm' = lmm * xm * rmm
    (lm', rm') = if denomexp xm' == denomexp xm - 1 then ([],[]) else decrease_opt1 (n-1) xm'


synth_so6 :: (SO6 DRootTwo) -> ([CliffordT2],([(Int,Int)],[(Int,Int)]))
synth_so6 xm = if lde == 0 then (cli0 , ([],[])) else (cli, (lm' ++ lm, rm ++ rm'))
  where
    (mm, lde) = denomexp_decompose xm
    cli0 = case find (\x -> let x' = so6of x in x' == xm || x' == -xm ) clifford_nf2_reduced of
      Just c -> c
      Nothing -> error "cannot find clifford"
      
    (lm, rm) = decrease_step xm
    lmm = so6ofii lm
    rmm = so6ofii rm
    xm' = lmm * xm * rmm
    
    (cli, (lm', rm')) = if lde == 0 then (cli0, ([],[])) else synth_so6 xm'


synth_so6_t :: (SO6 DRootTwo) -> ([CliffordT2],([(Int,Int)],[(Int,Int)]))
synth_so6_t xm = if lde == 0 then ([] , ([],[])) else ([], (lm' ++ lm, rm ++ rm'))
  where
    (mm, lde) = denomexp_decompose xm
      
    (lm, rm) = decrease_step xm
    lmm = so6ofii lm
    rmm = so6ofii rm
    xm' = lmm * xm * rmm
    
    (cli, (lm', rm')) = if lde == 0 then ([], ([],[])) else synth_so6_t xm'


synth_so6_t_opt :: (SO6 DRootTwo) -> ([CliffordT2],([(Int,Int)],[(Int,Int)]))
synth_so6_t_opt xm = if lde == 0 then ([] , ([],[])) else ([], (lm' ++ lm, rm ++ rm'))
  where
    (mm, lde) = denomexp_decompose xm
      
    (lm, rm) = decrease_step_opt xm
    lmm = so6ofii lm
    rmm = so6ofii rm
    xm' = lmm * xm * rmm
    
    (cli, (lm', rm')) = if lde == 0 then ([], ([],[])) else synth_so6_t_opt xm'


synth_so6_opt :: (SO6 DRootTwo) -> ([CliffordT2],([(Int,Int)],[(Int,Int)]))
synth_so6_opt xm = if lde == 0 then (cli0 , ([],[])) else (cli, (lm' ++ lm, rm ++ rm'))
  where
    (mm, lde) = denomexp_decompose xm
    cli0 = case find (\x -> let x' = so6of x in x' == xm || x' == -xm ) clifford_nf2_reduced of
      Just c -> c
      Nothing -> error "cannot find clifford"
      
    (lm, rm) = decrease_step_opt xm
    lmm = so6ofii lm
    rmm = so6ofii rm
    xm' = lmm * xm * rmm
    
    (cli, (lm', rm')) = if lde == 0 then (cli0, ([],[])) else synth_so6_opt xm'

eq_upto_gp_so6 :: SO6 DRootTwo -> SO6 DRootTwo -> Bool
eq_upto_gp_so6 a b = a == b || -a == b

eq_upto_gp :: U4 DOmega -> U4 DOmega -> Bool
eq_upto_gp a b = any (a == ) [omega ^ k `scalarmult` b | k <- [0..7]]

to_clinf_gate :: CliffordT2 -> [Syl.Gate]
to_clinf_gate S0 = [Syl.S0]
to_clinf_gate S1 = [Syl.S1]
to_clinf_gate Z0 = [Syl.S0,Syl.S0]
to_clinf_gate Z1 = [Syl.S1,Syl.S1]
to_clinf_gate H0 = [Syl.H0]
to_clinf_gate H1 = [Syl.H1]
to_clinf_gate X0 = [Syl.H0,Syl.S0,Syl.S0,Syl.H0]
to_clinf_gate X1 = [Syl.H1,Syl.S1,Syl.S1,Syl.H1]
to_clinf_gate CZ = [Syl.ZZ]
to_clinf_gate CX = [Syl.H1,Syl.ZZ,Syl.H1]
to_clinf_gate XC = [Syl.H0,Syl.ZZ,Syl.H0]
to_clinf_gate WI = [Syl.Omega 1]
to_clinf_gate Ex = [Syl.ZZ,Syl.H0,Syl.H1,Syl.ZZ,Syl.H0,Syl.H1,Syl.ZZ,Syl.H0,Syl.H1]

to_clinf :: [CliffordT2] -> [Syl.Gate]
to_clinf = Syl.repeatedly Syl.peephole_clifford . concat . map to_clinf_gate 

eq_upto_gp_nf :: [CliffordT2] -> [CliffordT2] -> Bool
eq_upto_gp_nf a b = any (\x -> to_clinf a == to_clinf x) [b ++ replicate k WI | k <- [0..7]]

synth_u4 :: [CliffordT2] -> [CliffordT2]
synth_u4 xs = simp $ l' ++ cli ++ r'
  where
    m = so6of xs
    (cli, (l,r)) = synth_so6 m
    l' = inv_cir $ concat $ map cir_of_pq l
    r' = inv_cir $ concat $ map cir_of_pq r

synth_u4_opt :: [CliffordT2] -> [CliffordT2]
synth_u4_opt xs = simp $ l' ++ cli ++ r'
  where
    m = so6of xs
    (cli, (l,r)) = synth_so6_opt m
    l' = inv_cir $ concat $ map cir_of_pq l
    r' = inv_cir $ concat $ map cir_of_pq r

synth_u4' :: SO6 DRootTwo -> [CliffordT2]
synth_u4' m = simp $ l' ++ cli ++ r'
  where
    (cli, (l,r)) = synth_so6 m
    l' = inv_cir $ concat $ map cir_of_pq l
    r' = inv_cir $ concat $ map cir_of_pq r

cir_of_rot :: [(Int, Int)] -> [CliffordT2]
cir_of_rot = concat . map cir_of_pq

cir_of_pq :: (Int, Int) -> [CliffordT2]
cir_of_pq (j,k)
  | j == 3 && k == 4 = [T1]
  | j == 4 && k == 3 = [X1,T1,X1]
  | otherwise = c ++ [T0] ++ inv_cir c
  where
    c = conjugator $ unrot j k

prop_synth_so6 :: [CliffordT2] -> Bool
prop_synth_so6 xs = eq_upto_gp_so6 (so6of xs) (so6of (synth_u4 xs))

prop_synth_so6b :: [CliffordT2] -> Bool
prop_synth_so6b xs = eq_upto_gp_so6 (so6of xs) (so6of (synth_u4_opt xs))

prop_synth_u4 :: [CliffordT2] -> Bool
prop_synth_u4 xs = eq_upto_gp (su4of xs) (su4of (synth_u4 xs))

prop_synth_u4b :: [CliffordT2] -> Bool
prop_synth_u4b xs = eq_upto_gp (su4of xs) (su4of (synth_u4_opt xs))


decreaseIO :: Int -> (SO6 DRootTwo) -> IO ([(Int,Int)],[(Int,Int)])
decreaseIO 0 xm = return ([],[])
decreaseIO n xm = do
  let (lm, rm) = decrease_step xm
  let lmm = so6ofii lm
  let rmm = so6ofii rm
  let xm' = lmm * xm * rmm
  let lde = denomexp xm'
  let pa = pattern_of xm
  print $ ((lde, pa), (lm, rm))
  let (xm2 , lde2) = denomexp_decompose xm
  pm $ matrix_map res3 xm2
  (lm', rm') <- if lde == 0 then return ([],[]) else decreaseIO (n-1) xm'
  return (lm' ++ lm , rm ++ rm')

transp :: Int -> Int -> SO6 DRootTwo
transp j k
  | j == k = 1
  | j < k = twolevel_matrix (0,1) (1,0) j k
  | j > k = twolevel_matrix (0,1) (1,0) k j

upto_swap_transpose :: SO6 DRootTwo -> SO6 DRootTwo
upto_swap_transpose m = ret
  where
    pa = pattern_of m
    ret = case pa of
      Case 1 (r1, c1) (r2,c2) (r3,c3) -> transp 1 (r1!!1) * transp 0 (r1!!0) * m * transp 0 (c1!!0) * transp 1 (c1!!1)
      Case 2 (r1, c1) (r2,c2) (r3,c3) -> 
        if length r1 == 4
        then transp 3 (r1!!3) * transp 2 (r1!!2) * transp 1 (r1!!1) * transp 0 (r1!!0) * m * transp 0 (c1!!0) * transp 1 (c1!!1)
        else transp 1 (r1!!1) * transp 0 (r1!!0) * m * transp 0 (c1!!0) * transp 1 (c1!!1) * transp 2 (c1!!2) * transp 3 (c1!!3)
      Case 3 (r1, c1) (r2,c2) (r3,c3) -> 
        transp 3 (r1!!3) * transp 2 (r1!!2) * transp 1 (r1!!1) * transp 0 (r1!!0) * m * transp 0 (c1!!0) * transp 1 (c1!!1) * transp 2 (c1!!2) * transp 3 (c1!!3)
      Case 4 (r1, c1) (r2,c2) (r3,c3) -> let r1' = r1\\r2 in let c1' = c1\\c2 in
        transp 1 (r1'!!1) * transp 0 (r1'!!0) * m * transp 0 (c1'!!0) * transp 1 (c1'!!1)
      Case 5 (r1s, c1s) (r1,c1) (r2,c2) -> 
        transp 1 (r1!!1) * transp 0 (r1!!0) * m * transp 0 (c1!!0) * transp 1 (c1!!1)
      Case 6 (r1, c1) (r2,c2) (r3,c3) -> let r1' = r1\\r2 in let c1' = c1\\(c2++c3) in
        if length c1 == 6
        then transp 3 (r1!!3) * transp 2 (r1!!2) * transp 1 (r1!!1) * transp 0 (r1!!0) * m
        else m * transp 0 (c1!!0) * transp 1 (c1!!1) * transp 2 (c1!!2) * transp 3 (c1!!3)
      Case 7 (r1, c1) (r2,c2) (r3,c3) -> 
        transp 3 (r2!!1) * transp 2 (r2!!0) * transp 1 (r1!!1) * transp 0 (r1!!0) * m * transp 0 (c1!!0) * transp 1 (c1!!1) * transp 2 (c2!!0) * transp 3 (c2!!1) 
      Case 8 (r1, c1) (r2,c2) (r3,c3) -> 
        transp 3 (r2!!1) * transp 2 (r2!!0) * transp 1 (r1!!1) * transp 0 (r1!!0) * m * transp 2 (c2!!0) * transp 3 (c2!!1) * transp 4 (c1!!0) * transp 5 (c1!!1)
    
dect :: Int -> (SO6 DRootTwo) -> IO (Integer, Integer)
dect k m = do
  let (m',l1) = denomexp_decompose m
  let (ll,rr) = decrease k m
  let l2 = (denomexp (so6ofii ll * m * so6ofii rr))
  print l2
  return (l1,l2)
    
main' = do
  m <- generate (arbitrary :: Gen (SO6 DRootTwo))
  let (mo,lde) = denomexp_decompose $ m
  if lde > 0 then do
    let (m',lde) = denomexp_decompose $ upto_swap_transpose m
    print "old:"
    print m
    print $ pattern_of m
    pm $ matrix_map res1 mo
    print "new:"
    pm $ matrix_map res1 m' else do print "lde = 0"

  
{-
 res3 x | res3 x^2
((0,0,0),(0,0,0))
((0,0,1),(0,0,0))
((0,1,0),(0,0,1))
((0,1,1),(0,0,1))
((1,0,0),(1,0,0))
((1,0,1),(1,0,0))
((1,1,0),(1,0,1))
((1,1,1),(1,0,1))

res2 x | res2 x^2
((0,0),(0,0))
((0,1),(0,0))
((1,0),(1,0))
((1,1),(1,0))
-}

{-
Let r = roottwo, and k be the lde of the matrix:

case 3, k = 3.

[r,1,r,-1,1,1]
[-r,1,r,1,1,-1]
[r,-1,r,1,-1,-1]
[r,1,-r,1,1,-1]
[0,-2,0,0,2,0]
[0,0,0,2,0,2]


case 4, r = roottwo, k = 3.

[ r, 1, 1, 1,-r,-1]
[ 0, 2,-1, 1, r, 0]
[ 0, 0, 1,-1, r,-2]
[-r, 1,-1,-1,-r,-1]
[-2, 0, r, r, 0, 0]
[ 0, r, r,-r, 0, r]

-}


-- ----------------------------------------------------------------------
-- ** Conjugators

-- The action of the Clifford group on Pauli operators is
-- transitive. Specifically, for every 2-qubit Pauli operator P ≠ ±I,
-- there exists some Clifford operator C such that
--
-- C(Z⊗I)C⁻¹ == P.
--
-- For each P, we choose a particular such C and call it the
-- conjugator of P.

-- Definition: conjugators for the unsigned Pauli operators.
conjugator_unsigned :: (Pauli,Pauli) -> [CliffordT2]
conjugator_unsigned (I,X) = [H1, Ex]
conjugator_unsigned (I,Y) = [S1, H1, Ex]
conjugator_unsigned (I,Z) = [Ex]
conjugator_unsigned (X,I) = [H0]
conjugator_unsigned (X,X) = [H1, CZ, H0]
conjugator_unsigned (X,Y) = [S1, H1, CZ, H0]
conjugator_unsigned (X,Z) = [CZ, H0]
conjugator_unsigned (Y,I) = [S0, H0]
conjugator_unsigned (Y,X) = [H1, S0, CZ, H0]
conjugator_unsigned (Y,Y) = [S1, H1, S0, CZ, H0]
conjugator_unsigned (Y,Z) = [S0, CZ, H0]
conjugator_unsigned (Z,I) = []
conjugator_unsigned (Z,X) = [H1, H0, CZ, H0]
conjugator_unsigned (Z,Y) = [S1, H1, H0, CZ, H0]
conjugator_unsigned (Z,Z) = [H0, CZ, H0]

type Pauli2 = (Pauli, Pauli)
-- Definition: conjugators for signed Pauli operators.
conjugator :: SignedPauli2 -> [CliffordT2]
conjugator (True , p,q) = conjugator_unsigned (p,q)
conjugator (False , p,q) = conjugator_unsigned (p,q) ++ [X0]

inv_gate :: CliffordT2 -> [CliffordT2]
inv_gate Z0 = [Z0]
inv_gate Z1 = [Z1]
inv_gate S0 = [Z0,S0]
inv_gate S1 = [Z1,S1]
inv_gate H0 = [H0]
inv_gate H1 = [H1]
inv_gate X0 = [X0]
inv_gate X1 = [X1]
inv_gate T0 = [Z0,S0,T0]
inv_gate T1 = [Z1,S1,T1]
inv_gate CS = [CZ,CS]
inv_gate CZ = [CZ]
inv_gate WI = replicate 7 WI
inv_gate Ex = [Ex]

inv_gate CX = [CX]
inv_gate XC = [XC]

inv_cir :: [CliffordT2] -> [CliffordT2]
inv_cir = concat . map inv_gate . reverse


peephole :: [CliffordT2] -> Maybe [CliffordT2]
peephole (CZ:CZ:t) = Just t
peephole (Z0:Z0:t) = Just t
peephole (Z1:Z1:t) = Just t
peephole (H1:H0:H1:t) = Just (H0:t)
peephole (H1:Z0:S0:H1:t) = Just (Z0:S0:t)
peephole (H1:S0:H0:H1:t) = Just (S0:H0:t)
peephole (H1:Z0:H1:t) = Just (Z0:t)
peephole (H1:H0:S0:H1:t) = Just (H0:S0:t)
peephole (H1:S0:H1:t) = Just (S0:t)
peephole (H0:H1:H0:t) = Just (H1:t)
peephole (H0:Z1:H0:t) = Just (Z1:t)
peephole (H0:S1:H0:t) = Just (S1:t)
peephole (H0:H1:S1:H0:t) = Just (H1:S1:t)
peephole (H0:X1:H1:H0:t) = Just (X1:H1:t)
peephole (H0:Z1:S1:H0:t) = Just (Z1:S1:t)
peephole (H0:H0:t) = Just t
peephole (H1:H1:t) = Just t
peephole (S0:S0:t) = Just (Z0:t)
peephole (S1:S1:t) = Just (Z1:t)
peephole (H0:S0:S0:H0:t) = Just (X0:t)
peephole (H1:S1:S1:H1:t) = Just (X1:t)
peephole (CZ:H1:H0:CZ:t) = Just (Ex:H1:H0:CZ:H0:H1:t)
peephole (H1:Ex:t) = Just (Ex:H0:t)
peephole (H0:Ex:t) = Just (Ex:H1:t)
peephole (X1:Ex:t) = Just (Ex:X0:t)
peephole (X0:Ex:t) = Just (Ex:X1:t)
peephole (Z1:Ex:t) = Just (Ex:Z0:t)
peephole (Z0:Ex:t) = Just (Ex:Z1:t)
peephole (S1:Ex:t) = Just (Ex:S0:t)
peephole (S0:Ex:t) = Just (Ex:S1:t)
peephole (Ex:Ex:t) = Just t
peephole (CZ:Ex:t) = Just (Ex:CZ:t)
peephole (S0:CZ:t) = Just (CZ:S0:t)
peephole (S1:CZ:t) = Just (CZ:S1:t)
peephole (Z0:CZ:t) = Just (CZ:Z0:t)
peephole (Z1:CZ:t) = Just (CZ:Z1:t)

peephole (Z1:S1:t) = Just (S1:Z1:t)
peephole (Z0:S0:t) = Just (S0:Z0:t)
peephole (Z1:S0:t) = Just (S0:Z1:t)
peephole (Z0:S1:t) = Just (S1:Z0:t)
peephole (Z1:T1:t) = Just (T1:Z1:t)
peephole (Z0:T0:t) = Just (T0:Z0:t)
peephole (Z1:T0:t) = Just (T0:Z1:t)
peephole (Z0:T1:t) = Just (T1:Z0:t)
peephole (S1:T1:t) = Just (T1:S1:t)
peephole (S0:T0:t) = Just (T0:S0:t)
peephole (S1:T0:t) = Just (T0:S1:t)
peephole (S0:T1:t) = Just (T1:S0:t)

peephole (T1:T0:t) = Just (T0:T1:t)
peephole (S1:S0:t) = Just (S0:S1:t)
peephole (Z1:Z0:t) = Just (Z0:Z1:t)
peephole (h:t) = do
  t' <- peephole t
  return (h:t')

peephole [] = Nothing

repeatedly :: (a -> Maybe a) -> a -> a
repeatedly f a = case f a of
  Just a -> repeatedly f a
  Nothing -> a


simp :: [CliffordT2] -> [CliffordT2]
simp = repeatedly peephole

prop_simp :: [CliffordT2] -> Bool
prop_simp xs = eq_upto_gp (su4of xs) (su4of $ simp xs)

cosetEnumA1' :: (Eq a, Show a) => ([a] -> [a] -> Bool) -> [[a]] -> ([[a]], [a]) -> IO ([[a]], [[a]])
cosetEnumA1' m gs (cs, d) = do 
  let gs' = map (++ d) gs
  let gs'' = filter (\x -> find (m x) cs == Nothing) gs'
  let gs''' = nubBy m gs''
  let cs' = cs ++ gs'''
  return (cs', gs''')

cosetEnumA' :: (Eq a, Show a) => ([a] -> [a] -> Bool) -> [[a]] -> ([[a]], [[a]]) -> IO ([[a]], [[a]])
cosetEnumA' m gs (cs, []) = return (cs, [])
cosetEnumA' m gs (cs, (h:t)) = do
  rh <- cosetEnumA1' m gs (cs, h)
  print cs
  print $ (length cs, length (t ++ snd rh))
  cosetEnumA' m gs (fst rh, t ++ snd rh)

int_part (RootTwo a b) = a

{-
precomputed_mat_cli :: () -> [([[Integer]], [CliffordT2])]
precomputed_mat_cli _ = map (\x -> (map (map int_part) (rows_of_matrix (fst (denomexp_decompose (so6of x)))), x)) clifford_nf2_reduced

precomputed_mat_cliQ :: () -> Q Exp
precomputed_mat_cliQ = lift . precomputed_mat_cli

-}
