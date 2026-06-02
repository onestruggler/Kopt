{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE IncoherentInstances #-}
--{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE TemplateHaskell #-}
module U4Di where
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
type SU2 = Matrix Two Two DComplex
type U4 a = Matrix Four Four a
-- Othognality and Speical Othognality are not checked.
type SO4 = Matrix Four Four DComplex
type O4 a = Matrix Four Four a
type SO6 a = Matrix Six Six a

type U4Di = U4 DComplex

det :: (Nat n, Num a) => Matrix n n a -> a
det = DM.detLaplace . DM.fromLists . rows_of_matrix

m :: U4 DOmega
m = roothalf `scalarmult` matrix_of_rows
  [
    [1,  0,  0,  i],
    [0,  i,  1,  0],
    [0,  i , -1,  0], 
    [1,  0,  0 , -i]
  ]

idm :: U4Di
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

cx' :: U4Di
cx' = matrix_of_rows
  [
    [1,  0,  0,  0],
    [0,  1,  0,  0],
    [0,  0,  0,  -1], 
    [0,  0,  1,  0]
  ]

cx :: U4 DComplex
cx = matrix_of_rows
  [
    [1,  0,  0,  0],
    [0,  1,  0,  0],
    [0,  0,  0,  1], 
    [0,  0,  1,  0]
  ]

gamma :: DComplex
gamma = Cplx 1 1
gamb :: DComplex
gamb = Cplx 1 (-1)
inv_gamma :: DComplex
inv_gamma = gamb * half

ck :: U4 DComplex
ck = inv_gamma `scalarmult` matrix_of_rows
  [
    [gamma,  0,  0,  0],
    [0,  gamma,  0,  0],
    [0,  0,  1,  1], 
    [0,  0,  1,  -1]
  ]

cs :: U4Di
cs = matrix_of_rows
  [
    [1,  0,  0,  0],
    [0,  1,  0,  0],
    [0,  0,  1,  0],
    [0,  0,  0,  i]
  ]

cz :: U4Di
cz = matrix_of_rows
  [
    [1,  0,  0,  0],
    [0,  1,  0,  0],
    [0,  0,  1,  0],
    [0,  0,  0,  -1]
  ]

xx :: U4Di
xx = matrix_of_rows
  [
    [0,  1,  0,  0],
    [1,  0,  0,  0],
    [0,  0,  0,  1], 
    [0,  0,  1,  0]
  ]

zz :: U4Di
zz = matrix_of_rows
  [
    [1,  0,  0,  0],
    [0,  -1,  0,  0],
    [0,  0,  1,  0], 
    [0,  0,  0,  -1]
  ]

zz' :: U4Di
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

h' :: U2 DComplex
h' = let a = Cplx half (-half) in matrix_of_rows [[a,a],[a,-a]]

h :: U2 DOmega
h = let a = roothalf in matrix_of_rows [[a,a],[a,-a]]

m_gate :: U2 DComplex
m_gate = inv_gamma `scalarmult` matrix_of_rows [[1,-i],[-i,1]]


mh :: U2 DRootTwo
mh = let a = roothalf in matrix_of_rows [[a,-a],[a,a]]

t :: U2 DOmega
t = matrix_of_rows [[1,0],[0,omega]]

s :: U2 DComplex
s = matrix_of_rows [[1,0],[0,i]]

z :: U2 DComplex
z = matrix_of_rows [[1,0],[0,-1]]

-- ht :: U2 DOmega
-- ht = h * t

-- sht :: U2 DOmega
-- sht = s * h * t


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
instance Arbitrary U4Di where
  arbitrary = do
    a <- (arbitrary :: Gen SU2)
    b <- (arbitrary :: Gen SU2)
    return (adj m * (a `tensor` b) * m)
-}

instance Arbitrary (U4 DComplex) where
  arbitrary = do
    w1 <- vectorOf 1 (arbitrary :: Gen [CliffordT2])
    return $ u4of $ concat w1


instance WholePart DComplex ZComplex where
  from_whole = fromZComplex
  to_whole (Cplx x y) = Cplx (to_whole x) (to_whole y)


-- ----------------------------------------------------------------------
-- * Common denominators

-- | A type class for things from which a common power of 1\/(1+i) (a
-- least denominator exponent) can be factored out. Typical instances
-- are 'DOmega', 'DRComplex', as well as tuples, lists, vectors, and
-- matrices thereof.
class LamDenomExp a where
  -- | Calculate the least denominator exponent /k/ of /a/. Returns
  -- the smallest /k/≥0 such that /a/ = /b/\/(1+i)[sup /k/] for some
  -- integral /b/.
  lamdenomexp :: a -> Integer

  -- | Factor out a /k/th power of 1\/(1+i) from /a/. In other words,
  -- calculate /a/(1+i)[sup /k/].
  lamdenomexp_factor :: a -> Integer -> a

-- | Calculate and factor out the least denominator exponent /k/ of
-- /a/. Return (/b/,/k/), where /a/ = /b/\/((1+i))[sup /k/] and /k/≥0.
lamdenomexp_decompose :: (WholePart a b, LamDenomExp a) => a -> (b, Integer)
lamdenomexp_decompose a = (b, k) where
  k = lamdenomexp a
  b = to_whole (lamdenomexp_factor a k)

-- | Generic 'show'-like method that factors out a common denominator
-- exponent.
showsPrec_LamDenomExp :: (WholePart a b, Show b, LamDenomExp a) => Int -> a -> ShowS
showsPrec_LamDenomExp d a
  | k == 0 = showsPrec d b
  | k == 1 = showParen (d >= 8) $
             showString "(1+i) * " . showsPrec 7 b
  | otherwise = showParen (d >= 8) $
                showString ("(1+i)^" ++ show k ++ " * ") . showsPrec 7 b
  where (b, k) = lamdenomexp_decompose a

instance LamDenomExp DComplex where
  lamdenomexp (Cplx x y) = k''
    where
      (a,k) = decompose_dyadic x
      (b,l) = decompose_dyadic y
      k' = maximum [k , l]
      km = if even (a * 2^(k' - k) + b * 2^(k' - l)) then 2*k' - 1 else 2*k'
      k'' = if k' > 0 then km else 0
  lamdenomexp_factor a k = a * (from_whole lam)^k


instance (LamDenomExp a, LamDenomExp b) => LamDenomExp (a,b) where
  lamdenomexp (a,b) = lamdenomexp a `max` lamdenomexp b
  lamdenomexp_factor (a,b) k = (lamdenomexp_factor a k, lamdenomexp_factor b k)

instance LamDenomExp () where
  lamdenomexp _ = 0
  lamdenomexp_factor _ k = ()

instance (LamDenomExp a) => LamDenomExp [a] where
  lamdenomexp as = maximum (0 : [ lamdenomexp a | a <- as ])
  lamdenomexp_factor as k = [ lamdenomexp_factor a k | a <- as ]

instance (LamDenomExp a) => LamDenomExp (Cplx a) where
  lamdenomexp (Cplx a b) = lamdenomexp a `max` lamdenomexp b
  lamdenomexp_factor (Cplx a b) k = Cplx (lamdenomexp_factor a k) (lamdenomexp_factor b k)


instance (LamDenomExp a) => LamDenomExp (Vector n a) where
  lamdenomexp as = lamdenomexp (list_of_vector as)
  lamdenomexp_factor as k = vector_map (\a -> lamdenomexp_factor a k) as

instance (LamDenomExp a) => LamDenomExp (Matrix m n a) where
  lamdenomexp (Matrix m) = lamdenomexp m
  lamdenomexp_factor (Matrix m) k = Matrix (lamdenomexp_factor m k)
  
data CliffordT2 =
  S0
  | S1
  | Z0
  | Z1
  | K0
  | K1
  | H0
  | H1
  | X0
  | X1
  | T0
  | T1
  | CS
  | CZ
  | II
  | Ex

  | CX
  | XC
  | CK
  | KC

  deriving (Show, Eq, Ord, Read, Lift)


instance Arbitrary CliffordT2 where
  arbitrary = do
    -- temporarily disallow T
    n <- choose (0,15)
    return $ [S0,S1,K0,K1,CS,CZ,X0,X1,Ex,II,Z0,Z1,CK,KC,CX,XC] !! n
    -- n <- choose (0,13)
    -- return $ [S0,S1,K0,K1,T0,T1,CS,CZ,X0,X1,Ex,II,Z0,Z1] !! n

class U4of a where
  u4of :: a -> U4 DComplex
  eq :: a -> a -> Bool
  eq a b = u4of a == u4of b
  eqm :: a -> a -> Bool
  eqm a b = eq_upto_gp (u4of a) (u4of b)

instance U4of CliffordT2 where
  u4of S0 = s `tensor` id2
  u4of S1 = id2 `tensor` s
  u4of Z0 = z `tensor` id2
  u4of Z1 = id2 `tensor` z
  u4of K0 = h' `tensor` id2
  u4of K1 = id2 `tensor` h'
  -- u4of T0 = t `tensor` id2
  -- u4of T1 = id2 `tensor` t
  u4of CZ = cz
  u4of CS = cs
  u4of Ex = twolevel_matrix (0,1) (1,0) 1 2
  u4of X1 = id2 `tensor` xm
  u4of X0 = xm `tensor` id2
  u4of II = i `scalarmult` 1

  u4of CX = cx
  u4of XC = u4of Ex * cx * u4of Ex
  u4of CK = ck
  u4of KC = u4of Ex * ck * u4of Ex

instance U4of a => U4of [a] where
  u4of [] = 1
  u4of xs@(h:t) = u4of h * u4of t --((*) (u4of (take hf xs))) (u4of (drop hf xs))
    where
      hf = length xs `div` 2


class SO6of a where
  so6of :: a -> (SO6 DRootTwo)

instance SO6of a => SO6of [a] where
  so6of [] = 1
  so6of (h:t) = so6of h * so6of t

instance SO6of CliffordT2 where
  so6of II = -1 `scalarmult` 1
  so6of S0 = twolevel_matrix (0,-1) (1,0) 0 1
  so6of S1 = twolevel_matrix (0,-1) (1,0) 3 4
  so6of K0 = twolevel_matrix (0,1) (1,0) 0 2 * onelevel_matrix (-1) 1
  so6of K1 = twolevel_matrix (0,1) (1,0) 3 5 * onelevel_matrix (-1) 4
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


t_count :: [CliffordT2] -> Int
t_count cir = t_count_t + 3 * t_count_cs
  where
    t_count_t = length $ filter (\x -> x == T1 || x == T0) cir
    t_count_cs = length $ filter (\x -> x == CS) cir



pm :: (Nat n , Show a) => Matrix n n a -> IO ()
pm m = sequence_ $ map print $ rows_of_matrix m

pmd :: (Nat n) => Matrix n n (DComplex) -> IO ()
pmd m = sequence_ $ map print $ rows_of_matrix m'
  where
    (m', k) = lamdenomexp_decompose m


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

-- instance {-# OVERLAPS #-} Show [Z2] where
--   show ([] :: [Z2]) = ""
--   show (h:t) = show h ++ show t

resi1 :: ZComplex -> Z2
resi1 (Cplx a b) = if even (a + b) then Even else Odd

lam :: ZComplex
lam = 1 + i

divLam :: ZComplex -> ZComplex
divLam (Cplx a b) = Cplx ((a+b)`div`2) ((b-a)`div`2)

applyN f n x = iterate f x !! n

res :: Int -> ZComplex -> [Z2]
res 1 x = resi1 x : []
res k x@(Cplx a b) = ih ++ [bn]
  where
    ih = res (k-1) x
    emb :: Z2 -> ZComplex
    emb Odd = 1
    emb Even = 0
    sbi = sum $ zipWith (*) (map emb ih) [(1+i) ^ l | l <- [0..]]
    kgn = (x - sbi)
    kk = applyN divLam (k-1) kgn
    bn = resi1 kk


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

scalar_omega = [S0,K0,S0,K0,S0,K0]
scalar_i = [II]

class ToCliffordT2 a where
  to_ct2 :: a -> CliffordT2


a_box0 = [[],[K0], [K0,S0,K0]]
a_box1 = [[],[K1], [K1,S1,K1]]

b_box = [
  [K1,CZ,K0,K1,CZ,K0,K1,CZ],
  [CZ,K0,K1,CZ],
  [K0,S0,CZ,K0,K1,CZ],
  [K0,CZ,K0,K1,CZ]
  ]

c_box0 = [[], [K0,S0,S0,K0]]  
c_box1 = [[], [K1,S1,S1,K1]]

d_box = [
  [CZ,K0,K1,CZ,K0,K1,CZ,K1],
  [K0,CZ,K0,K1,CZ,K1],
  [K0,K1,S1,CZ,K0,K1,CZ,K1],
  [K0,K1,CZ,K0,K1,CZ,K1]
  ]

e_box0 = [replicate k S0 | k <- [0..3]]
e_box1 = [replicate k S1 | k <- [0..3]]

l_stair2 = [a ++ b ++ c | a <- a_box1, b <- b_box, c <- c_box0] ++ l_stair1
r_stair2 = [d ++ e | d <- d_box, e <- e_box1]

l_stair1 = [a  ++ c | a <- a_box0, c <- c_box0]
r_stair1 = [e | e <- e_box0]

all_scalars = [(replicate k II) | k <- [0..3]]

clifford_nf2 =  map reverse [s ++ l2 ++ r2 ++ l1 ++ r1 | s <- all_scalars, l2 <- l_stair2, r2 <- r_stair2, l1 <- l_stair1, r1 <- r_stair1 ]
clifford_nf2_modscalar =  map reverse [l2 ++ r2 ++ l1 ++ r1 | l2 <- l_stair2, r2 <- r_stair2, l1 <- l_stair1, r1 <- r_stair1 ]
clifford_nf2_reduced = sortBy (\x y -> compare (length x) (length y)) $ map simp clifford_nf2_modscalar

eq_upto_gp :: U4 DComplex -> U4 DComplex -> Bool
eq_upto_gp a b = any (a == ) [i ^ k `scalarmult` b | k <- [0..3]]


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


peephole :: [CliffordT2] -> Maybe [CliffordT2]
peephole (CZ:CZ:t) = Just t
peephole (Z0:Z0:t) = Just t
peephole (Z1:Z1:t) = Just t
peephole (K1:K0:K1:t) = Just (K0:t)
peephole (K1:Z0:S0:K1:t) = Just (Z0:S0:t)
peephole (K1:S0:K0:K1:t) = Just (S0:K0:t)
peephole (K1:Z0:K1:t) = Just (Z0:t)
peephole (K1:K0:S0:K1:t) = Just (K0:S0:t)
peephole (K1:S0:K1:t) = Just (S0:t)
peephole (K0:K1:K0:t) = Just (K1:t)
peephole (K0:Z1:K0:t) = Just (Z1:t)
peephole (K0:S1:K0:t) = Just (S1:t)
peephole (K0:K1:S1:K0:t) = Just (K1:S1:t)
peephole (K0:X1:K1:K0:t) = Just (X1:K1:t)
peephole (K0:Z1:S1:K0:t) = Just (Z1:S1:t)
peephole (K0:K0:t) = Just t
peephole (K1:K1:t) = Just t
peephole (S0:S0:t) = Just (Z0:t)
peephole (S1:S1:t) = Just (Z1:t)
peephole (K0:S0:S0:K0:t) = Just (X0:t)
peephole (K1:S1:S1:K1:t) = Just (X1:t)
peephole (CZ:K1:K0:CZ:t) = Just (Ex:K1:K0:CZ:K0:K1:t)
peephole (K1:Ex:t) = Just (Ex:K0:t)
peephole (K0:Ex:t) = Just (Ex:K1:t)
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
prop_simp xs = eq_upto_gp (u4of xs) (u4of $ simp xs)

unJust (Just a) = a

int_part (RootTwo a b) = a


perm_mat :: [Int] -> U4Di
perm_mat xs = matrix_of_function f
  where
    xys = zip xs [0,1,2,3]
    f x y
      | (x,y) `elem` xys = 1
      | otherwise = 0
    
perm_mats = map perm_mat $ permutations [0,1,2,3]

patof :: U4Di -> U4 Z2
patof m = unJust fd
  where
    candis = map (\m -> let (m',k) = lamdenomexp_decompose m in matrix_map resi1 m')
      [l*m*r | l <- perm_mats, r <- perm_mats]
    candis_t = map matrix_transpose candis
    fd = find (\x -> x `elem` pats) $ candis ++ candis_t

ppz2 x = sequence_ $ map print $ rows_of_matrix $  x

ec = do
  m <- generate $ vectorOf 1000 (arbitrary :: (Gen U4Di))
  let m2 = map (\x -> (x , patof x)) m
  
  -- sequence_ $ map (\(x, y) -> do
  --                     pm $ let (m',k) = lamdenomexp_decompose x in matrix_map resi1 m'
  --                     ppz2 y
  --                 ) m2
  let ps = nub $ map patof m
  print $ length ps
  sequence_ $ map ppz2 $ ps


ec44 = do
  m <- generate $ vectorOf 3000 (arbitrary :: (Gen U4Di))
  let m2 = map (\x -> (x , patof x)) m
  let m3 = nub $ filter (\(x, y) -> y == pats !! 5 && let (m',k) = lamdenomexp_decompose x in k == 4) m2
  let m4 = nub $ map (\(x , y) -> (x, let (m',k) = lamdenomexp_decompose x in k, y)) m3
  
  sequence_ $ map (\(x,k, y) -> do
                      pm x
                      print k
                      ppz2 y
                  ) m4


one22 :: Matrix Two Two Z2
one22 = matrix_of_rows [[Odd, Odd], [Odd, Odd]]

pats :: [U4 Z2]
pats =
  [
    1,
    one22 `oplus` (null_matrix :: Matrix Two Two Z2),
    (one22 `stack_horizontal` one22) `stack_vertical` (null_matrix :: Matrix Two Four Z2),
    (one22 `stack_horizontal` one22) `stack_vertical` (one22 `stack_horizontal` (null_matrix :: Matrix Two Two Z2)),
    one22 `oplus` one22,
    one22 `tensor` one22
    
  ]


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
conjugator_unsigned (I,X) = [K1, Ex]
conjugator_unsigned (I,Y) = [S1, K1, Ex]
conjugator_unsigned (I,Z) = [Ex]
conjugator_unsigned (X,I) = [K0]
conjugator_unsigned (X,X) = [K1, CZ, K0]
conjugator_unsigned (X,Y) = [S1, K1, CZ, K0]
conjugator_unsigned (X,Z) = [CZ, K0]
conjugator_unsigned (Y,I) = [S0, K0]
conjugator_unsigned (Y,X) = [K1, S0, CZ, K0]
conjugator_unsigned (Y,Y) = [S1, K1, S0, CZ, K0]
conjugator_unsigned (Y,Z) = [S0, CZ, K0]
conjugator_unsigned (Z,I) = []
conjugator_unsigned (Z,X) = [K1, K0, CZ, K0]
conjugator_unsigned (Z,Y) = [S1, K1, K0, CZ, K0]
conjugator_unsigned (Z,Z) = [K0, CZ, K0]

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
inv_gate K0 = [K0,II]
inv_gate K1 = [K1,II]
inv_gate H0 = [H0]
inv_gate H1 = [H1]
inv_gate X0 = [X0]
inv_gate X1 = [X1]
inv_gate T0 = [Z0,S0,T0]
inv_gate T1 = [Z1,S1,T1]
inv_gate CS = [CZ,CS]
inv_gate CZ = [CZ]
inv_gate II = replicate 3 II
inv_gate Ex = [Ex]

inv_gate CX = [CX]
inv_gate XC = [XC]

inv_gate CK = [CK,S0]

inv_cir :: [CliffordT2] -> [CliffordT2]
inv_cir = concat . map inv_gate . reverse

