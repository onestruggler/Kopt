{-# LANGUAGE BangPatterns #-}

-- | Optimal exact synthesis for two-qubit Clifford+CS operators.
--
-- Reference: A. N. Glaudell, N. J. Ross, J. M. Taylor,
-- "Optimal Two-Qubit Circuits for Universal Fault-Tolerant Quantum
-- Computation" (npj Quantum Information 7, 103, 2021; arXiv:2001.05997).
--
-- The algorithm exploits the exceptional isomorphism SU(4) = Spin(6) to
-- map 4x4 unitaries to 6x6 orthogonal matrices over Z/sqrt(2)^k.
--
-- This module provides:
--   * Exact arithmetic over Z[omega], omega = e^{i*pi/4}
--   * 4x4 matrix representation of Clifford+CS gates
--   * The SU(4) -> SO(6) isomorphism via the wedge product (Section 3)
--   * Optimal CS-count synthesis via FFP pattern matching (Section 4)

module CliffordCS where

import Data.List (foldl', intercalate, sort, sortBy, groupBy, find)
import Data.Ord (comparing)
import Data.Maybe (fromJust, isJust)
import qualified Data.Map.Strict as Map

----------------------------------------------------------------------
-- 1.  Ring Z[omega], omega = e^{i*pi/4}, omega^4 = -1, omega^8 = 1
----------------------------------------------------------------------

-- | a + b*omega + c*omega^2 + d*omega^3
-- where omega^2 = i, omega^4 = -1
data ZOmega = ZO !Integer !Integer !Integer !Integer
  deriving (Eq, Ord)

instance Show ZOmega where
  show (ZO a 0 0 0) = show a
  show (ZO a b c d) = "(" ++ show a ++ "+" ++ show b ++ "w+"
                          ++ show c ++ "i+" ++ show d ++ "w3)"

instance Num ZOmega where
  (ZO a b c d) + (ZO e f g h) = ZO (a+e) (b+f) (c+g) (d+h)
  -- omega^4 = -1 used in multiplication
  (ZO a b c d) * (ZO e f g h) =
    ZO (a*e - b*h - c*g - d*f)
       (a*f + b*e - c*h - d*g)
       (a*g + b*f + c*e - d*h)
       (a*h + b*g + c*f + d*e)
  negate (ZO a b c d) = ZO (-a) (-b) (-c) (-d)
  fromInteger n       = ZO n 0 0 0
  abs    = error "ZOmega: abs"
  signum = error "ZOmega: signum"

zo0, zo1, zoi, zow :: ZOmega
zo0 = ZO 0 0 0 0
zo1 = ZO 1 0 0 0
zoi = ZO 0 0 1 0      -- i = omega^2
zow = ZO 0 1 0 0      -- omega

-- | Complex conjugate: omega -> omega^7 = -omega^3, i -> -i
conjZO :: ZOmega -> ZOmega
conjZO (ZO a b c d) = ZO a (-d) (-c) (-b)

-- | Powers of omega
omegaPow :: Int -> ZOmega
omegaPow n = case n `mod` 8 of
  0 -> ZO 1 0 0 0;     1 -> ZO 0 1 0 0
  2 -> ZO 0 0 1 0;     3 -> ZO 0 0 0 1
  4 -> ZO (-1) 0 0 0;  5 -> ZO 0 (-1) 0 0
  6 -> ZO 0 0 (-1) 0;  _ -> ZO 0 0 0 (-1)

-- | Divide by sqrt(2) = omega - omega^3 in Z[omega].
-- Returns Nothing if not divisible.
divSqrt2 :: ZOmega -> Maybe ZOmega
divSqrt2 (ZO a b c d)
  | even (a+c) && even (b+d) =
      Just $ ZO ((b-d)`div`2) ((a+c)`div`2)
                ((b+d)`div`2) ((c-a)`div`2)
  | otherwise = Nothing

-- | Is this a real integer (b=c=d=0)?
isRealInt :: ZOmega -> Bool
isRealInt (ZO _ 0 0 0) = True
isRealInt _             = False

-- | Is this a real number in Z[sqrt(2)]?
-- A Z[omega] element a + b*omega + c*i + d*omega^3 is real iff
-- conjugate = self, i.e., c=0 and b=-d.
-- Then the value is a + b*(omega - omega^3) = a + b*sqrt(2).
isReal :: ZOmega -> Bool
isReal (ZO _ b 0 d) = b == negate d
isReal _             = False

-- | Extract real integer part (assumes isRealInt).
realPart :: ZOmega -> Integer
realPart (ZO a _ _ _) = a

----------------------------------------------------------------------
-- 2.  4x4 matrices over Z[omega] / sqrt(2)^k
----------------------------------------------------------------------

-- | 4x4 matrix: 16 ZOmega entries (row-major) / sqrt(2)^k
data Mat4 = Mat4 { m4K :: !Int, m4E :: [ZOmega] }
  deriving (Show)

-- | Simplify: divide all entries by sqrt(2) while possible.
simplify4 :: Mat4 -> Mat4
simplify4 (Mat4 k e) =
  case mapM divSqrt2 e of
    Just e' -> simplify4 (Mat4 (k-1) e')
    Nothing -> Mat4 k e

mkMat4 :: Int -> [[ZOmega]] -> Mat4
mkMat4 k rows = simplify4 $ Mat4 k (concat rows)

-- | Access entry (i,j), 0-indexed.
m4at :: Mat4 -> Int -> Int -> ZOmega
m4at (Mat4 _ e) i j = e !! (i*4+j)

-- | 4x4 identity.
mat4Id :: Mat4
mat4Id = Mat4 0 [if i==j then zo1 else zo0 | i<-[0..3], j<-[0..3]]

-- | 4x4 matrix multiplication.
mat4Mul :: Mat4 -> Mat4 -> Mat4
mat4Mul (Mat4 k1 a) (Mat4 k2 b) = simplify4 $ Mat4 (k1+k2) entries
  where
    entries = [ sum [ a!!(i*4+l) * b!!(l*4+j) | l<-[0..3] ]
              | i<-[0..3], j<-[0..3] ]

-- | Kronecker (tensor) product of two 2x2 matrices stored as [a,b,c,d].
-- Result is 4x4.
kron2x2 :: Int -> [ZOmega] -> Int -> [ZOmega] -> Mat4
kron2x2 k1 [a11,a12,a21,a22] k2 [b11,b12,b21,b22] =
  simplify4 $ Mat4 (k1+k2)
    [ a11*b11, a11*b12, a12*b11, a12*b12
    , a11*b21, a11*b22, a12*b21, a12*b22
    , a21*b11, a21*b12, a22*b11, a22*b12
    , a21*b21, a21*b22, a22*b21, a22*b22 ]
kron2x2 _ _ _ _ = error "kron2x2: need exactly 4 entries each"

----------------------------------------------------------------------
-- 3.  Standard 4x4 gate matrices
----------------------------------------------------------------------

-- | 2x2 identity entries
id2 :: [ZOmega]
id2 = [zo1, zo0, zo0, zo1]

-- | H = (1/sqrt2) [[1,1],[1,-1]]
hGate2x2 :: (Int, [ZOmega])
hGate2x2 = (1, [zo1, zo1, zo1, negate zo1])

-- | S = [[1,0],[0,i]]
sGate2x2 :: (Int, [ZOmega])
sGate2x2 = (0, [zo1, zo0, zo0, zoi])

-- | 4x4 gates
gateHI, gateIH, gateSI, gateIS, gateCZ, gateCS :: Mat4

gateHI = kron2x2 1 [zo1,zo1,zo1,negate zo1] 0 id2
gateIH = kron2x2 0 id2 1 [zo1,zo1,zo1,negate zo1]
gateSI = kron2x2 0 [zo1,zo0,zo0,zoi] 0 id2
gateIS = kron2x2 0 id2 0 [zo1,zo0,zo0,zoi]

-- CZ = diag(1,1,1,-1)
gateCZ = Mat4 0 [ zo1,zo0,zo0,zo0
                , zo0,zo1,zo0,zo0
                , zo0,zo0,zo1,zo0
                , zo0,zo0,zo0,negate zo1 ]

-- CS = diag(1,1,1,i)
gateCS = Mat4 0 [ zo1,zo0,zo0,zo0
                , zo0,zo1,zo0,zo0
                , zo0,zo0,zo1,zo0
                , zo0,zo0,zo0,zoi ]

-- | Evaluate a circuit to a 4x4 matrix.
data Gate2 = H1 | H2 | S1g | S2g | CZg | CSg
  deriving (Eq, Show)

gateMat4 :: Gate2 -> Mat4
gateMat4 H1  = gateHI
gateMat4 H2  = gateIH
gateMat4 S1g = gateSI
gateMat4 S2g = gateIS
gateMat4 CZg = gateCZ
gateMat4 CSg = gateCS

type Circuit2 = [Gate2]

evalCircuit4 :: Circuit2 -> Mat4
evalCircuit4 = foldl' (\acc g -> mat4Mul acc (gateMat4 g)) mat4Id

----------------------------------------------------------------------
-- 4.  SU(4) -> SO(6) isomorphism via wedge product
--     (Section 3 of the paper, Definition 3.4)
----------------------------------------------------------------------

-- The 6 index pairs for the standard basis of /\^2 C^4:
-- (0,1), (0,2), (0,3), (1,2), (1,3), (2,3)
wedgePairs :: [(Int,Int)]
wedgePairs = [(0,1),(0,2),(0,3),(1,2),(1,3),(2,3)]

-- | Compound (second exterior power) matrix: /\^2(U).
-- Entry at (pair p, pair q) = U_{i1,j1}*U_{i2,j2} - U_{i1,j2}*U_{i2,j1}
-- where pair p = (i1,i2) and pair q = (j1,j2).
-- Result has denominator exponent 2*k.
compoundMatrix :: Mat4 -> (Int, [ZOmega])  -- (k, 36 entries row-major)
compoundMatrix (Mat4 k e) = (2*k, entries)
  where
    u i j = e !! (i*4+j)
    entries = [ u i1 j1 * u i2 j2 - u i1 j2 * u i2 j1
              | (i1,i2) <- wedgePairs
              , (j1,j2) <- wedgePairs ]

-- | The matrix P*sqrt(2), whose columns are sqrt(2) * B_j
-- in the standard wedge-product basis (e_{01}, e_{02}, ..., e_{23}).
--
-- From the paper's basis B (Equation 9-10):
--   B_0 = s_{-,12,34} = (i/sqrt2)(e1^e2 - e3^e4)
--   B_1 = s_{+,12,34} = (1/sqrt2)(e1^e2 + e3^e4)
--   B_2 = s_{-,23,14} = (i/sqrt2)(e2^e3 - e1^e4)
--   B_3 = s_{+,24,13} = (1/sqrt2)(e2^e4 + e1^e3)
--   B_4 = s_{-,24,13} = (i/sqrt2)(e2^e4 - e1^e3)
--   B_5 = s_{+,23,14} = (1/sqrt2)(e2^e3 + e1^e4)
--
-- Columns of P*sqrt(2) (B_j * sqrt(2) in standard basis):
--         B0    B1    B2    B3    B4    B5
-- e01: [  i,    1,    0,    0,    0,    0  ]
-- e02: [  0,    0,    0,    1,   -i,    0  ]
-- e03: [  0,    0,   -i,    0,    0,    1  ]
-- e12: [  0,    0,    i,    0,    0,    1  ]
-- e13: [  0,    0,    0,    1,    i,    0  ]
-- e23: [ -i,    1,    0,    0,    0,    0  ]
-- | Corrected basis change matrix P*sqrt(2), 6x6 row-major.
-- Columns are the basis vectors B_j * sqrt(2) from Equations 9-10,
-- with columns 3,4 swapped and phase-corrected to ensure P†Λ²(U)P
-- gives real SO(6) entries for ALL generators (including I⊗iH).
pSqrt2 :: [ZOmega]  -- 6x6 row-major
pSqrt2 =
  [  zoi,  zo1,  zo0,       zo0,        zo0,  zo0
  ,  zo0,  zo0,  zo0,  negate zo1,  zoi,      zo0
  ,  zo0,  zo0,  negate zoi, zo0,       zo0,  zo1
  ,  zo0,  zo0,  zoi,       zo0,        zo0,  zo1
  ,  zo0,  zo0,  zo0,       zo1,        zoi,  zo0
  ,  negate zoi,  zo1,  zo0, zo0,       zo0,  zo0
  ]

-- | (P*sqrt(2))^dagger = conjugate transpose of pSqrt2.
-- Row j of P†*sqrt(2) = conjugate of column j of P*sqrt(2).
-- The isomorphism uses the Hermitian inner product: Ū = P† Λ²(U) P.
pSqrt2Dag :: [ZOmega]  -- 6x6 row-major
pSqrt2Dag =
  [ negate zoi, zo0, zo0,        zo0,       zo0,        zoi          -- conj col 0
  , zo1,        zo0, zo0,        zo0,       zo0,        zo1          -- conj col 1
  , zo0,        zo0, zoi,        negate zoi, zo0,       zo0          -- conj col 2
  , zo0,   negate zo1, zo0,      zo0,       zo1,        zo0          -- conj col 3
  , zo0,   negate zoi, zo0,      zo0,       negate zoi, zo0          -- conj col 4
  , zo0,        zo0, zo1,        zo1,       zo0,        zo0          -- conj col 5
  ]

-- | 6x6 matrix multiply (ZOmega entries).
matMul6Z :: [ZOmega] -> [ZOmega] -> [ZOmega]
matMul6Z a b =
  [ sum [ a!!(i*6+l) * b!!(l*6+j) | l<-[0..5] ]
  | i<-[0..5], j<-[0..5] ]

-- | Convert a 4x4 Clifford+CS matrix (Mat4) to a 6x6 SO(6) matrix (Mat6).
--
-- Uses the isomorphism from Section 3 of the paper (Definition 3.4):
--   Ū = P† · Λ²(U) · P
--
-- where P has columns B_j (the corrected wedge-product basis) and
-- P† is its conjugate transpose. Since P is unitary, P†P = I.
--
-- For U not in SU(4), we search for a phase ω^{2j} (j=0..3) such that
-- ω^{2j} · P†Λ²(U)P is real. This corresponds to normalizing U → ω^j·U
-- to have det=1.
--
-- Algorithm:
--   1. Compute compound matrix Λ²(U) in the standard wedge basis
--   2. Change to basis B:  tmp = P†·sqrt2 * Λ²(U) * P·sqrt2
--   3. Try phases ω^{2j} for j=0..3 to make entries real
--   4. Reduce sqrt(2) factors and extract integer entries
su4ToSO6 :: Mat4 -> Either String Mat6
su4ToSO6 m4 =
  let (ck, cEntries) = compoundMatrix m4

      -- Step 2: basis change using conjugate transpose
      tmp     = matMul6Z pSqrt2Dag (matMul6Z cEntries pSqrt2)
      denomK  = ck + 2   -- from the two sqrt(2) factors in P

      -- Step 3: try phase factors ω^j for j=0..7
      -- Λ²(ω^j U) = ω^{2j} Λ²(U), but we also need to handle
      -- matrices not in SU(4) (e.g. CS with det=i), where the
      -- compound matrix entries may be proportional to odd powers of ω.
      zo_w  = ZO 0 1 0 0   -- ω
      zo_w3 = ZO 0 0 0 1   -- ω³
      zo_w5 = ZO 0 (-1) 0 0 -- ω⁵ = -ω
      zo_w7 = ZO 0 0 0 (-1) -- ω⁷ = -ω³
      phases  = [zo1, zo_w, zoi, zo_w3, negate zo1, zo_w5, negate zoi, zo_w7]
      tryPhase ph = map (ph *) tmp

      -- Step 4: for each phase, check if entries become real and reducible
      go k es
        | all isRealInt es =
            let ints = map (fromIntegral . realPart) es
            in Right (simplify6 (Mat6 k ints))
        | all isReal es =
            case mapM divSqrt2 es of
              Just es' -> go (k-1) es'
              Nothing  -> Left "su4ToSO6: entries not reducible to integers"
        | otherwise = Left $ "su4ToSO6: non-real entries after basis change"

      results = [ go denomK (tryPhase ph) | ph <- phases ]
      successes = [ r | r@(Right _) <- results ]

  in case successes of
       (r:_) -> r
       []    -> Left $ "su4ToSO6: no phase makes entries real"

----------------------------------------------------------------------
-- 5.  6x6 integer matrices with sqrt(2)^k denominator
----------------------------------------------------------------------

-- | Mat6 represents M / sqrt(2)^k where M is a 6x6 integer matrix.
data Mat6 = Mat6 { mat6K :: !Int, mat6E :: ![Int] }
  deriving (Show)

instance Eq Mat6 where
  (Mat6 k1 e1) == (Mat6 k2 e2) = k1 == k2 && e1 == e2

(!) :: Mat6 -> (Int,Int) -> Int
(Mat6 _ e) ! (i,j) = e !! (i*6+j)

mat6Id :: Mat6
mat6Id = Mat6 0 [if i==j then 1 else 0 | i<-[0..5], j<-[0..5]]

negateMat6 :: Mat6 -> Mat6
negateMat6 (Mat6 k e) = Mat6 k (map negate e)

simplify6 :: Mat6 -> Mat6
simplify6 (Mat6 k e)
  | k >= 2 && all even e = simplify6 (Mat6 (k-2) (map (`div` 2) e))
  | otherwise = Mat6 k e

matMul6 :: Mat6 -> Mat6 -> Mat6
matMul6 (Mat6 k1 a) (Mat6 k2 b) = simplify6 $ Mat6 (k1+k2) entries
  where
    entries = [ sum [a !! (i*6+l) * b !! (l*6+j) | l <- [0..5]]
              | i <- [0..5], j <- [0..5] ]

matTr6 :: Mat6 -> Mat6
matTr6 (Mat6 k e) = Mat6 k [e !! (j*6+i) | i<-[0..5], j<-[0..5]]

lde :: Mat6 -> Int
lde = mat6K

----------------------------------------------------------------------
-- 6.  The 15 S-gates in SO(6) (from Figure 2 of the paper)
----------------------------------------------------------------------

mkMat6 :: Int -> [[Int]] -> Mat6
mkMat6 k rows = simplify6 $ Mat6 k (concat rows)

s1, s2, s3, s4, s5, s6, s7, s8, s9 :: Mat6
s10, s11, s12, s13, s14, s15 :: Mat6

s1 = mkMat6 1
  [[ 1, 0, 0,-1, 0, 0],[ 0, 1,-1, 0, 0, 0],[ 0, 1, 1, 0, 0, 0],
   [ 1, 0, 0, 1, 0, 0],[ 0, 0, 0, 0, 1,-1],[ 0, 0, 0, 0, 1, 1]]
s2 = mkMat6 1
  [[ 1, 0, 1, 0, 0, 0],[ 0, 1, 0, 0,-1, 0],[-1, 0, 1, 0, 0, 0],
   [ 0, 0, 0, 1, 0, 1],[ 0, 1, 0, 0, 1, 0],[ 0, 0, 0,-1, 0, 1]]
s3 = mkMat6 1
  [[ 1,-1, 0, 0, 0, 0],[ 1, 1, 0, 0, 0, 0],[ 0, 0, 1, 0, 0,-1],
   [ 0, 0, 0, 1,-1, 0],[ 0, 0, 0, 1, 1, 0],[ 0, 0, 1, 0, 0, 1]]
s4 = mkMat6 1
  [[ 1, 0, 1, 0, 0, 0],[ 0, 1, 0, 0, 0,-1],[-1, 0, 1, 0, 0, 0],
   [ 0, 0, 0, 1,-1, 0],[ 0, 0, 0, 1, 1, 0],[ 0, 1, 0, 0, 0, 1]]
s5 = mkMat6 1
  [[ 1,-1, 0, 0, 0, 0],[ 1, 1, 0, 0, 0, 0],[ 0, 0, 1, 0,-1, 0],
   [ 0, 0, 0, 1, 0, 1],[ 0, 0, 1, 0, 1, 0],[ 0, 0, 0,-1, 0, 1]]
s6 = mkMat6 1
  [[ 1,-1, 0, 0, 0, 0],[ 1, 1, 0, 0, 0, 0],[ 0, 0, 1,-1, 0, 0],
   [ 0, 0, 1, 1, 0, 0],[ 0, 0, 0, 0, 1,-1],[ 0, 0, 0, 0, 1, 1]]
s7 = mkMat6 1
  [[ 1, 0, 0, 0, 0,-1],[ 0, 1,-1, 0, 0, 0],[ 0, 1, 1, 0, 0, 0],
   [ 0, 0, 0, 1,-1, 0],[ 0, 0, 0, 1, 1, 0],[ 1, 0, 0, 0, 0, 1]]
s8 = mkMat6 1
  [[ 1, 0, 0, 0,-1, 0],[ 0, 1,-1, 0, 0, 0],[ 0, 1, 1, 0, 0, 0],
   [ 0, 0, 0, 1, 0, 1],[ 1, 0, 0, 0, 1, 0],[ 0, 0, 0,-1, 0, 1]]
s9 = mkMat6 1
  [[ 1, 0, 1, 0, 0, 0],[ 0, 1, 0,-1, 0, 0],[-1, 0, 1, 0, 0, 0],
   [ 0, 1, 0, 1, 0, 0],[ 0, 0, 0, 0, 1,-1],[ 0, 0, 0, 0, 1, 1]]
s10 = mkMat6 1
  [[ 1, 0, 0, 1, 0, 0],[ 0, 1, 0, 0, 1, 0],[ 0, 0, 1, 0, 0, 1],
   [-1, 0, 0, 1, 0, 0],[ 0,-1, 0, 0, 1, 0],[ 0, 0,-1, 0, 0, 1]]
s11 = mkMat6 1
  [[ 1, 0, 0,1, 0, 0],[ 0, 1, 0, 0, 0, -1],[ 0, 0, 1, 0, 1, 0],
   [ -1, 0, 0, 1, 0, 0],[ 0, 0,-1, 0, 1, 0],[ 0,1, 0, 0, 0, 1]]
-- as in paper, but there is some mismatch.
s11' = mkMat6 1
  [[ 1, 0, 0,-1, 0, 0],[ 0, 1, 0, 0, 0, 1],[ 0, 0, 1, 0, 1, 0],
   [ 1, 0, 0, 1, 0, 0],[ 0, 0,-1, 0, 1, 0],[ 0,-1, 0, 0, 0, 1]]
s12 = mkMat6 1
  [[ 1, 0, 0, 0, 0, 1],[ 0, 1, 0, 0,-1, 0],[ 0, 0, 1, 1, 0, 0],
   [ 0, 0,-1, 1, 0, 0],[ 0, 1, 0, 0, 1, 0],[-1, 0, 0, 0, 0, 1]]
s13 = mkMat6 1
  [[ 1, 0, 0, 0,-1, 0],[ 0, 1, 0, 1, 0, 0],[ 0, 0, 1, 0, 0, 1],
   [ 0,-1, 0, 1, 0, 0],[ 1, 0, 0, 0, 1, 0],[ 0, 0,-1, 0, 0, 1]]
  
s14 = mkMat6 1
  [[ 1, 0, 0, 0, -1, 0],[ 0, 1, 0, 0, 0, -1],[ 0, 0, 1, 1, 0, 0],
   [ 0, 0,-1, 1, 0, 0],[1, 0, 0, 0, 1, 0],[ 0,1, 0, 0, 0, 1]]
-- as in paper, but there is some mismatch.
s14' = mkMat6 1
  [[ 1, 0, 0, 0, 1, 0],[ 0, 1, 0, 0, 0, 1],[ 0, 0, 1, 1, 0, 0],
   [ 0, 0,-1, 1, 0, 0],[-1, 0, 0, 0, 1, 0],[ 0,-1, 0, 0, 0, 1]]
  
s15 = mkMat6 1
  [[ 1, 0, 0, 0, 0, 1],[ 0, 1, 0, -1, 0, 0],[ 0, 0, 1, 0, -1, 0],
   [ 0,1, 0, 1, 0, 0],[ 0, 0,1, 0, 1, 0],[-1, 0, 0, 0, 0, 1]]
-- as in paper, but there is some mismatch.
s15' = mkMat6 1
  [[ 1, 0, 0, 0, 0, 1],[ 0, 1, 0, 1, 0, 0],[ 0, 0, 1, 0, 1, 0],
   [ 0,-1, 0, 1, 0, 0],[ 0, 0,-1, 0, 1, 0],[-1, 0, 0, 0, 0, 1]]

sGates :: [Mat6]
sGates = [s1,s2,s3,s4,s5,s6,s7,s8,s9,s10,s11,s12,s13,s14,s15]

sGateNames :: [String]
sGateNames =
  [ "R(XI,IX)", "R(YI,IY)", "R(ZI,IZ)"
  , "R(YI,IZ)", "R(ZI,IY)", "R(ZI,IX)"
  , "R(XI,IZ)", "R(XI,IY)", "R(YI,IX)"
  , "R(XX,YY)", "R(XX,ZY)", "R(ZX,YY)"
  , "R(YX,XY)", "R(ZX,XY)", "R(YX,ZY)" ]

----------------------------------------------------------------------
-- 7.  Clifford generators in SO(6) (for circuit-level evaluation)
----------------------------------------------------------------------

genSI, genIS, genHI, genIH, genCZ :: Mat6

genSI = mkMat6 0
  [[ 0,-1, 0, 0, 0, 0],[ 1, 0, 0, 0, 0, 0],[ 0, 0, 1, 0, 0, 0],
   [ 0, 0, 0, 1, 0, 0],[ 0, 0, 0, 0, 1, 0],[ 0, 0, 0, 0, 0, 1]]
genIS = mkMat6 0
  [[ 1, 0, 0, 0, 0, 0],[ 0, 1, 0, 0, 0, 0],[ 0, 0, 1, 0, 0, 0],
   [ 0, 0, 0, 0,-1, 0],[ 0, 0, 0, 1, 0, 0],[ 0, 0, 0, 0, 0, 1]]
genHI = mkMat6 0
  [[ 0, 0, 1, 0, 0, 0],[ 0,-1, 0, 0, 0, 0],[ 1, 0, 0, 0, 0, 0],
   [ 0, 0, 0, 1, 0, 0],[ 0, 0, 0, 0, 1, 0],[ 0, 0, 0, 0, 0, 1]]
genIH = mkMat6 0
  [[ 1, 0, 0, 0, 0, 0],[ 0, 1, 0, 0, 0, 0],[ 0, 0, 1, 0, 0, 0],
   [ 0, 0, 0, 0, 0, 1],[ 0, 0, 0, 0,-1, 0],[ 0, 0, 0, 1, 0, 0]]
genCZ = mkMat6 0
  [[ 0,-1, 0, 0, 0, 0],[ 1, 0, 0, 0, 0, 0],[ 0, 0, 0, 0, 0,-1],
   [ 0, 0, 0, 0,-1, 0],[ 0, 0, 0, 1, 0, 0],[ 0, 0, 1, 0, 0, 0]]

gateMat6 :: Gate2 -> Mat6
gateMat6 H1  = genHI
gateMat6 H2  = genIH
gateMat6 S1g = genSI
gateMat6 S2g = genIS
gateMat6 CZg = genCZ
gateMat6 CSg = s3

evalCircuit6 :: Circuit2 -> Mat6
evalCircuit6 = foldl' (\acc g -> matMul6 acc (gateMat6 g)) mat6Id

----------------------------------------------------------------------
-- 8.  Residue, pattern, and FFP table
----------------------------------------------------------------------

residue :: Mat6 -> [[Int]]
residue (Mat6 _ e) =
  [ [ abs (e !! (i*6+j)) `mod` 2 | j <- [0..5] ] | i <- [0..5] ]

type Pattern = [[Int]]

rowPattern :: [[Int]] -> Pattern
rowPattern rows =
  let indexed = zip [0..] rows
      groups  = groupBy (\a b -> snd a == snd b)
              $ sortBy (comparing snd) indexed
  in sort $ map (sort . map fst) groups

ffpTable :: [(Int, [Pattern])]
ffpTable =
  [ (0,  [[[0,3],[1,2],[4,5]], [[0,3],[1,2,4,5]], [[1,2],[0,3,4,5]], [[4,5],[0,1,2,3]]])
  , (1,  [[[0,2],[1,4],[3,5]], [[0,2],[1,3,4,5]], [[1,4],[0,2,3,5]], [[3,5],[0,1,2,4]]])
  , (2,  [[[0,1],[2,5],[3,4]], [[0,1],[2,3,4,5]], [[2,5],[0,1,3,4]], [[3,4],[0,1,2,5]]])
  , (3,  [[[0,2],[1,5],[3,4]], [[1,5],[0,2,3,4]]])
  , (4,  [[[0,1],[2,4],[3,5]], [[2,4],[0,1,3,5]]])
  , (5,  [[[0,1],[2,3],[4,5]], [[2,3],[0,1,4,5]]])
  , (6,  [[[0,5],[1,2],[3,4]], [[0,5],[1,2,3,4]]])
  , (7,  [[[0,4],[1,2],[3,5]], [[0,4],[1,2,3,5]]])
  , (8,  [[[0,2],[1,3],[4,5]], [[1,3],[0,2,4,5]]])
  , (9,  [[[0,3],[1,4],[2,5]]])
  , (10, [[[0,3],[1,5],[2,4]]])
  , (11, [[[0,5],[1,4],[2,3]]])
  , (12, [[[0,4],[1,3],[2,5]]])
  , (13, [[[0,4],[1,5],[2,3]]])
  , (14, [[[0,5],[1,3],[2,4]]])
  ]

lookupFFP :: Pattern -> Maybe Int
lookupFFP pat =
  let normPat p = sort (map sort p)
      matches (_, pats) = normPat pat `elem` map normPat pats
  in fst <$> find matches ffpTable

----------------------------------------------------------------------
-- 9.  Synthesis algorithm (Theorem 4.15)
----------------------------------------------------------------------

data SynthResult = SynthResult
  { srGates    :: [Int]    -- S-gate indices (0..14), outermost first
  , srClifford :: Mat6     -- final Clifford (LDE = 0)
  } deriving (Show)

-- | Synthesize from an SO(6) matrix.
synthesize :: Mat6 -> Either String SynthResult
synthesize v0 = go v0 []
  where
    go !v !acc
      | lde v == 0 = Right (SynthResult (reverse acc) v)
      | otherwise =
          let res = residue v
              pat = rowPattern res
          in case lookupFFP pat of
               Nothing ->
                 Left $ "No FFP match for pattern " ++ show pat
                      ++ " (LDE=" ++ show (lde v) ++ ")"
               Just j ->
                 let sj  = sGates !! j
                     v'  = matMul6 (matTr6 sj) v
                 in go v' (j : acc)

-- | Synthesize from a 4x4 matrix.
synthesizeFromMat4 :: Mat4 -> Either String SynthResult
synthesizeFromMat4 m4 = do
  so6 <- su4ToSO6 m4
  synthesize so6

----------------------------------------------------------------------
-- 10. Pretty printing
----------------------------------------------------------------------

prettyGate2 :: Gate2 -> String
prettyGate2 H1  = "H*I"; prettyGate2 H2  = "I*H"
prettyGate2 S1g = "S*I"; prettyGate2 S2g = "I*S"
prettyGate2 CZg = "CZ";  prettyGate2 CSg = "CS"

prettyCircuit2 :: Circuit2 -> String
prettyCircuit2 [] = "I"
prettyCircuit2 gs = intercalate "." (map prettyGate2 gs)

prettySynth :: SynthResult -> String
prettySynth (SynthResult gs _) =
  let gnames = map (sGateNames !!) gs
  in if null gnames then "Clifford"
     else intercalate " . " gnames ++ " . C"

isOrthogonal :: Mat6 -> Bool
isOrthogonal v =
  let prod = matMul6 (matTr6 v) v
  in mat6K prod == 0 && mat6E prod == mat6E mat6Id

----------------------------------------------------------------------
-- 11. Demo
----------------------------------------------------------------------

main' :: IO ()
main' = do
  putStrLn "============================================================"
  putStrLn "  Glaudell-Ross-Taylor Optimal Clifford+CS Synthesis"
  putStrLn "  with SU(4) -> SO(6) isomorphism"
  putStrLn "============================================================"

  -- 1. Verify SU(4)->SO(6) isomorphism against known SO(6) representations
  putStrLn ""
  putStrLn "--- Verifying SU(4) -> SO(6) isomorphism ---"
  let isoTests :: [(String, Mat4, Mat6)]
      isoTests =
        [ ("H*I",  gateHI,  genHI)
        , ("I*H",  gateIH,  genIH)
        , ("S*I",  gateSI,  genSI)
        , ("I*S",  gateIS,  genIS)
        , ("CZ",   gateCZ,  genCZ)
        , ("CS",   gateCS,  s3)
        ]

  mapM_ (\(name, m4, expected6) -> do
    case su4ToSO6 m4 of
      Left err -> putStrLn $ "  " ++ pad 8 name ++ " ERROR: " ++ err
      Right got6 ->
        let ok = got6 == expected6
            okNeg = got6 == negateMat6 expected6
        in putStrLn $ "  " ++ pad 8 name
                   ++ (if ok || okNeg then " [ok]" else " [MISMATCH]")
                   ++ " LDE=" ++ show (lde got6)
    ) isoTests

  -- Verify isomorphism for products
  putStrLn ""
  putStrLn "--- Verifying isomorphism for composite circuits ---"
  let circTests :: [(String, Circuit2)]
      circTests =
        [ ("CS.H1.CS",         [CSg, H1, CSg])
        , ("H1.CS.H2.CS",      [H1, CSg, H2, CSg])
        , ("CS.H1.CS.H2.CS",   [CSg, H1, CSg, H2, CSg])
        , ("H1.H2.CS.H1.H2",   [H1, H2, CSg, H1, H2])
        , ("(CS)^4",            [CSg, CSg, CSg, CSg])
        , ("S1.H1.CS.H2.CS.S2", [S1g, H1, CSg, H2, CSg, S2g])
        , ("CZ.CS.CZ.CS.CZ",   [CZg, CSg, CZg, CSg, CZg])
        , ("H1.S1.CS.H2.S2.CS.H1.CS",
            [H1, S1g, CSg, H2, S2g, CSg, H1, CSg])
        ]

  mapM_ (\(name, circ) -> do
    let m4   = evalCircuit4 circ
        so6c = evalCircuit6 circ  -- via circuit-level SO(6) evaluation
    case su4ToSO6 m4 of
      Left err -> putStrLn $ "  " ++ pad 28 name ++ " ISO ERROR: " ++ err
      Right so6i ->
        let ok = so6i == so6c
            okNeg = so6i == negateMat6 so6c
        in putStrLn $ "  " ++ pad 28 name
                   ++ (if ok || okNeg then " [ok]" else " [MISMATCH]")
                   ++ " LDE=" ++ show (lde so6i)
    ) circTests

  -- 2. Full synthesis from 4x4 matrices
  putStrLn ""
  putStrLn "--- Optimal synthesis from 4x4 matrices ---"
  putStrLn "------------------------------------------------------------"

  let synthExamples :: [(String, Mat4)]
      synthExamples =
        [ ("CS",          gateCS)
        , ("CZ",          gateCZ)
        , ("CS^2 (=CZ)",  mat4Mul gateCS gateCS)
        , ("H1.CS",       mat4Mul gateHI gateCS)
        , ("CS.H1.CS",    foldl1 mat4Mul [gateCS, gateHI, gateCS])
        , ("H1.CS.H2.CS", foldl1 mat4Mul [gateHI, gateCS, gateIH, gateCS])
        , ("CS.H1.CS.H2.CS",
            foldl1 mat4Mul [gateCS, gateHI, gateCS, gateIH, gateCS])
        , ("H1.H2.CS.H1.H2.CS.H1.H2",
            foldl1 mat4Mul [gateHI,gateIH,gateCS,gateHI,gateIH,gateCS,gateHI,gateIH])
        , ("CS^4 (=I)",
            foldl1 mat4Mul [gateCS,gateCS,gateCS,gateCS])
        , ("S1.H1.CS.H2.CS.S2",
            foldl1 mat4Mul [gateSI,gateHI,gateCS,gateIH,gateCS,gateIS])
        , ("H1.S1.CS.H2.S2.CS.H1.CS",
            foldl1 mat4Mul [gateHI,gateSI,gateCS,gateIH,gateIS,gateCS,gateHI,gateCS])
        -- A matrix entered directly (not via circuit)
        , ("direct: diag(1,1,i,i)",
            Mat4 0 [ zo1,zo0,zo0,zo0
                   , zo0,zo1,zo0,zo0
                   , zo0,zo0,zoi,zo0
                   , zo0,zo0,zo0,zoi ])
        , ("direct: SWAP",
            Mat4 0 [ zo1,zo0,zo0,zo0
                   , zo0,zo0,zo1,zo0
                   , zo0,zo1,zo0,zo0
                   , zo0,zo0,zo0,zo1 ])
        ]

  mapM_ (\(label, m4) -> do
    case synthesizeFromMat4 m4 of
      Left err -> putStrLn $ "  " ++ pad 32 label ++ " ERROR: " ++ err
      Right sr -> do
        let csCount = length (srGates sr)
        -- Verify: reconstruct in SO(6)
        case su4ToSO6 m4 of
          Left _ -> putStrLn $ "  " ++ pad 32 label ++ " (iso failed)"
          Right so6 -> do
            let reconstructed = foldl' (\acc j -> matMul6 (sGates !! j) acc)
                                       (srClifford sr)
                                       (reverse $ srGates sr)
                match = reconstructed == so6
            putStrLn $ "  " ++ pad 32 label
                    ++ " CS=" ++ show csCount
                    ++ "  => " ++ pad 40 (prettySynth sr)
                    ++ (if match then " [ok]" else " [FAIL]")
    ) synthExamples

  putStrLn ""
  putStrLn "------------------------------------------------------------"
  -- Summary
  let allOk = all (\(_, m4) ->
        case synthesizeFromMat4 m4 of
          Left _ -> False
          Right sr -> case su4ToSO6 m4 of
            Left _ -> False
            Right so6 ->
              let recon = foldl' (\acc j -> matMul6 (sGates !! j) acc)
                                 (srClifford sr)
                                 (reverse $ srGates sr)
              in recon == so6
        ) synthExamples
  putStrLn $ if allOk
    then "All " ++ show (length synthExamples) ++ " examples verified."
    else "Some examples FAILED!"

pad :: Int -> String -> String
pad n s = s ++ replicate (max 0 (n - length s)) ' '


conjugator2 :: Int -> Circuit2
conjugator2 0 = [H1,H2]
conjugator2 1 = [S1g, H1,S2g, H2]
conjugator2 2 = []
conjugator2 3 = [S1g, H1]
conjugator2 4 = [S2g, H2]
conjugator2 5 = [H2]
conjugator2 6 = [H1]
conjugator2 7 = [H1,S2g, H2]
conjugator2 8 = [H2,S1g, H1]
conjugator2 9 = [H1,S1g,H1,H2,S2g,CZg, H1,H2]
conjugator2 10 = [H1,S1g,S1g,H1,H2,S2g,CZg, H1,H2]
conjugator2 11 = [S1g,H1,H2,S2g,CZg, H1,H2]
conjugator2 12 = [S1g,H1,S1g,H1,H2,S2g,CZg, H1,H2]
conjugator2 13 = [H1,S1g,H1,S1g,H1,S1g,H1,H2,S2g,CZg, H1,H2]
conjugator2 14 = [H1,S1g,H1,S1g,H1,H2,S2g,CZg, H1,H2]

conjugator2 _ = error "conjugator2: out of bound 0..15."

