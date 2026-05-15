module Lagarias (typeII, typeIII, qred, qred', red_def, id33,Mat33, Mat22, det33, det22, adjF) where
import Quantum.Synthesis.Matrix
import Quantum.Synthesis.Diophantine 
import Data.Number.FixedPrec
import Quantum.Synthesis.EuclideanDomain

rom = rows_of_matrix

id11 :: Matrix One One Integer
id11 = matrix [[1]]

id22 :: Mat22
id22 = matrix [[1,0],[0,1]]

id33 :: Mat33
id33 = matrix [[1,0,0],[0,1,0],[0,0,1]]



is_square :: Integer -> Bool
is_square n | n < 0 = False
is_square n = b where
  n' = fromIntegral n :: FixedPrec P2000
  b = sqrt n' * sqrt n' == n' 


is_red :: Mat22 -> Bool
is_red m = yn where
  m' = rom m
  d = det22 m
  a11 = m' !! 0 !! 0
  a12 = m' !! 0 !! 1
  a21 = m' !! 1 !! 0
  a22 = m' !! 1 !! 1
  b = fromIntegral a12 :: FixedPrec P2000
  a = fromIntegral a11 :: FixedPrec P2000
  d' = abs $ fromIntegral d :: FixedPrec P2000
  h = ceiling $ sqrt d'
  yn = case is_square d of
    True -> a11 == 0 && a12 == h && a22 >= 0 && a22 <= 2*h -1
    False -> case d < 0 of
      True ->  case a > 0 of
        True -> abs (2*a12) <= a11 && a11 <= a22
        False -> is_red (scalarmult (-1) m)
      False -> b >=0 && b < sqrt d' && abs a < sqrt d'


-- red_deg m = red_deg' (id22, m)
-- -- | matF -> A and F_qred
-- red_deg' :: (Mat22,Mat22) -> (Mat22, Mat22)
-- red_deg' (aA,m) = (aA',mred) where
--   (aA', mred) = if is_red m then (aA, m)
--     else let (aa,ff) = red_deg1 m in red_deg' (aA*aa, ff)

red_deg1 :: Mat22 -> (Mat22, Mat22)
red_deg1 m = (s1*s2,m2) where
  m' = rom m
  d = det22 m
  a11 = m' !! 0 !! 0
  a12 = m' !! 0 !! 1
  a22 = m' !! 1 !! 1
  d' = abs $  fromIntegral d :: FixedPrec P2000
  h = ceiling $ sqrt d'
  (a,b,s,t,dd) = extended_euclid (a12-h) a11
  alpha = -t
  gamma = s
  delta = -a
  beta = b
  s1 = matrix [[alpha,beta],[-gamma,-delta]] :: Mat22
  s1t = (matrix_transpose s1)
  m1 = s1t * m * s1
  m1' = rom m1
  c1 = fromIntegral $ m1' !! 1 !! 1
  lambda = round (-c1/(2*sqrt d'))
  s2 = matrix [[1,lambda],[0,1]] :: Mat22
  s2t = matrix_transpose s2
  m2 = s2t*m1*s2

  
red_def m = red_def' (id22, m)
-- | matF -> A and F_qred
red_def' :: (Mat22,Mat22) -> (Mat22, Mat22)
red_def' (aA,m) = (aA',mred) where
  (aA', mred) = if is_red m then (aA, m)
    else let (aa,ff) = red_def1 m in red_def' (aA*aa, ff)

red_def1 :: Mat22 -> (Mat22, Mat22)
red_def1 m = (sl,mred) where
  m' = rom m
  d = det22 m
  a11 = m' !! 0 !! 0
  a12 = m' !! 0 !! 1
  a21 = m' !! 1 !! 0
  a22 = m' !! 1 !! 1
  c = fromIntegral a22 :: FixedPrec P2000
  b = fromIntegral a12 :: FixedPrec P2000
  d' = fromIntegral d :: FixedPrec P2000
  ml1 = floor $ (-b/c) :: Integer
  ml2 = ceiling $ (-b/c) :: Integer
  lendpt = ((- sqrt d' - b) /c)
  l1 = floor $ lendpt :: Integer
  l2 = ceiling $ lendpt :: Integer
  li = round (-b/c)
  sl = matrix [[0,1],[-1,li]] :: Mat22
  slt = (matrix_transpose sl)
  mred = slt * m * sl



red_indef m = red_indef' (id22, m)
-- | matF -> A and F_qred
red_indef' :: (Mat22,Mat22) -> (Mat22, Mat22)
red_indef' (aA,m) = (aA',mred) where
  (aA', mred) = if is_red m then (aA, m)
    else let (aa,ff) = red_indef1 m in red_indef' (aA*aa, ff)

red_indef1 :: Mat22 -> (Mat22, Mat22)
red_indef1 m = (sl,mred) where
  m' = rom m
  d = det22 m
  a11 = m' !! 0 !! 0
  a12 = m' !! 0 !! 1
  a21 = m' !! 1 !! 0
  a22 = m' !! 1 !! 1
  c = fromIntegral a22 :: FixedPrec P2000
  b = fromIntegral a12 :: FixedPrec P2000
  d' = fromIntegral d :: FixedPrec P2000
  ml1 = floor $ (-b/c) :: Integer
  ml2 = ceiling $ (-b/c) :: Integer
  lendpt = ((- sqrt d' - b) /c)
  l1 = floor $ lendpt :: Integer
  l2 = ceiling $ lendpt :: Integer
  li =  case fromIntegral (abs a22) < 2* sqrt d' of
    True -> case c > 0  of
      True -> if fractional lendpt == 0 then l2+1 else l2
      False -> if fractional lendpt == 0 then l1-1 else l1
    False -> if fromIntegral ml1 < (-b/c + 1/2) && fromIntegral ml1 > (-b/c - 1/2) then ml1 else ml2
  sl = matrix [[0,1],[-1,li]] :: Mat22
  slt = (matrix_transpose sl)
  mred = slt * m * sl


type Mat22 = Matrix Two Two Integer
type Mat33 = Matrix Three Three Integer

-- | determinant defined in Lagarias's paper, it differs by a sign
-- with the standard definition.
det22 :: Mat22 -> Integer
det22 m = -d where
  m' = rows_of_matrix m
  a11 = m' !! 0 !! 0
  a12 = m' !! 0 !! 1
  a21 = m' !! 1 !! 0
  a22 = m' !! 1 !! 1
  d = a11*a22 - a12*a21


-- | determinant defined in Lagarias's paper, it differs by a sign
-- with the standard definition.
det33 :: Mat33 -> Integer
det33 m = -d where
  m' = rows_of_matrix m
  a11 = m' !! 0 !! 0
  a12 = m' !! 0 !! 1
  a13 = m' !! 0 !! 2  
  a21 = m' !! 1 !! 0
  a22 = m' !! 1 !! 1
  a23 = m' !! 1 !! 2  
  a31 = m' !! 2 !! 0
  a32 = m' !! 2 !! 1
  a33 = m' !! 2 !! 2  
  d = a11*a22*a33 + a12*a23*a31 + a13*a21*a32 - a13*a22*a31 -a12*a21*a33 - a11*a23*a32



-- | adjoint of F
adjF :: Mat33 -> Mat33
adjF m = mM where
  m' = rows_of_matrix m
  a11 = m' !! 0 !! 0
  a12 = m' !! 0 !! 1
  a13 = m' !! 0 !! 2  
  a21 = m' !! 1 !! 0
  a22 = m' !! 1 !! 1
  a23 = m' !! 1 !! 2  
  a31 = m' !! 2 !! 0
  a32 = m' !! 2 !! 1
  a33 = m' !! 2 !! 2
  det = (\x -> -x).det22
  d = a11*a22*a33 + a12*a23*a31 + a13*a21*a32 - a13*a22*a31 -a12*a21*a33 - a11*a23*a32
  b11 = det $ matrix [[a22,a23],[a32,a33]]
  b12 = -(det $ matrix [[a21,a23],[a31,a33]])
  b13 = det $ matrix [[a21,a22],[a31,a32]]  
  b21 = -(det $ matrix [[a12,a13],[a32,a33]])
  b22 = det $ matrix [[a11,a13],[a31,a33]]
  b23 = -(det $ matrix [[a11,a12],[a31,a32]])
  b31 = det $ matrix [[a12,a13],[a22,a23]]
  b32 = -(det $ matrix [[a11,a13],[a21,a23]])
  b33 = det $ matrix [[a11,a12],[a21,a22]]
  mM = scalarmult (-1) $ matrix [[b11,b12,b13],[b21,b22,b23],[b31,b32,b33]]



is_qred3 :: Mat33 -> Bool
is_qred3 m = b where
  m' = rows_of_matrix m
  d = abs (fromIntegral $ det33 m) :: FixedPrec P2000
  a11 = m' !! 0 !! 0
  a12 = m' !! 0 !! 1
  a13 = m' !! 0 !! 2  
  a21 = m' !! 1 !! 0
  a22 = m' !! 1 !! 1
  a23 = m' !! 1 !! 2  
  a31 = m' !! 2 !! 0
  a32 = m' !! 2 !! 1
  a33 = m' !! 2 !! 2
  a11' = fromIntegral a11
  a12' = fromIntegral a12  
  b33 = (fromIntegral $ det22(matrix [[a11,a12],[a21,a22]])):: FixedPrec P2000
  b13 = (fromIntegral $ det22(matrix [[a21,a22],[a31,a32]])):: FixedPrec P2000
  b23 = (fromIntegral $ det22(matrix [[a11,a12],[a31,a32]])):: FixedPrec P2000
  b = abs a11' < 2*d**((1/3)::FixedPrec P2000)
    && abs b33 < 2*d**((2/3)::FixedPrec P2000)
    && abs a12' <= 1/2* abs a11'
    && abs b13 <= 1/2 * abs b33
    && abs b23 <= 1/2 * abs b33




typeI :: Mat33 -> (Mat33, Mat33)
typeI m = (s,m1) where
  m' = rows_of_matrix m
  d = det33 m
  a11 = m' !! 0 !! 0
  a12 = m' !! 0 !! 1
  a22 = m' !! 1 !! 1
  (aA,mF) = red_def $ matrix [[a11,a12],[a12,a22]]
  s = aA `oplus` id11
  st = matrix_transpose s
  m1 = st*m*s


typeII :: Mat33 -> (Mat33, Mat33)
typeII m = (s,m1) where
  madj = adjF m
  m' = rows_of_matrix madj
  d = det33 m
  a22 = m' !! 1 !! 1
  a23 = m' !! 1 !! 2
  a33 = m' !! 2 !! 2
  (aA,mF) = red_def $ matrix [[a33,a23],[a23,a22]]
  s' = rows_of_matrix aA
  s11 = s' !! 0 !! 0
  s12 = s' !! 0 !! 1
  s21 = s' !! 1 !! 0
  s22 = s' !! 1 !! 1
  aA' = matrix [[s11, -s12],[-s21,s22]]
  s = id11 `oplus` aA'
  st = matrix_transpose s
  m1 = st*m*s

typeIII :: Mat33 -> (Mat33, Mat33)
typeIII m = (s,m1) where
  madj = adjF m
  s' = rows_of_matrix madj
  m' = rows_of_matrix m
  d = det33 m
  a12 = m' !! 0 !! 1 
  a11 = m' !! 0 !! 0
  r12 = round ((-fromIntegral a12 :: FixedPrec P2000)/ fromIntegral a11)
  s23 = s' !! 1 !! 2
  s33 = s' !! 2 !! 2
  s13 = s' !! 0 !! 2
  r23 = round ((fromIntegral s23 :: FixedPrec P2000)/fromIntegral s33)
  s23' = s23 - s33*r23
  r13 = round (((fromIntegral s13::FixedPrec P2000) - fromIntegral s23'*fromIntegral r12)/fromIntegral s33)
  s = matrix [[1,r12,r13], [0, 1, r23], [0,0,1]]
  st = matrix_transpose s
  m1 = st*m*s

-- qred' :: (Mat33,Mat33) -> (Mat33,Mat33)
-- qred' (aA,m) = (aA',f) where
--   (aA1,m1) = typeI m
--   (aA2,m2) = typeII m1
--   (aA3,m3) = typeIII m2
--   m' = rows_of_matrix m
--   a11 = m' !! 0 !! 0
--   a12 = m' !! 0 !! 1
--   a21 = m' !! 1 !! 0
--   a22 = m' !! 1 !! 1
--   a11' = fromIntegral a11 :: FixedPrec P2000
--   b33 = (fromIntegral $ det22(matrix [[a11,a12],[a21,a22]])):: FixedPrec P2000
--   d = (fromIntegral $ abs (det33 m3))::FixedPrec P2000
--   b = abs a11' < 2*d**((1/3)::FixedPrec P2000)
--     && abs b33 < 2*d**((2/3)::FixedPrec P2000)
--   (aA',f) = if b then (aA, m) else
--     let (aAn,fn) = qred' (aA*aA1*aA2*aA3, m3) in (aAn, fn)

qred' :: (Mat33,Mat33) -> (Mat33,Mat33)
qred' (aA,m) = (aA',f) where
  (aA1,m1) = typeI m
  (aA2,m2) = typeII m1
  (aA3,m3) = typeIII m2
  m' = rows_of_matrix m
  a11 = m' !! 0 !! 0
  a12 = m' !! 0 !! 1
  a21 = m' !! 1 !! 0
  a22 = m' !! 1 !! 1
  a11' = fromIntegral a11 :: FixedPrec P2000
  b33 = abs $ det22(matrix [[a11,a12],[a21,a22]])
  b = abs a11 < 2
    && abs b33 < 2
  (aA',f) = if b then
    let (aAn, fn) = typeIII (m) in (aA*aAn, fn)
    else
    let (aAn,fn) = qred' (aA*aA1*aA2*aA3, m3) in (aAn, fn)

qred :: Mat33 -> (Mat33,Mat33)
qred m = qred' (id33, m)
