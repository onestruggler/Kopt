module Main where

import U4Di hiding (I, II)
import qualified U4Di as UD
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
import Test.QuickCheck


data SixCases = I | II | III | IIIt | IV | V | Vt | VI deriving (Show, Eq, Ord)

case_i :: U4 Z2
case_i = 1

case_ii :: U4 Z2
case_ii = (constant_mat 1 :: U2 Z2 ) `oplus` (0 :: U2 Z2)

case_iii :: U4 Z2
case_iii = (constant_mat 1 :: U2 Z2 ) `oplus` (constant_mat 1 :: U2 Z2)

case_iiit = matrix_transpose case_iii

case_iv :: U4 Z2
case_iv = ((constant_mat 1 :: U2 Z2) `stack_horizontal` (constant_mat 1 :: U2 Z2)) `stack_vertical` ((0 :: U2 Z2) `stack_horizontal` (0 :: U2 Z2))

case_vt :: U4 Z2
case_vt = ((constant_mat 1 :: U2 Z2) `stack_horizontal` (constant_mat 1 :: U2 Z2)) `stack_vertical` ((0 :: U2 Z2) `stack_horizontal` (constant_mat 1 :: U2 Z2))

case_v = matrix_transpose case_vt

case_vi :: U4 Z2
case_vi = ((constant_mat 1 :: U2 Z2) `stack_horizontal` (constant_mat 1 :: U2 Z2)) `stack_vertical` ((constant_mat 1 :: U2 Z2) `stack_horizontal` (constant_mat 1 :: U2 Z2))


case_vi_rho2tr :: U2 [Z2]
case_vi_rho2tr = matrix_of_rows [[[Odd,Even],[Odd,Even]],[[Odd,Odd],[Odd,Odd]]]

case_vi_rho2br :: U2 [Z2]
case_vi_rho2br = matrix_of_rows [[[Odd,Even],[Odd,Odd]],[[Odd,Odd],[Odd,Even]]]

case_vi_rho2br' :: U2 [Z2]
case_vi_rho2br' = matrix_of_rows [[[Odd,Odd],[Odd,Even]],[[Odd,Even],[Odd,Odd]]]

case_vi_rho2 :: U4 [Z2]
case_vi_rho2 = ((constant_mat 1 :: U2 [Z2]) `stack_horizontal` case_vi_rho2tr) `stack_vertical` ((matrix_transpose case_vi_rho2tr) `stack_horizontal` case_vi_rho2br')




pat :: SixCases -> U4 Z2
pat I = case_i
pat II = case_ii
pat III = case_iii
pat IIIt = case_iiit
pat IV = case_iv
pat V = case_v
pat Vt = case_vt
pat VI = case_vi

-- note Vt = V.
six_cases = [I,II,III,IV,V,VI,IIIt]

lde :: U4Di -> Integer
lde = lamdenomexp

rho :: Integer -> Integer -> U4Di -> U4 [Z2]
rho k n m
  | lde m > k = error "lde > k"
  | otherwise = matrix_map (res (fromIntegral n)) m''
  where
    (m' , k') = lamdenomexp_decompose m
    m'' = (lam ^ (k - k')) `scalarmult` m'

rho1 :: Integer -> U4Di -> U4 Z2
rho1 k m = matrix_map head $ rho k 1 m

rhok :: Integer -> U4Di -> U4 [Z2]
rhok n m = rho (lde m) n m
    

type PermCir = [CliffordT2]
type Cir = [CliffordT2]
type DCir = [CliffordT2]
type PDCir = [CliffordT2]

-- Given a matrix m, return its pattern p and also the generalized
-- permutation matrices L and R such that rho (LAR) = p.
lemma_six :: U4Di -> (SixCases, PermCir, PermCir)
lemma_six m
  | lde m == 0 = (I, l0, [])
  | otherwise = (p, x, y)
  where
    (m' , k) = lamdenomexp_decompose m
    l0 = unJust $ find (\x -> rho1 k (u4of x * m) == case_i ) perms
    (x,y,p) = unJust $ find (\(x,y,p) -> rho1 k (u4of x * m * (u4of y)) == pat p ) [(x, y, p) | x <- perms, y <- perms, p <- six_cases]
    r = []

constant_mat :: (Nat a, Num n) => n -> Matrix a a n
constant_mat c = matrix_of_function (\ x y -> c)

test_lemma_six = do
  m <- generate $ vectorOf 1000 (arbitrary :: Gen U4Di)
  let ps = nub$ map (\(p,l,r) -> p) $ map lemma_six m
  print ps

cof :: U4Di -> SixCases
cof m = (\(p,l,r) -> p) $ lemma_six m

im :: [Z2] -> Int -> U4Di
im [Odd,Odd] ix = MS.onelevel_matrix i ix
im _ _ = 1


ims :: Vector Four [Z2] -> U4Di
ims v = product $ map (\(oo, ix) -> im oo ix) xs'
  where
    xs = list_of_vector v
    xs' = zip xs [0..]

dcir :: U4Di -> DCir
dcir m = unJust $ find (\x -> u4of x == m) diag_cirs

decrease1_lde :: U4Di -> (PDCir, PDCir)
decrease1_lde m
  | lde m == 0 = ([],[])
  | otherwise = case cof m of
      I -> error "lde=0"
      III -> (ll, rr)
      IIIt -> (ll3t, rr3t)
      II -> (ll2, rr2)
      IV -> (ll4, rr4)
      V -> (ll5, rr5)
      VI -> (ll6, rr6)
      where
        (m' , k) = lamdenomexp_decompose m
        (p,l,r) = lemma_six m
        m2 = rho k 2 (u4of l * m * u4of r)
        m2r = rows_of_matrix m2
        m2r' = SM.vector (head m2r) :: Vector Four [Z2]
        
        rcir' = ims m2r'
        rcir = dcir rcir'
        m2'3a = m2 * rho 0 2 rcir'
        
        lcir' = im (matrix_index m2'3a 1 0) 1
          * im (matrix_index m2'3a 2 0) 2
          * im (matrix_index m2'3a 3 0) 3
        lcir = dcir lcir'
        
        m2'3 = rho 0 2 lcir' * m2 * rho 0 2 rcir'        
        sp =   if (matrix_index m2'3 2 0 == matrix_index m2'3 2 1) then [K1]
          else if (matrix_index m2'3 2 0 == matrix_index m2'3 2 2) then [K0]
          else if (matrix_index m2'3 2 0 == matrix_index m2'3 2 3) then [CX,K0]
          else error "cannot find sp"
        -- todo: exchange CX and rcir, merge r and CX.
        rr = r ++ rcir ++ sp
        ll = lcir ++ l

        sp3t = if (matrix_index m2'3 0 2 == matrix_index m2'3 1 2) then [K1]
          else if (matrix_index m2'3 0 2 == matrix_index m2'3 2 2) then [K0]
          else if (matrix_index m2'3 0 2 == matrix_index m2'3 3 2) then [K0, CX]
          else error "cannot find sp3t"
        rr3t = r ++ rcir
        ll3t = sp3t ++ lcir ++ l


        sp2r = if k == 1 then [X0,CK,X0] else []
        sp2l = if k == 1 then [] else [K1,S1]
        rr2 = r ++ rcir ++ sp2r
        ll2 = sp2l ++ lcir ++ l

        rcir4' = im (matrix_index m2 0 0) 0
          * im (matrix_index m2 0 1) 1
          * im (matrix_index m2 2 2) 2
          * im (matrix_index m2 2 3) 3
        rcir4 = dcir rcir4'

        m2'4a = m2 * rho 0 2 rcir4'
        
        lcir4 = dcir $ im (matrix_index m2'4a 1 0) 1
          *  im (matrix_index m2'4a 3 2) 3
        
        sp4l = if k == 1 then [K1] else [K1, S1]
        rr4 = r ++ rcir4
        ll4 = sp4l ++ lcir4 ++ l

        rcir5' = im (matrix_index m2 0 0) 0
          * im (matrix_index m2 0 1) 1
          * im (matrix_index m2 2 2) 2
          * im (matrix_index m2 3 3) 3
        rcir5 = dcir rcir5'
        m2' = m2 * rho 0 2 rcir5'
        lcir5 = dcir $ im (matrix_index m2' 1 0) 1
          * im (matrix_index m2' 2 0) 2
          * im (matrix_index m2' 3 0) 3
        
        sp5l = [K1]
        rr5 = r ++ rcir5
        ll5 = sp5l ++ lcir5 ++ l

        rcir6' = im (matrix_index m2 0 0) 0
          * im (matrix_index m2 0 1) 1
          * im (matrix_index m2 0 2) 2
          * im (matrix_index m2 0 3) 3
        rcir6 = dcir rcir6'
        m6r = m2 * rho 0 2 rcir6'
        lcir6' = im (matrix_index m6r 1 0) 1
          * im (matrix_index m6r 2 0) 2
          * im (matrix_index m6r 3 0) 3
        lcir6 = dcir lcir6'
        
        m6lr = rho 0 2 lcir6' * m6r
        
        sp6l = if (matrix_index m6lr 1 1 == [Odd,Even]) then []
          else if (matrix_index m6lr 2 1 == [Odd,Even]) then [Ex]
          else if (matrix_index m6lr 3 1 == [Odd,Even]) then [Ex,CX]
          else error "cannot find sp6"
          
        m6lr' = rho 0 2 (u4of sp6l) * m6lr

        (sp6l' , sp6r) = if (matrix_index m6lr' 1 2 == [Odd,Even]) then ([K1],[]) else
          if (matrix_index m6lr' 2 1 /= [Odd,Even]) then ([K1],[]) else error "vi-3, this case shouldn't happen" -- ([],[K1])
          
        rr6 = r ++ rcir6 ++ sp6r
        ll6 = sp6l' ++ sp6l ++ lcir6 ++ l


synth' :: Int -> U4Di -> ([CliffordT2], [CliffordT2])
synth' j m
  | j <= 0 = ([],[])
synth' ss m
  | lde m == 0 = (inv_cir (unJust $ find (\x -> u4of x == m) gperms), [])
  | otherwise = (li ++ l1, r1 ++ ri)
  where
    (l1,r1) = decrease1_lde m
    m' = u4of l1 * m * u4of r1
    (li, ri) = synth' (ss-1) m'


test_dec1 = do
  m <- generate $ vectorOf 1000 (arbitrary :: Gen U4Di)
  let ps = filter (\x -> let (p,l,r) = lemma_six x in p == V) m
  let lrs = map (\x -> (decrease1_lde x, x)) ps
  let h = head ps
  print $ cof h
  print $ cof (dagger h)
  sequence_ $ map print $ nub $  map (\((ll,rr),x) -> (cof x, cof (u4of ll * x * u4of rr), lde x, lde (u4of ll * x * u4of rr), lde (u4of ll * x * u4of rr) == lde x -1)) lrs


test_dec2 = do
  m <- generate $ vectorOf 2000 (arbitrary :: Gen U4Di)
  let ps = filter (\x -> let (p,l,r) = lemma_six x in p == VI) m
  let lrs = map (\x -> let (l1,r1) = decrease1_lde x in let x' = u4of l1 * x * u4of r1 in let (l2,r2) = decrease1_lde x' in let x'' = u4of l2 * x' * u4of r2  in ((l1,r1), x,x',x'')) ps
  let h = head ps
  sequence_ $ map print $ nub $  map (\((ll,rr),x,x',x'') -> ((ll,rr),cof x, cof x', cof x'', lde x, lde x', lde x'')) lrs



test_syn = do
  m <- generate $ vectorOf 1000 (arbitrary :: Gen U4Di)
  let ps = m -- filter (\x -> let (p,l,r) = lemma_six x in p == IV) m
  let lrs = map (\x -> (synth' (fromIntegral $ lde x * 2+3) x, x)) ps
  sequence_ $ map print $  filter (\(a,b,c,d,e) -> e == True) $ map (\((ll,rr),x) -> (cof x, lde x, lde (u4of ll * x * u4of rr), lde (u4of ll * x * u4of rr) == 0, u4of (inv_cir (ll++rr)) == x)) lrs

kc :: Cir -> Int
kc xs = length $ filter (\x -> x == K0 || x == K1 || x == H1 || x == H0) xs

csc :: Cir -> Int
csc xs = length $ filter (\x -> x == CS) xs


main = test_syn


instance Num [Z2] where
  (+) x y = zipWith (+) x y
  (*) (Odd:Even:[]) y = y
  (*) (Odd:Odd:[]) y = y + rs y
    where
      rs [y1,y2] = [Even, y1]
  (*) (Even:Odd:[]) y = rs y
    where
      rs [y1,y2] = [Even, y1]
  (*) (Even:Even:[]) y = [Even,Even]
    where
      rs [y1,y2] = [Even, y1]

  abs = id
  signum = id
  fromInteger 1 = [Odd,Even]
  fromInteger 0 = [Even,Even]
  fromInteger k = error $ "num [Z2]: " ++ show k
  negate = id

dagger :: U4Di -> U4Di
dagger m = matrix_map adj $ matrix_transpose m 


padd :: (Z2,Z2,Z2) -> (Z2,Z2,Z2) -> (Z2,Z2,Z2)
padd (a,b,c) (e,f,g) = (a+e, b+f , (c + g) + a * e)

pmult :: (Z2,Z2,Z2) -> (Z2,Z2,Z2) -> (Z2,Z2,Z2)
pmult (Even,Even,Even) (e,f,g) = (Even,Even,Even)
pmult (Odd,Even,Even) (e,f,g) = (e,f,g)
pmult (Even,Odd,Even) (e,f,g) = (Even,e,f)
pmult (Even,Even,Odd) (e,f,g) = (Even,Even,e)
pmult (a,b,c) x@(e,f,g) = (pmult (a,Even,Even) x) `padd` ((pmult (Even,b,Even) x) `padd` (pmult (Even,Even,c) x))

instance Num (Z2,Z2,Z2) where
  (+) = padd
  (*) = pmult
  negate = pneg
  fromInteger n = let n' = fromInteger n in let [a,b,c] = residue_m 3 n' in (a,b,c)
  abs x = x
  signum x = 1

inner_product xs ys = sum $ zipWith (*) xs ys

pneg :: (Z2,Z2,Z2) -> (Z2,Z2,Z2)
pneg x = (Odd,Even,Odd) `pmult` x

pfix :: (Z2,Z2,Z2) -> (Z2,Z2,Z2)
pfix (x,y,z) = (x, Odd + y,z)


vi_c1 = [[(Odd,Even,Even), (Odd,Even,Even), (Odd,Even,Even),(Odd,Even,Even) ] ]

vi_c2 = [[(Odd,Even,Even), (Odd,Even,a), (Odd,Odd,b),(Odd,Odd,c) ] | a <- [Even,Odd], b <- [Even,Odd], c <- [Even,Odd] ]


vi_c3 = [[(Odd,Even,Even), (Odd,Odd,a), (Odd,Odd,b),(Odd,Even,c) ] |  a <- [Even,Odd], b <- [Even,Odd], c <- [Even,Odd] ]


vi_c4 = [[(Odd,Even,Even), (Odd,Odd,a), (Odd,Even,b),(Odd,Odd,c) ] | a <- [Even,Odd], b <- [Even,Odd], c <- [Even,Odd] ]


mynorm :: [(Z2,Z2,Z2)] -> (Z2,Z2,Z2)
mynorm  xs = inner_product xs xs

vivi = [ (c1,c2,c3,c4) | c1 <- vi_c1, c2 <- vi_c2, c3 <- vi_c3, c4 <- vi_c4, is_o (matrix_of_columns [c1,c2,c3,c4])]

vivi' = [ (c1,c2,c3,c4) | c1 <- vi_c1, c2 <- vi_c2, c3 <- vi_c3, c4 <- vi_c4, inner_product c1 c2 /= (Even,Even,Even) && inner_product c1 c3 /= (Even,Even,Even) && inner_product  c1 c4 /= (Even,Even,Even) && inner_product  c3 c2 /= (Even,Even,Even) && inner_product  c4 c2 /= (Even,Even,Even) && inner_product  c3 c4 /= (Even,Even,Even)]

dag3 :: (Z2,Z2,Z2) -> (Z2,Z2,Z2)
dag3 (a,b,c) = (a,b,c+1)


is_unitv x = sum (zipWith (*) (map dag3 x) x) == 0

is_perp x y = sum (zipWith (*) (map dag3 x) y) == 0

is_perp1s x ys = all (is_perp x) ys

is_perpss xs ys = all (\z -> is_perp1s z ys) xs


all_perp [] = True
all_perp [h] = True
all_perp (h:t) = is_perp1s h t && all_perp t


is_o :: U4 (Z2,Z2,Z2) -> Bool
is_o m = bc && br
  where
    rs = rows_of_matrix m
    br = all_perp rs
    cs = columns_of_matrix m
    bc = all_perp cs && all is_unitv cs

eq_mod_cpd :: [CliffordT2] -> [CliffordT2] -> Bool
eq_mod_cpd x y = elem ( u4of (x ++ inv_cir y) ) $ map u4of cgperms

eq_u4 :: [CliffordT2] -> [CliffordT2] -> Bool
eq_u4 x y = u4of x == u4of y

c15 = [[],[K0],[K1],[K0,S0],[K0,CX],[K0,K1],[K1,S1],[K0,S0,CX],[K0,S0,K1],[K0,CX,K0],[K0,K1,S1],[K0,S0,CX,K0],[K0,S0,CX,K1],[K0,S0,K1,S1],[K0,S0,K1,XC]]

ce = do
  cosetEnumAR' (eq_mod_cpd) (map (\x -> [x]) [UD.II,X0,X1,Z0,Z1,S0,S1,CX,XC,CZ,Ex,K0,K1] ++ []) ([[]],[[]])

ce1 = do
  cosetEnumAR' (eq_u4) (map (\x -> [x]) [UD.II,X0,X1,Z0,Z1,S0,S1,CX,XC,CZ,Ex,K0,K1] ++ []) ([[]],[[]])


-- Enumerate Right cosets.
cosetEnumAR1' :: (Eq a, Show a) => ([a] -> [a] -> Bool) -> [[a]] -> ([[a]], [a]) -> IO ([[a]], [[a]])
cosetEnumAR1' m gs (cs, d) = do 
  let gs' = map (d ++ ) gs
  let gs'' = filter (\x -> find (m x) cs == Nothing) gs'
  let gs''' = nubBy m gs''
  let cs' = cs ++ gs'''
  return (cs', gs''')

cosetEnumAR' :: (Eq a, Show a) => ([a] -> [a] -> Bool) -> [[a]] -> ([[a]], [[a]]) -> IO ([[a]], [[a]])
cosetEnumAR' m gs (cs, []) = return (cs, [])
cosetEnumAR' m gs (cs, (h:t)) = do
  rh <- cosetEnumAR1' m gs (cs, h)
  print cs
  print $ (length cs, length (t ++ snd rh))
--  if length cs > 50 then return ([],[]) else
  cosetEnumAR' m gs (fst rh, t ++ snd rh)
