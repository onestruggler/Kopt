{-# LANGUAGE TemplateHaskell #-}
module Kopt2 where

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
import Test.QuickCheck
import CliffordCS hiding (main' , lde , H1, H0)
import Translations
import LookupTable

-- | Six cases and the corresponding pattern matrices.

-- note that V^T = V upto row and column permutations.
data SixCases = I | II | III | IV | IVt | V | VI deriving (Show, Eq, Ord)

case_i :: U4 Z2
case_i = 1

case_ii :: U4 Z2
case_ii = (constant_mat 1 :: U2 Z2 ) `oplus` (0 :: U2 Z2)

case_iii :: U4 Z2
case_iii = (constant_mat 1 :: U2 Z2 ) `oplus` (constant_mat 1 :: U2 Z2)

case_iv :: U4 Z2
case_iv = ((constant_mat 1 :: U2 Z2) `stack_horizontal` (constant_mat 1 :: U2 Z2)) `stack_vertical` ((0 :: U2 Z2) `stack_horizontal` (0 :: U2 Z2))

case_ivt = matrix_transpose case_iv


case_vt :: U4 Z2
case_vt = ((constant_mat 1 :: U2 Z2) `stack_horizontal` (constant_mat 1 :: U2 Z2)) `stack_vertical` ((0 :: U2 Z2) `stack_horizontal` (constant_mat 1 :: U2 Z2))

case_v = matrix_transpose case_vt

case_vi :: U4 Z2
case_vi = ((constant_mat 1 :: U2 Z2) `stack_horizontal` (constant_mat 1 :: U2 Z2)) `stack_vertical` ((constant_mat 1 :: U2 Z2) `stack_horizontal` (constant_mat 1 :: U2 Z2))


pat :: SixCases -> U4 Z2
pat I = case_i
pat II = case_ii
pat III = case_iii
pat IV = case_iv
pat IVt = case_ivt
pat V = case_v
pat VI = case_vi

-- note V^T = V.
six_cases = [I,II,III,IV,V,VI,IVt]

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
-- permutation matrices L and R such that rho (LAR) = p. Moreover, if
-- lde(m) > 0, then both L and R are permutation matrices.
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
  m <- generate $ vectorOf 10000 (arbitrary :: Gen U4Di)
  let ps = nub $ sort $ map (\(p,l,r) -> p) $ map lemma_six m
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
dcir = gperm_of -- unJust $ find (\x -> u4of x == m) diag_cirs



dcir_fast :: U4Di -> [CliffordT2]
dcir_fast = gperm_of



case_iv_2bl :: U2 [Z2]
case_iv_2bl = matrix_of_rows [[[Even, Odd],[Even, Odd]],[[Even,Even],[Even,Even]]]

case_iv_2br :: Z2 -> U2 [Z2]
case_iv_2br e = let f = e + 1 in matrix_of_rows [[[Even, e],[Even, e]],[[Even, f],[Even,f]]]

case_iv_2 :: [U4 [Z2]]
case_iv_2 = [((constant_mat 1 :: U2 [Z2]) `stack_horizontal` (constant_mat 1 :: U2 [Z2])) `stack_vertical` (( case_iv_2bl) `stack_horizontal` case_iv_2br e) | e <- [Even, Odd]]

case_ivt_2 :: [U4 [Z2]]
case_ivt_2 = [((constant_mat 1 :: U2 [Z2]) `stack_vertical` (constant_mat 1 :: U2 [Z2])) `stack_horizontal` ( (matrix_transpose case_iv_2bl) `stack_vertical` (matrix_transpose (case_iv_2br e))   ) | e <- [Even, Odd]]

-- Given a matrix m with pattern IV, find genearalized matrices L and
-- R such that rho2 (LAR) =

-- 10 10 10 10
-- 10 10 10 10
-- 01 01 0e 0e
-- 00 00 0f 0f

-- where e is an indeterminate and f = e+1.

refine_iv :: U4Di -> (PDCir, PDCir)
refine_iv m = case cof m of
  IV -> (lcir4p ++ lcir4d ++ l , r ++ rcir4d ++ rcir4p)
  _ -> error "refine: not iv"
  where
    k = lamdenomexp m
    (p,l,r) = lemma_six m
    m2 = rho k 2 (u4of l * m * u4of r)

    rcir4' = 
      im (matrix_index m2 0 0) 0
      * im (matrix_index m2 0 1) 1
      * im (matrix_index m2 0 2) 2
      * im (matrix_index m2 0 3) 3
      
    rcir4d = dcir rcir4'

    m2' = m2 * rho 0 2 rcir4'

    lcir4' = if matrix_index m2' 1 0 == [Odd,Even] then
      1 else
      im (matrix_index m2' 1 0) 1 *
      im [Odd,Odd] 2
      
    lcir4d = dcir $ lcir4'

    m2'' = rho 0 2 lcir4' * m2'
    lcir4p = if matrix_index m2'' 2 0 == [Even, Odd] then [] else [CX]
    m2''' = rho 0 2 (u4of lcir4p) * m2''
    rcir4p = if matrix_index m2''' 2 1 == [Even, Odd] then [] else
      if matrix_index m2''' 2 2 == [Even, Odd] then [Ex] else [CX,Ex]

test_refine_iv = do
  m <- generate $ vectorOf 1000 (arbitrary :: Gen U4Di)
  let ps = filter (\x -> let (p,l,r) = lemma_six x in p == IV) m
  let lrs = map (\x -> (refine_iv x, x)) ps
  sequence_ $ map print $ nub $  map (\((ll,rr),x) -> let p2 = rhok 2 (u4of ll * x * u4of rr) in (p2 `elem` case_iv_2, p2)) lrs

refine_ivt :: U4Di -> (PDCir, PDCir)
refine_ivt m = case cof m of
  IVt -> (inv_cir r , inv_cir l)
  _ -> error "refine: not ivt"
  where
    (l,r) = refine_iv (dagger m)

test_refine_ivt = do
  m <- generate $ vectorOf 1000 (arbitrary :: Gen U4Di)
  let ps = filter (\x -> let (p,l,r) = lemma_six x in p == IVt) m
  print $ cof $ dagger (head ps)
  let lrs = map (\x -> (refine_ivt x, x)) ps
  sequence_ $ map print $ nub $  map (\((ll,rr),x) -> let p2 = rhok 2 (u4of ll * x * u4of rr) in (p2 `elem` (case_ivt_2), p2)) lrs


-- Given a matrix m with pattern II, find genearalized matrices L and
-- R such that if lde m > 1, rho2 (LAR) =

-- 10 10 01 00
-- 10 10 01 00
-- 01 01 0d 0d
-- 00 00 0d 0d

-- if lde m = 1, rho2 (LAR) =

-- 10 10 00 00
-- 10 10 00 00
-- 00 00 0d 0e
-- 00 00 0f 0g

pii2 :: Z2 -> U4 [Z2]
pii2 d = matrix_of_rows [
  [[1,0],[1,0],[0,1],[0,0]],
  [[1,0],[1,0],[0,1],[0,0]],
  [[0,1],[0,1],[0,d],[0,d]],
  [[0,0],[0,0],[0,d],[0,d]]
  ]

pii2k1 :: Z2 -> Z2 -> Z2 -> Z2 -> U4 [Z2]
pii2k1 d e f g = matrix_of_rows [
  [[1,0],[1,0],[0,0],[0,0]],
  [[1,0],[1,0],[0,0],[0,0]],
  [[0,0],[0,0],[0,d],[0,e]],
  [[0,0],[0,0],[0,f],[0,g]]
  ]

refine_ii :: U4Di -> (PDCir, PDCir)
refine_ii m = case cof m of
  II -> case lde m of
    1 -> (dcir l' ++ l , r ++ dcir r')
    _ -> (l'' ++ dcir l' ++ l , r ++ dcir r' ++ r'')
  px -> error $ "cannot refine " ++ show px
  where
    k = lamdenomexp m
    (p,l,r) = lemma_six m
    mres = rho k 2 (u4of l * m * u4of r)

    r' = if matrix_index mres 0 0 + matrix_index mres 0 1 == [Even,Even] then
      im (matrix_index mres 0 0) 0 *
      im (matrix_index mres 0 1) 1
      else
      im (matrix_index mres 0 0) 0 *
      im (matrix_index mres 0 1) 1 *
      im [Odd,Odd] 3
      
    mres' = mres * rho 0 2 r'

    l' = if matrix_index mres' 1 0 == [Odd,Even] then
      1 else
      im (matrix_index mres' 1 0) 1
      * im [Odd,Odd] 3

    mres'' = rho 0 2 l' * mres'
    
    l'' = if matrix_index mres'' 2 0 == [Even, Odd] then [] else [CX]
    
    mres''' = rho 0 2 (u4of l'') * mres''
    
    r'' = if matrix_index mres''' 0 2 == [Even, Odd] then [] else [CX]


test_refine_ii = do
  m <- generate $ vectorOf 1000 (arbitrary :: Gen U4Di)
  let ps = filter (\x -> let (p,l,r) = lemma_six x in p == II) m
  let lrs = map (\x -> (refine_ii x, x)) ps
  sequence_ $ map print $ nub $  map (\((ll,rr),x) -> let p2 = rhok 2 (u4of ll * x * u4of rr) in (p2 `elem` [pii2 d | d <- [Even,Odd]], p2)) lrs

test_refine_iik1 = do
  m <- generate $ vectorOf 1000 (arbitrary :: Gen U4Di)
  let ps = filter (\x -> let (p,l,r) = lemma_six x in p == II && lde x == 1) m
  let lrs = map (\x -> (refine_ii x, x)) ps
  sequence_ $ map print $ nub $  map (\((ll,rr),x) -> let p2 = rhok 2 (u4of ll * x * u4of rr) in (p2 `elem` [pii2k1 d e f g | d <- [Even,Odd], e <- [Even,Odd], f <- [Even,Odd], g <- [Even,Odd] ], p2)) lrs



-- Given a matrix m with pattern III, find genearalized matrices L and
-- R such that if lde m > 1, rho2 (LAR) =

-- 10 10 01 00
-- 10 10 00 01
-- 01 00 10 10
-- 00 01 10 10

-- if lde m = 1, rho2 (LAR) =

-- 10 10 00 00
-- 10 10 00 00
-- 00 00 10 10
-- 00 00 10 10

piii2 :: U4 [Z2]
piii2 = matrix_of_rows [
  [[1,0],[1,0],[0,1],[0,0]],
  [[1,0],[1,0],[0,0],[0,1]],
  [[0,1],[0,0],[1,0],[1,0]],
  [[0,0],[0,1],[1,0],[1,0]]
  ]

piii2k1 :: U4 [Z2]
piii2k1 = matrix_of_rows [
  [[1,0],[1,0],[0,0],[0,0]],
  [[1,0],[1,0],[0,0],[0,0]],
  [[0,0],[0,0],[1,0],[1,0]],
  [[0,0],[0,0],[1,0],[1,0]]
  ]


refine_iii :: U4Di -> (PDCir, PDCir)
refine_iii m = case cof m of
  III -> case lde m of
    1 -> (dcir l' ++ l , r ++ dcir r')
    _ -> (l'' ++ dcir l' ++ l , r ++ dcir r' ++ r'')
  px -> error $ "cannot refine " ++ show px
  where
    k = lamdenomexp m
    (p,l,r) = lemma_six m
    mres = rho k 2 (u4of l * m * u4of r)

    r' =
      im (matrix_index mres 0 0) 0 *
      im (matrix_index mres 0 1) 1 *
      im (matrix_index mres 2 2) 2 *
      im (matrix_index mres 2 3) 3
      
    mres' = mres * rho 0 2 r'

    l' = 
      im (matrix_index mres' 0 0) 0 *
      im (matrix_index mres' 1 0) 1 *
      im (matrix_index mres' 3 2) 3

    mres'' = rho 0 2 l' * mres'
    
    l'' = if matrix_index mres'' 2 0 == [Even, Odd] then [] else [CX]
    
    mres''' = rho 0 2 (u4of l'') * mres''
    
    r'' = if matrix_index mres''' 0 2 == [Even, Odd] then [] else [CX]


test_refine_iii = do
  m <- generate $ vectorOf 1000 (arbitrary :: Gen U4Di)
  let ps = filter (\x -> let (p,l,r) = lemma_six x in p == III) m
  let lrs = map (\x -> (refine_iii x, x)) ps
  sequence_ $ map print $ nub $  map (\((ll,rr),x) -> let p2 = rhok 2 (u4of ll * x * u4of rr) in (p2 `elem` [piii2 ], p2)) lrs

test_refine_iiik1 = do
  m <- generate $ vectorOf 1000 (arbitrary :: Gen U4Di)
  let ps = filter (\x -> let (p,l,r) = lemma_six x in p == III && lde x == 1) m
  let lrs = map (\x -> (refine_iii x, x)) ps
  sequence_ $ map print $ nub $  map (\((ll,rr),x) -> let p2 = rhok 2 (u4of ll * x * u4of rr) in (p2 `elem` [piii2k1 ], p2)) lrs




-- Given a matrix m with pattern V, find genearalized matrices L and
-- R such that if lde m > 1, rho2 (LAR) =


-- 10 10 01 00
-- 10 10 00 01
-- 10 11 10 11
-- 10 11 11 10


pv2 :: U4 [Z2]
pv2 = matrix_of_rows [
  [[1,0],[1,0],[0,1],[0,0]],
  [[1,0],[1,0],[0,0],[0,1]],
  [[1,0],[1,1],[1,0],[1,1]],
  [[1,0],[1,1],[1,1],[1,0]]
  ]


refine_v :: U4Di -> (PDCir, PDCir)
refine_v m = case cof m of
  V -> (dcir l' ++ l , r ++ dcir r' ++ r'' ++ dcir r''')
  px -> error $ "cannot refine " ++ show px
  where
    k = lamdenomexp m
    (p,l,r) = lemma_six m
    mres = rho k 2 (u4of l * m * u4of r)

    l' =
      im (matrix_index mres 0 0) 0 *
      im (matrix_index mres 1 0) 1 *
      im (matrix_index mres 2 0) 2 *
      im (matrix_index mres 3 0) 3
      
    mres' = rho 0 2 l' * mres

    r' =
      im (matrix_index mres' 0 1) 1
      
    mres'' = mres' * rho 0 2 r'
    
    r'' = if matrix_index mres'' 0 2 == [Even, Odd] then [] else [CX]
    
    mres''' = mres'' * rho 0 2 (u4of r'')

    r''' =
      im (matrix_index mres''' 2 2) 2 *
      im (matrix_index mres''' 3 3) 3



test_refine_v = do
  m <- generate $ vectorOf 1000 (arbitrary :: Gen U4Di)
  let ps = filter (\x -> let (p,l,r) = lemma_six x in p == V) m
  let lrs = map (\x -> (refine_v x, x)) ps
  sequence_ $ map print $ nub $  map (\((ll,rr),x) -> let p2 = rhok 2 (u4of ll * x * u4of rr) in (p2 `elem` [pv2 ], p2)) lrs



-- Given a matrix m with pattern VI, find genearalized matrices L and
-- R such that if lde m > 1, rho2 (LAR) =


-- 10 10 01 00
-- 10 10 00 01
-- 10 11 10 11
-- 10 11 11 10


pvi2 :: Z2 -> U4 [Z2]
pvi2 e = matrix_of_rows [
  [[1,0],[1,0],[1,0],[1,0]],
  [[1,0],[1,0],[1,0],[1,0]],
  [[1,0],[1,0],[1,e],[1,e]],
  [[1,0],[1,0],[1,e],[1,e]]
  ]


refine_vi :: U4Di -> (PDCir, PDCir)
refine_vi m = case cof m of
  VI -> (l''' ++ l'' ++ dcir l' ++ l , r ++ dcir r' ++ r''')
  px -> error $ "cannot refine " ++ show px
  where
    k = lamdenomexp m
    (p,l,r) = lemma_six m
    mres = rho k 2 (u4of l * m * u4of r)

    l' = 
      im (matrix_index mres 0 0) 0 *
      im (matrix_index mres 1 0) 1 *
      im (matrix_index mres 2 0) 2 *
      im (matrix_index mres 3 0) 3
      
    mres' = rho 0 2 l' * mres

    r' = 
      im (matrix_index mres' 0 1) 1 *
      im (matrix_index mres' 0 2) 2 *
      im (matrix_index mres' 0 3) 3
      
    mres'' = mres' * rho 0 2 r'
    
    l'' =
      if matrix_index mres'' 1 1 == [Odd, Even] then [] else
      if matrix_index mres'' 2 1 == [Odd, Even] then [Ex] else [Ex,CX]
    
    mres''' = rho 0 2 (u4of l'') * mres''

    l''' =
      if matrix_index mres''' 1 2 == [Odd, Even] then [] else
      if matrix_index mres''' 2 2 == [Odd, Even] then [Ex] else [Ex,CX]

    r''' =
      if matrix_index mres''' 2 1 == [Odd, Even] then [] else
      if matrix_index mres''' 2 2 == [Odd, Even] then [Ex] else [CX,Ex]




test_refine_vi = do
  m <- generate $ vectorOf 1000 (arbitrary :: Gen U4Di)
  let ps = filter (\x -> let (p,l,r) = lemma_six x in p == VI) m
  let lrs = map (\x -> (refine_vi x, x)) ps
  sequence_ $ map print $ nub $  map (\((ll,rr),x) -> let p2 = rhok 2 (u4of ll * x * u4of rr) in (p2 `elem` [pvi2 e | e <- [Even, Odd] ], p2)) lrs




refine :: U4Di -> (PDCir, PDCir)
refine m = case cof m of
  II -> refine_ii m
  III -> refine_iii m
  IV -> refine_iv m
  IVt -> refine_ivt m
  V -> refine_v m
  VI -> refine_vi m

    

decrease1_lde :: U4Di -> (PDCir, PDCir)
decrease1_lde m
  | lde m == 0 = ([],[])
  | otherwise = case cof m of
      I -> error "lde=0"
      II -> case lde m of
        1 -> ([X0,CK,X0] ++ lref, rref)
        _ -> ([K1,S1] ++ lref, rref)
      III -> case lde m of
        1 -> ([K1] ++ lref, rref)
        _ -> ([K1,S1] ++ lref, rref)
      IV -> (lref, rref ++ [K1])
      IVt -> (inv_cir rih, inv_cir lih)
      V -> ([K1] ++ lref, rref)
      VI -> ([K1] ++ lref, rref)
      where
        (lref,rref) = refine m
        (lih, rih) = decrease1_lde (dagger m)
      


synth' :: Int -> U4Di -> ([CliffordT2], [CliffordT2])
synth' j m
  | j < 0 = ([],[])
synth' ss m
  | lde m == 0 = (inv_cir (gperm_of m), [])
  | otherwise = (li ++ l1, r1 ++ ri)
  where
    (l1,r1) = decrease1_lde m
    m' = u4of l1 * m * u4of r1
    (li, ri) = synth' (ss-1) m'

synth :: U4Di -> [CliffordT2]
synth m = ret
  where
  (l,r) = synth' (fromIntegral $ lde m * 2) m
  ret = optimize_gp $ inv_cir (r ++ l)

decompose_ck :: CliffordT2 -> [CliffordT2]
decompose_ck CK = [CZ,Z0,S0,Z1,S1,K1,CS,K1,S1,UD.II]
decompose_ck x = [x]

desugar_ck :: [CliffordT2] -> [CliffordT2]
desugar_ck = concat . map decompose_ck

optimize_gp' :: [CliffordT2] -> [CliffordT2]
optimize_gp' [] = []
optimize_gp' (K0 : t) = K0 : optimize_gp' t
optimize_gp' (K1 : t) = K1 : optimize_gp' t
optimize_gp' xs@(h : t) = gp' ++ optimize_gp' rem
  where
    gp = takeWhile (\x -> x /= K0 && x /= K1) xs
    rem = dropWhile (\x -> x /= K0 && x /= K1) xs
    gp' = gperm_of (u4of gp)

optimize_gp :: [CliffordT2] -> [CliffordT2]
optimize_gp = optimize_gp' . desugar_ck



all_cli_CP :: [[CliffordT2]]
all_cli_CP = [gp ++ c | gp <- gperms, c <- c15]


optimize_cli' :: [CliffordT2] -> [CliffordT2]
optimize_cli' [] = []
optimize_cli' (CS : t) = CS : optimize_cli' t
optimize_cli' xs@(h : t) = cli' ++ optimize_cli' rem
  where
    cli = takeWhile (\x -> x /= CS) xs
    rem = dropWhile (\x -> x /= CS) xs
    cli' = unJust $ find (\x -> u4of x == u4of cli) all_cli_CP

optimize_cli'_fast :: [CliffordT2] -> [CliffordT2]
optimize_cli'_fast [] = []
optimize_cli'_fast (CS : t) = CS : optimize_cli'_fast t
optimize_cli'_fast xs@(h : t) = cli' ++ optimize_cli'_fast rem
  where
    cli = takeWhile (\x -> x /= CS) xs
    rem = dropWhile (\x -> x /= CS) xs
    cli' = cli_of2k (u4of cli)




pc_cli_2k = $(precomputed_mat_cliQ2k ())
pc_gperms = $(precomputed_mat_gpermsQ ())

cli_of2k :: U4Di -> [CliffordT2]
cli_of2k x = if lde x <= 2 then ret else error $ "lde>2, not a Clifford" ++ show x
  where
    f = (\x -> (
                                  (lamdenomexp x,
                                   (map (\(Cplx x y) -> (x, y)) (concat (rows_of_matrix (fst (lamdenomexp_decompose x))))))
                                  , x)
                                  )
    mzzs = map (\k -> fst (f (x * u4of (replicate k UD.II)))) [0..3]
    rets = filter (/= Nothing) $ map (\x -> lookup x pc_cli_2k) mzzs
    ret = unJust $ head rets

gperm_of :: U4Di -> [CliffordT2]
gperm_of x = if lde x <= 2 then ret else error "lde>2, not a Clifford"
  where
    f = (\x -> (
                                  (lamdenomexp x,
                                   (map (\(Cplx x y) -> (x, y)) (concat (rows_of_matrix (fst (lamdenomexp_decompose x))))))
                                  , x)
                                  )
    mzzs = map (\k -> fst (f (x * u4of (replicate k UD.II)))) [0..3]
    rets = filter (/= Nothing) $ map (\x -> lookup x pc_gperms) mzzs
    ret = unJust $ head rets


optimize_cli :: [CliffordT2] -> [CliffordT2]
optimize_cli = optimize_cli'_fast . desugar_ck



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
  let lrs = map (\x -> (synth x, x)) ps
  sequence_ $ map print $  filter (\(a,b,c,d,e,f,g) -> True) $ map (\(ret,x) -> (cof x, lde x, u4of ret == x, kc ret, csc ret, length ret, fromIntegral (kc ret) / fromIntegral (lde x))) lrs

kc :: Cir -> Int
kc xs = length $ filter (\x -> x == K0 || x == K1 || x == H1 || x == H0) xs

csc :: Cir -> Int
csc xs = length $ filter (\x -> x == CS) xs


cli_of :: (SO6 DRootTwo) -> [SO6.CliffordT2]
cli_of xm = []
  where
    (mm, lde) = denomexp_decompose xm


    
synthcs :: [SO6.CliffordT2] -> [CliffordT2]
synthcs x = optimize_cli $ map f $ simp ret
  where
    m4 = evalCircuit4 $ cs2_of_t2 x

    ret = case synthesizeFromMat4 m4 of
      Right sr -> t2_of_sr sr
      Left msg -> error msg

    t2_of_sr :: SynthResult -> [CliffordT2]
    t2_of_sr (SynthResult srgs srcli) = ss ++ mycli
      where
        conj2 x = t2_of_cs2 $ conjugator2 x
        ss = map t2_of_t2 $ concat $ map (\x -> conj2 x ++ [SO6.CS] ++ SO6.inv_cir (conj2 x) ) srgs
        c = u4of (inv_cir ss) * u4of ((map t2_of_t2 x))
        mycli = cli_of2k c

    f H0 = K0
    f H1 = K1
    f x = x
    

grouping :: Int -> [a] -> [[a]]
grouping k [] = []
grouping k xs@(h:t) = take k xs : grouping k (drop k xs)

    
test_compare = do
  ms1 <- generate $ vectorOf 1000 (arbitrary :: Gen U4Di)
  let ms = map product $ grouping 50 ms1
  let lrs = map (\x -> let x' = synth x in (x, x', synthcs (map t2_of_t2' x'))) ms
  print ("lde" , "mycs", "ocs", "mykc", "Julien's kc")
  sequence_ $ map print $ map (\(x, a,b) -> (lde x, csc a, csc b, kc a, kc b)) lrs

test_comparek = do
  ms <- generate $ vectorOf 1000 (arbitrary :: Gen U4Di)
  let lrs = map (\x -> let x' = synth x in (x, x', synthcs (map t2_of_t2' x'))) ms
  sequence_ $ map print $ map (\(x, a,b) -> (lde x, kc a, kc b, fromIntegral (csc b) / fromIntegral (lde x), fromIntegral (csc a) / fromIntegral (lde x))) lrs

cal1 = do
  let ms = map u4of [concat $ replicate 10 [CK,KC]]
  let lrs = map (\x -> let x' = synth x in (x, x', synthcs (map t2_of_t2' x'))) ms
  print ("lde" , "mycs", "ocs", "mykc", "Julien's kc")
  sequence_ $ map print $ map (\(x, a,b) -> (lde x, csc a, csc b, kc a, kc b)) lrs
--  print $ let a = synth $ u4of $ concat $ replicate 20 [CK,KC] in
--    let b = synthcs (map t2_of_t2' a) in (kc a, csc a, kc b , csc b, a , b)

cal2 = do
  print $ let a = synth $ u4of $ concat $ replicate 30 [CK,KC] in
    let b = synthcs (map t2_of_t2' a) in (lde (u4of a), csc b, csc a, kc a, kc b)


test_compare_lde_cs = do
  ms <- generate $ vectorOf 1000 (arbitrary :: Gen U4Di)
  let lrs = map (\x -> let x' = synth x in (x, x', synthcs (map t2_of_t2' x'))) ms
  sequence_ $ map print $ map (\(x, a,b) -> (lde x, csc a, csc b, fromIntegral (csc a) / fromIntegral (csc b))) lrs



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


-- | Experiments

case_vi_rho2tr :: U2 [Z2]
case_vi_rho2tr = matrix_of_rows [[[Odd,Even],[Odd,Even]],[[Odd,Odd],[Odd,Odd]]]

case_vi_rho2br :: U2 [Z2]
case_vi_rho2br = matrix_of_rows [[[Odd,Even],[Odd,Odd]],[[Odd,Odd],[Odd,Even]]]

case_vi_rho2br' :: U2 [Z2]
case_vi_rho2br' = matrix_of_rows [[[Odd,Odd],[Odd,Even]],[[Odd,Even],[Odd,Odd]]]

case_vi_rho2 :: U4 [Z2]
case_vi_rho2 = ((constant_mat 1 :: U2 [Z2]) `stack_horizontal` case_vi_rho2tr) `stack_vertical` ((matrix_transpose case_vi_rho2tr) `stack_horizontal` case_vi_rho2br')
