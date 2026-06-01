{-# LANGUAGE TemplateHaskell #-}

module Translations where
import Clifford
import SO6
import qualified U4Di as UD
import CliffordCS hiding (main)
import System.Environment
import Test.QuickCheck

import qualified Quantum.Synthesis.MultiQubitSynthesis as MS
import Quantum.Synthesis.MultiQubitSynthesis
import Quantum.Synthesis.EuclideanDomain
import Quantum.Synthesis.Ring
import Quantum.Synthesis.Matrix
import Data.List

rows_of_list :: Int -> [a] -> [[a]]
rows_of_list k [] = []
rows_of_list k xs@(h:t) = take k xs : rows_of_list k (drop k xs)

rows_of_mat6E :: [a] -> [[a]]
rows_of_mat6E = rows_of_list 6

rows_of_mat4E :: [a] -> [[a]]
rows_of_mat4E = rows_of_list 4

t2_of_cs2_gate :: Gate2 -> CliffordT2
t2_of_cs2_gate CliffordCS.H1 = SO6.H0
t2_of_cs2_gate CliffordCS.H2 = SO6.H1
t2_of_cs2_gate CliffordCS.S1g = SO6.S0
t2_of_cs2_gate CliffordCS.S2g = SO6.S1
t2_of_cs2_gate CliffordCS.CZg = SO6.CZ
t2_of_cs2_gate CliffordCS.CSg = SO6.CS


t2_of_cs2 :: Circuit2 -> [CliffordT2]
t2_of_cs2 = map t2_of_cs2_gate

cs2_of_t2_gate :: CliffordT2 -> [Gate2]
cs2_of_t2_gate SO6.H0 = [CliffordCS.H1]
cs2_of_t2_gate SO6.H1 = [CliffordCS.H2]
cs2_of_t2_gate SO6.S0 = [CliffordCS.S1g]
cs2_of_t2_gate SO6.S1 = [CliffordCS.S2g]
cs2_of_t2_gate SO6.CZ = [CliffordCS.CZg]
cs2_of_t2_gate SO6.CS = [CliffordCS.CSg]

cs2_of_t2_gate SO6.Z0 = [CliffordCS.S1g, CliffordCS.S1g]
cs2_of_t2_gate SO6.Z1 = [CliffordCS.S2g, CliffordCS.S2g]

cs2_of_t2_gate SO6.X0 = [CliffordCS.H1,CliffordCS.S1g, CliffordCS.S1g,CliffordCS.H1]
cs2_of_t2_gate SO6.X1 = [CliffordCS.H2,CliffordCS.S2g, CliffordCS.S2g,CliffordCS.H2]


cs2_of_t2_gate CX = [CliffordCS.H2,CliffordCS.CZg,CliffordCS.H2]
cs2_of_t2_gate XC = [CliffordCS.H1,CliffordCS.CZg,CliffordCS.H1]

cs2_of_t2_gate Ex = cs2_of_t2_gate CX ++ cs2_of_t2_gate XC ++ cs2_of_t2_gate CX
cs2_of_t2_gate WI = []

cs2_of_t2 :: [CliffordT2] -> Circuit2
cs2_of_t2 = concat . map cs2_of_t2_gate

so6_of_mat6 :: Mat6 -> SO6 DRootTwo
so6_of_mat6 (Mat6 k e) = matrix $ rows_of_mat6E $ map aux e
  where
    auxe :: Integer -> DRootTwo
    auxe x = RootTwo (Dyadic (fromIntegral x) (fromIntegral (k `div` 2))) 0
    auxo :: Integer -> DRootTwo
    auxo x = RootTwo (Dyadic (fromIntegral x) (fromIntegral ((k+1) `div` 2))) 0 * roottwo
    aux = if even k then auxe else auxo


su4_of_mat4 :: Mat4 -> SU4 DOmega
su4_of_mat4 (Mat4 k e) = matrix $ rows_of_mat4E $ map aux e
  where
    dof x = Dyadic x (fromIntegral (k `div` 2))
    dof' x = Dyadic x (fromIntegral ((k+1) `div` 2))
    auxe :: CliffordCS.ZOmega -> DOmega
    auxe (ZO d c b a) = Omega (dof a) (dof b) (dof c) (dof d)
    auxo :: CliffordCS.ZOmega -> DOmega
    auxo x@(ZO d c b a) = Omega (dof' a) (dof' b) (dof' c) (dof' d) * roottwo
    aux = if even k then auxe else undefined

pqs_of_sgate :: Mat6 -> [(Int, Int)]
pqs_of_sgate m6 = head $ filter (\ x -> so6_of_mat6 m6 == so6ofii x) candis
  where
    candis = [[(p1,q1),(p2,q2),(p3,q3)] | p1 <- [0..5] , q1 <- [0..5], p1 /= q1,  p2 <- [0..5] , q2 <- [0..5], p2 /= q2,  p3 <- [0..5] , q3 <- [0..5], p3 /= q3 ]

t2_of_t2 :: CliffordT2 -> UD.CliffordT2

t2_of_t2 S0 = UD.S0
t2_of_t2 S1 = UD.S1
t2_of_t2 Z0 = UD.Z0
t2_of_t2 Z1 = UD.Z1
t2_of_t2 H0 = UD.K0
t2_of_t2 SO6.H1 = UD.K1
t2_of_t2 X0 = UD.X0
t2_of_t2 X1 = UD.X1
t2_of_t2 T0 = UD.T0
t2_of_t2 T1 = UD.T1
t2_of_t2 CS = UD.CS
t2_of_t2 CZ = UD.CZ
t2_of_t2 WI = UD.II
t2_of_t2 Ex = UD.Ex

t2_of_t2 CX = UD.CX
t2_of_t2 XC = UD.XC


t2_of_t2' :: UD.CliffordT2 -> CliffordT2

t2_of_t2' UD.S0 = S0
t2_of_t2' UD.S1 = S1
t2_of_t2' UD.Z0 = Z0
t2_of_t2' UD.Z1 = Z1
t2_of_t2' UD.H0 = H0
t2_of_t2' UD.H1 = SO6.H1
t2_of_t2' UD.K0 = H0
t2_of_t2' UD.K1 = SO6.H1
t2_of_t2' UD.X0 = X0
t2_of_t2' UD.X1 = X1
t2_of_t2' UD.T0 = T0
t2_of_t2' UD.T1 = T1
t2_of_t2' UD.CS = CS
t2_of_t2' UD.CZ = CZ
t2_of_t2' UD.II = WI
t2_of_t2' UD.Ex = Ex

t2_of_t2' UD.CX = CX
t2_of_t2' UD.XC = XC
