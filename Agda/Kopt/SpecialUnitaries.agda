------------------------------------------------------------------------
-- Kopt.SpecialUnitaries — Section 3 of Bian & Feng.
--
-- 3.1  Mat4 = 4×4 matrices over ℤ[i].
-- 3.2  The Clifford+CS gate set with explicit matrices (K-gates scaled by γ).
-- 3.3  Circuit = List Gate, eval, rkc, rcs, rlen.
--      GenPerm structure with phaseToZI helper.
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Kopt.SpecialUnitaries where

open import Data.Integer using (ℤ; +_; -_)
import Data.Integer as ℤ
open import Data.Nat using (ℕ; zero; suc)
open import Data.Fin using (Fin; #_)
open import Data.Fin.Patterns using (0F; 1F; 2F; 3F)
open import Data.List using (List; []; _∷_; _++_; foldl; length)
open import Data.Bool using (Bool; true; false)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (yes; no)

open import Kopt.Algebra

------------------------------------------------------------------------
-- §3.1  4×4 matrices over ℤ[i]
------------------------------------------------------------------------

Mat4 : Set
Mat4 = Fin 4 → Fin 4 → ZI

-- Identity matrix.
idMat4 : Mat4
idMat4 i j with i Data.Fin.≟ j
... | yes _ = 1ZI
... | no  _ = 0ZI
  where open import Data.Fin using (_≟_)

-- Matrix multiplication.
mulMat4 : Mat4 → Mat4 → Mat4
mulMat4 A B i k =
  (A i 0F *ZI B 0F k)
    +ZI (A i 1F *ZI B 1F k)
    +ZI (A i 2F *ZI B 2F k)
    +ZI (A i 3F *ZI B 3F k)

------------------------------------------------------------------------
-- §3.2  The Clifford+CS gate set
------------------------------------------------------------------------

data Gate : Set where
  K0 K1 S0 S1 CZ CS X0 X1 Z0 Z1 SWAP CX XC Glb : Gate

-- The phase-3 entry (index 3) corresponds to |11⟩.

-- Helper: build a ZI from an integer.
ofℤ : ℤ → ZI
ofℤ n = mkZI n (+ 0)

-- Gate matrices. We represent each by a function Fin 4 → Fin 4 → ZI
-- using pattern-match on the index pair.
-- For K0/K1, we drop the 1/γ scaling and remember it via the K-count metric.
gateMatrix : Gate → Mat4

-- K₀ = K ⊗ I (scaled by γ). Matches Haskell/Clifford.hs: rows 0/2 paired,
-- rows 1/3 paired; entries (0,0)=(0,2)=1, (1,1)=(1,3)=1, (2,0)=1, (2,2)=-1,
-- (3,1)=1, (3,3)=-1.
gateMatrix K0 0F 0F = 1ZI
gateMatrix K0 0F 2F = 1ZI
gateMatrix K0 1F 1F = 1ZI
gateMatrix K0 1F 3F = 1ZI
gateMatrix K0 2F 0F = 1ZI
gateMatrix K0 2F 2F = ofℤ (- (+ 1))
gateMatrix K0 3F 1F = 1ZI
gateMatrix K0 3F 3F = ofℤ (- (+ 1))
gateMatrix K0 _  _  = 0ZI

-- K₁ = I ⊗ K (scaled by γ). (0,0)=(0,1)=(1,0)=1, (1,1)=-1,
-- (2,2)=(2,3)=(3,2)=1, (3,3)=-1.
gateMatrix K1 0F 0F = 1ZI
gateMatrix K1 0F 1F = 1ZI
gateMatrix K1 1F 0F = 1ZI
gateMatrix K1 1F 1F = ofℤ (- (+ 1))
gateMatrix K1 2F 2F = 1ZI
gateMatrix K1 2F 3F = 1ZI
gateMatrix K1 3F 2F = 1ZI
gateMatrix K1 3F 3F = ofℤ (- (+ 1))
gateMatrix K1 _  _  = 0ZI

-- S₀ = diag(1, 1, i, i). (Affects entries 2, 3.)
gateMatrix S0 0F 0F = 1ZI
gateMatrix S0 1F 1F = 1ZI
gateMatrix S0 2F 2F = iZI
gateMatrix S0 3F 3F = iZI
gateMatrix S0 _  _  = 0ZI

-- S₁ = diag(1, i, 1, i). (Affects entries 1, 3.)
gateMatrix S1 0F 0F = 1ZI
gateMatrix S1 1F 1F = iZI
gateMatrix S1 2F 2F = 1ZI
gateMatrix S1 3F 3F = iZI
gateMatrix S1 _  _  = 0ZI

-- CZ = diag(1, 1, 1, -1).
gateMatrix CZ 0F 0F = 1ZI
gateMatrix CZ 1F 1F = 1ZI
gateMatrix CZ 2F 2F = 1ZI
gateMatrix CZ 3F 3F = ofℤ (- (+ 1))
gateMatrix CZ _  _  = 0ZI

-- CS = diag(1, 1, 1, i).
gateMatrix CS 0F 0F = 1ZI
gateMatrix CS 1F 1F = 1ZI
gateMatrix CS 2F 2F = 1ZI
gateMatrix CS 3F 3F = iZI
gateMatrix CS _  _  = 0ZI

-- X₀ = X ⊗ I, permutation [0↔2, 1↔3].
gateMatrix X0 0F 2F = 1ZI
gateMatrix X0 1F 3F = 1ZI
gateMatrix X0 2F 0F = 1ZI
gateMatrix X0 3F 1F = 1ZI
gateMatrix X0 _  _  = 0ZI

-- X₁ = I ⊗ X, permutation [0↔1, 2↔3].
gateMatrix X1 0F 1F = 1ZI
gateMatrix X1 1F 0F = 1ZI
gateMatrix X1 2F 3F = 1ZI
gateMatrix X1 3F 2F = 1ZI
gateMatrix X1 _  _  = 0ZI

-- Z₀ = Z ⊗ I = diag(1, 1, -1, -1).
gateMatrix Z0 0F 0F = 1ZI
gateMatrix Z0 1F 1F = 1ZI
gateMatrix Z0 2F 2F = ofℤ (- (+ 1))
gateMatrix Z0 3F 3F = ofℤ (- (+ 1))
gateMatrix Z0 _  _  = 0ZI

-- Z₁ = I ⊗ Z = diag(1, -1, 1, -1).
gateMatrix Z1 0F 0F = 1ZI
gateMatrix Z1 1F 1F = ofℤ (- (+ 1))
gateMatrix Z1 2F 2F = 1ZI
gateMatrix Z1 3F 3F = ofℤ (- (+ 1))
gateMatrix Z1 _  _  = 0ZI

-- SWAP = exchange qubits.
gateMatrix SWAP 0F 0F = 1ZI
gateMatrix SWAP 1F 2F = 1ZI
gateMatrix SWAP 2F 1F = 1ZI
gateMatrix SWAP 3F 3F = 1ZI
gateMatrix SWAP _  _  = 0ZI

-- CX = controlled-X (control 0, target 1).
gateMatrix CX 0F 0F = 1ZI
gateMatrix CX 1F 1F = 1ZI
gateMatrix CX 2F 3F = 1ZI
gateMatrix CX 3F 2F = 1ZI
gateMatrix CX _  _  = 0ZI

-- XC = controlled-X (control 1, target 0).
gateMatrix XC 0F 0F = 1ZI
gateMatrix XC 1F 3F = 1ZI
gateMatrix XC 2F 2F = 1ZI
gateMatrix XC 3F 1F = 1ZI
gateMatrix XC _  _  = 0ZI

-- Glb = global phase i, diag(i, i, i, i).
gateMatrix Glb 0F 0F = iZI
gateMatrix Glb 1F 1F = iZI
gateMatrix Glb 2F 2F = iZI
gateMatrix Glb 3F 3F = iZI
gateMatrix Glb _  _  = 0ZI

------------------------------------------------------------------------
-- §3.3  Circuits and counts
------------------------------------------------------------------------

Circuit : Set
Circuit = List Gate

-- Evaluate a circuit by composing gate matrices in order.
eval : Circuit → Mat4
eval c = foldl (λ acc g → mulMat4 acc (gateMatrix g)) idMat4 c

-- Predicates for counting K and CS gates.
isK : Gate → Bool
isK K0 = true
isK K1 = true
isK _  = false

isCS : Gate → Bool
isCS CS = true
isCS _  = false

-- Raw K-count: count gates g with isK g = true.
rkc : Circuit → ℕ
rkc [] = 0
rkc (g ∷ gs) with isK g
... | true  = suc (rkc gs)
... | false = rkc gs

-- Raw CS-count.
rcs : Circuit → ℕ
rcs [] = 0
rcs (g ∷ gs) with isCS g
... | true  = suc (rcs gs)
... | false = rcs gs

-- Raw length.
rlen : Circuit → ℕ
rlen = length

------------------------------------------------------------------------
-- §3.3  Generalized permutations (paper's lde-0 Clifford+CS operators)
------------------------------------------------------------------------

-- A generalized permutation is a permutation σ : Fin 4 → Fin 4 plus a
-- phase function φ : Fin 4 → Fin 4 (mod 4 phases).
-- The matrix has entry i^{φ(r)} at column σ(r) of row r, zeros elsewhere.

record GenPerm : Set where
  constructor mkGP
  field
    perm   : Fin 4 → Fin 4
    phases : Fin 4 → Fin 4

open GenPerm public

-- Convert a Fin 4 phase exponent to its corresponding power of i.
phaseToZI : Fin 4 → ZI
phaseToZI 0F = 1ZI
phaseToZI 1F = iZI
phaseToZI 2F = ofℤ (- (+ 1))
phaseToZI 3F = mkZI (+ 0) (- (+ 1))

-- The matrix of a generalized permutation.
gpToMatrix : GenPerm → Mat4
gpToMatrix gp i j with perm gp i Data.Fin.≟ j
... | yes _ = phaseToZI (phases gp i)
... | no  _ = 0ZI
  where open import Data.Fin using (_≟_)

-- Identity GP.
idGP : GenPerm
idGP = mkGP (λ i → i) (λ _ → 0F)
