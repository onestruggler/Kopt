------------------------------------------------------------------------
-- Kopt.Optimality — Section 5 of Bian & Feng.
--
-- IsKCOptimal / IsCSOptimal / IsLenOptimal predicates.
-- The synthesis algorithm and its correctness:
--   Lemma 4.6 (lem:alg): synth gives circuit with eval = numerator
--                        and rkc = prkc(lde, pat).
--   K-optimality lower bound: kc ≥ prkc.
--   Corollary thm:main: full statement.
--
-- The matrix-equality content of §4.4 (residue arithmetic) is captured
-- as postulates per pattern × subcase. Pattern-locking, vi-preserving,
-- and kc_descent_step (the §5 enumeration claims) are also postulates.
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Kopt.Optimality where

open import Data.Nat using (ℕ; zero; suc; _≤_; _<_; _∸_; z≤n; s≤s)
import Data.Nat as ℕ
open import Data.Nat.Properties using (≤-refl; m∸n≤m; +-comm)
open import Data.Fin using (Fin)
open import Data.List using (List; []; _∷_; _++_)
open import Data.Product using (∃; _×_; _,_; ∃-syntax; Σ; Σ-syntax)
open import Data.Sum using (_⊎_; inj₁; inj₂)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; cong; subst)
open import Relation.Nullary using (¬_; yes; no)
open import Function using (_∘_)

open import Kopt.Algebra
open import Kopt.SpecialUnitaries
open import Kopt.Synthesis
open import Relation.Binary.PropositionalEquality using (_≢_)
open import Data.Empty using (⊥; ⊥-elim)

------------------------------------------------------------------------
-- §5  UnitaryDi: A 4×4 unitary over D[i] with Lemma 4.1 invariant
------------------------------------------------------------------------

-- A 4×4 unitary over D[i], represented by its scaled numerator (a Mat4
-- over ℤ[i]) together with the lde exponent `l ≥ 0` and the residue
-- pattern `pat`. The Lemma 4.1 invariant `pat ≡ I ↔ l ≡ 0` is part of
-- the type.

record UnitaryDi : Set where
  constructor mkU
  field
    numerator : Mat4
    l         : ℕ
    pat       : Pattern
    pat-I-imp-l-zero : pat ≡ I → l ≡ 0
    l-zero-imp-pat-I : l ≡ 0 → pat ≡ I

open UnitaryDi public

-- Lemma 4.1 contrapositive: pat ≠ I implies l > 0.
pat-ne-I-imp-l-pos : (A : UnitaryDi) → pat A ≢ I → 0 < l A
pat-ne-I-imp-l-pos A hp with l A in hl
... | zero  = ⊥-elim (hp (l-zero-imp-pat-I A hl))
... | suc _ = s≤s z≤n

------------------------------------------------------------------------
-- §5  Optimal-count predicates (Definition 5.1)
------------------------------------------------------------------------

IsKCOptimal : Mat4 → ℕ → Set
IsKCOptimal A k =
  (∃[ c ] (eval c ≡ A × rkc c ≡ k)) ×
  (∀ c → eval c ≡ A → k ≤ rkc c)

IsCSOptimal : Mat4 → ℕ → Set
IsCSOptimal A k =
  (∃[ c ] (eval c ≡ A × rcs c ≡ k)) ×
  (∀ c → eval c ≡ A → k ≤ rcs c)

IsLenOptimal : Mat4 → ℕ → Set
IsLenOptimal A k =
  (∃[ c ] (eval c ≡ A × rlen c ≡ k)) ×
  (∀ c → eval c ≡ A → k ≤ rlen c)

------------------------------------------------------------------------
-- §4.4  Lemma 4.4 transitions (per pattern × subcase, axiomatized).
--
-- Each axiom delivers gpL, gpR ∈ GenPerm and a successor unitary A',
-- with the K-count, lde drop, target pattern, and matrix-equality
-- properties. The matrix-equality side is the residue-arithmetic content
-- of paper §4.4.
------------------------------------------------------------------------

postulate
  -- Lemma 4.1 (paper): patterns V and VI require lde ≥ 2.
  V-VI-lde-≥-2 : (A : UnitaryDi) → (pat A ≡ V) ⊎ (pat A ≡ VI) → 2 ≤ l A

  -- Lemma 4.1 (⇐ direction): every lde-0 unitary equals some gp matrix.
  lde-zero-is-gen-perm : (A : UnitaryDi) → l A ≡ 0 →
    ∃[ gp ] numerator A ≡ gpToMatrix gp

------------------------------------------------------------------------
-- §4.6  Lemma 4.6 (achievability, axiomatized).
--
-- For every UnitaryDi A there exists a Clifford+CS circuit with the
-- prescribed K-count, CS-count, length, and matrix equality.
------------------------------------------------------------------------

postulate
  lemma-4-6 : (A : UnitaryDi) →
    ∃[ c ] (eval c ≡ numerator A × rkc c ≡ prkc (l A) (pat A))

  -- Full statement with rcs and rlen bounds.
  lemma-4-6-full : (A : UnitaryDi) →
    ∃[ c ] (eval c ≡ numerator A
            × rkc c ≡ prkc (l A) (pat A)
            × rcs c ≤ 3 ℕ.* prkc (l A) (pat A) ℕ.+ 1
            × rlen c ≤ 36 ℕ.* prkc (l A) (pat A) ℕ.+ 12)

------------------------------------------------------------------------
-- §5  K-optimality lower bound (axiomatized).
--
-- Paper proof: induction on lde using pattern-locking + vi-preserving +
-- descent decomposition. All three are finite-enumeration claims over
-- the Clifford group.
------------------------------------------------------------------------

postulate
  -- Pattern-locking: any 1-K-gate 1-descent has source-target pattern
  -- in {III→I, IV→II, IV→V, VI→III, VI→IV}.
  pattern-locking : (A A' : UnitaryDi) (c : Circuit) →
    rkc c ≡ 1 → l A' ≡ l A ∸ 1 → eval c ≡ numerator A →
    (pat A ≡ III × pat A' ≡ I) ⊎
    (pat A ≡ IV  × pat A' ≡ II) ⊎
    (pat A ≡ IV  × pat A' ≡ V) ⊎
    (pat A ≡ VI  × pat A' ≡ III) ⊎
    (pat A ≡ VI  × pat A' ≡ IV)

  -- vi-preserving: K-count-1 0-descent from VI cannot reach II or V.
  vi-preserving : (A A' : UnitaryDi) (c : Circuit) →
    rkc c ≡ 1 → l A' ≡ l A → pat A ≡ VI → eval c ≡ numerator A →
    pat A' ≢ II × pat A' ≢ V

  -- K-optimality lower bound.
  kc-ge-prkc : (A : UnitaryDi) (c : Circuit) →
    eval c ≡ numerator A → prkc (l A) (pat A) ≤ rkc c

------------------------------------------------------------------------
-- Combined: A.numerator is K-optimal at prkc(l, pat).
------------------------------------------------------------------------

is-kc-optimal : (A : UnitaryDi) → IsKCOptimal (numerator A) (prkc (l A) (pat A))
is-kc-optimal A =
  let (c , heval , hrkc) = lemma-4-6 A
  in (c , heval , hrkc) , (λ c h-eval → kc-ge-prkc A c h-eval)

------------------------------------------------------------------------
-- Corollary thm:main (full statement)
------------------------------------------------------------------------

corollary-thm-main : (A : UnitaryDi) →
  ∃[ c ] ∃[ k ]
    (eval c ≡ numerator A
     × rkc c ≡ k
     × IsKCOptimal (numerator A) k
     × rcs c ≤ 3 ℕ.* k ℕ.+ 1
     × rlen c ≤ 36 ℕ.* k ℕ.+ 12)
corollary-thm-main A =
  let (c , heval , hrkc , hrcs , hrlen) = lemma-4-6-full A
      k = prkc (l A) (pat A)
  in c , k , heval , hrkc , is-kc-optimal A , hrcs , hrlen

-- The K-count of any synth circuit is at most 2·l.
kc-le-2l : (A : UnitaryDi) → prkc (l A) (pat A) ≤ 2 ℕ.* l A
kc-le-2l A = prkc-le-2l (l A) (pat A)
