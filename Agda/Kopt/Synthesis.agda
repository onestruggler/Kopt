------------------------------------------------------------------------
-- Kopt.Synthesis — Section 4 of Bian & Feng.
--
-- 4.1  Lemma 4.1: six residue patterns I-VI; pattern.toMatrix.
-- 4.2  residue1: ρ₁ residue of a Mat4 (entry-wise parity test).
-- 4.4  Per-step transition data: transitionRkc, transitionTarget.
-- 4.5  prkc table.
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Kopt.Synthesis where

open import Data.Integer using (ℤ; +_; -_)
import Data.Integer as ℤ
open import Data.Nat using (ℕ; zero; suc; _≤_; _∸_)
import Data.Nat as ℕ
open import Data.Fin using (Fin)
open import Data.Fin.Patterns using (0F; 1F; 2F; 3F)
open import Relation.Binary.PropositionalEquality using (_≡_; refl)
open import Relation.Nullary using (¬_; yes; no)

open import Kopt.Algebra
open import Kopt.SpecialUnitaries

-- Aliases to disambiguate Bit constructors (Bit.I clashes with Pattern.I).
b0 : Bit
b0 = O

b1 : Bit
b1 = Bit.I

------------------------------------------------------------------------
-- §4.1  The six residue patterns
------------------------------------------------------------------------

data Pattern : Set where
  I II III IV V VI : Pattern

-- Decidable equality on Pattern.
_≟Pat_ : (p q : Pattern) → Relation.Nullary.Dec (p ≡ q)
I   ≟Pat I   = yes refl
II  ≟Pat II  = yes refl
III ≟Pat III = yes refl
IV  ≟Pat IV  = yes refl
V   ≟Pat V   = yes refl
VI  ≟Pat VI  = yes refl
I   ≟Pat II  = no λ ()
I   ≟Pat III = no λ ()
I   ≟Pat IV  = no λ ()
I   ≟Pat V   = no λ ()
I   ≟Pat VI  = no λ ()
II  ≟Pat I   = no λ ()
II  ≟Pat III = no λ ()
II  ≟Pat IV  = no λ ()
II  ≟Pat V   = no λ ()
II  ≟Pat VI  = no λ ()
III ≟Pat I   = no λ ()
III ≟Pat II  = no λ ()
III ≟Pat IV  = no λ ()
III ≟Pat V   = no λ ()
III ≟Pat VI  = no λ ()
IV  ≟Pat I   = no λ ()
IV  ≟Pat II  = no λ ()
IV  ≟Pat III = no λ ()
IV  ≟Pat V   = no λ ()
IV  ≟Pat VI  = no λ ()
V   ≟Pat I   = no λ ()
V   ≟Pat II  = no λ ()
V   ≟Pat III = no λ ()
V   ≟Pat IV  = no λ ()
V   ≟Pat VI  = no λ ()
VI  ≟Pat I   = no λ ()
VI  ≟Pat II  = no λ ()
VI  ≟Pat III = no λ ()
VI  ≟Pat IV  = no λ ()
VI  ≟Pat V   = no λ ()
  where open import Relation.Nullary using (Dec)

-- Binary matrix for each pattern (paper Lemma 4.1, Eq. of patterns):
--   I:    diagonal {1,1,1,1}
--   II:   2×2 top-left block of 1's
--   III:  2×2 top-left + 2×2 bottom-right blocks of 1's
--   IV:   top two rows all 1's
--   V:    top-left 2×2 + bottom rows all 1's
--   VI:   all 1's
patToMatrix : Pattern → Fin 4 → Fin 4 → Bit
patToMatrix I i j with i Data.Fin.≟ j
... | yes _ = b1
... | no  _ = b0
  where open import Data.Fin using (_≟_)
patToMatrix II 0F 0F = b1
patToMatrix II 0F 1F = b1
patToMatrix II 1F 0F = b1
patToMatrix II 1F 1F = b1
patToMatrix II _  _  = b0
patToMatrix III 0F 0F = b1
patToMatrix III 0F 1F = b1
patToMatrix III 1F 0F = b1
patToMatrix III 1F 1F = b1
patToMatrix III 2F 2F = b1
patToMatrix III 2F 3F = b1
patToMatrix III 3F 2F = b1
patToMatrix III 3F 3F = b1
patToMatrix III _  _  = b0
patToMatrix IV 0F _ = b1
patToMatrix IV 1F _ = b1
patToMatrix IV _  _ = b0
patToMatrix V 0F 0F = b1
patToMatrix V 0F 1F = b1
patToMatrix V 1F 0F = b1
patToMatrix V 1F 1F = b1
patToMatrix V 2F _  = b1
patToMatrix V 3F _  = b1
patToMatrix V _  _  = b0
patToMatrix VI _ _ = b1

------------------------------------------------------------------------
-- §4.2  The ρ₁ residue of a 4×4 ZI matrix.
--       (Entry-wise parity test, equivalent to "odd" by Lemma 2.1.)
------------------------------------------------------------------------

-- Parity test: returns b1 if (re + im) is odd, else b0.
-- We compute |re + im| mod 2 via the natural-number absolute value.
parityBit : ZI → Bit
parityBit (mkZI a b) with (∣ a ℤ.+ b ∣ ℕ.% 2) ℕ.≟ 1
  where
    open import Data.Integer using (∣_∣)
    open import Data.Nat using (_%_)
... | yes _ = b1
... | no  _ = b0

-- ρ₁ residue of a matrix.
residue1 : Mat4 → Fin 4 → Fin 4 → Bit
residue1 M i j = parityBit (M i j)

------------------------------------------------------------------------
-- §4.4  Per-step transition data
------------------------------------------------------------------------

-- K-count for the step from (l, p) to (l-1, target).
transitionRkc : Pattern → ℕ → ℕ
transitionRkc I    _       = 0
transitionRkc II   _       = 2
transitionRkc III  (suc 0) = 1
transitionRkc III  _       = 2
transitionRkc IV   _       = 1
transitionRkc V    _       = 2
transitionRkc VI   _       = 1

-- Successor pattern at lde l-1.
transitionTarget : Pattern → ℕ → Pattern
transitionTarget I    _       = I
transitionTarget II   (suc 0) = I
transitionTarget II   _       = II
transitionTarget III  (suc 0) = I
transitionTarget III  _       = III
transitionTarget IV   (suc 0) = I
transitionTarget IV   _       = II
transitionTarget V    (suc 0) = I
transitionTarget V    _       = II
transitionTarget VI   (suc 0) = I
transitionTarget VI   _       = III

------------------------------------------------------------------------
-- §4.5  prkc table (Lemma 4.5)
--
-- The K-count along the complete transition path back to pattern I:
--   I:    0
--   II:   2l
--   III:  2l - 1
--   IV:   2l - 1
--   V:    2l
--   VI:   2l - 2
------------------------------------------------------------------------

prkc : ℕ → Pattern → ℕ
prkc l I    = 0
prkc l II   = 2 ℕ.* l
prkc l III  = 2 ℕ.* l ∸ 1
prkc l IV   = 2 ℕ.* l ∸ 1
prkc l V    = 2 ℕ.* l
prkc l VI   = 2 ℕ.* l ∸ 2

-- Bound: prkc l p ≤ 2·l for all p.
prkc-le-2l : ∀ (l : ℕ) (p : Pattern) → prkc l p ≤ 2 ℕ.* l
prkc-le-2l l I = ℕ.z≤n
prkc-le-2l l II = ≤-refl
  where open import Data.Nat.Properties using (≤-refl)
prkc-le-2l l III = m∸n≤m (2 ℕ.* l) 1
  where open import Data.Nat.Properties using (m∸n≤m)
prkc-le-2l l IV = m∸n≤m (2 ℕ.* l) 1
  where open import Data.Nat.Properties using (m∸n≤m)
prkc-le-2l l V = ≤-refl
  where open import Data.Nat.Properties using (≤-refl)
prkc-le-2l l VI = m∸n≤m (2 ℕ.* l) 2
  where open import Data.Nat.Properties using (m∸n≤m)
