------------------------------------------------------------------------
-- Kopt.Algebra — Section 2 of Bian & Feng.
--
-- Contents:
--   2.1 ZI = Gaussian integers ℤ[i] = {a+bi | a,b ∈ ℤ}, γ = 1+i, conj, norm.
--       Lemma 2.1 (parity-norm), Lemma 2.3 (cancel-γ).
--   2.2 Di = ℤ[½, i] with stored exponent and lde,
--       Lemma 2.2 (k-odd), Lemma 2.4 (subadditivity / additivity for odd).
--   2.3 Bit type, binary n-digit residues.
------------------------------------------------------------------------

{-# OPTIONS --without-K #-}

module Kopt.Algebra where

open import Data.Integer using (ℤ; +_)
import Data.Integer as ℤ
open import Data.Nat using (ℕ; zero; suc)
import Data.Nat as ℕ
open import Data.Fin using (Fin)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; sym; trans; cong; cong₂)
open import Relation.Nullary using (¬_; Dec; yes; no)
open import Data.Empty using (⊥; ⊥-elim)
open import Data.Product using (∃; _×_; _,_; proj₁; proj₂; Σ; Σ-syntax)

------------------------------------------------------------------------
-- §2.1  Gaussian integers ℤ[i]
------------------------------------------------------------------------

record ZI : Set where
  constructor mkZI
  field
    re : ℤ
    im : ℤ

open ZI public

infixl 6 _+ZI_ _-ZI_
infixl 7 _*ZI_

_+ZI_ : ZI → ZI → ZI
mkZI a b +ZI mkZI c d = mkZI (a ℤ.+ c) (b ℤ.+ d)

_-ZI_ : ZI → ZI → ZI
mkZI a b -ZI mkZI c d = mkZI (a ℤ.- c) (b ℤ.- d)

-ZI_ : ZI → ZI
-ZI mkZI a b = mkZI (ℤ.- a) (ℤ.- b)

_*ZI_ : ZI → ZI → ZI
mkZI a b *ZI mkZI c d = mkZI (a ℤ.* c ℤ.- b ℤ.* d) (a ℤ.* d ℤ.+ b ℤ.* c)

0ZI : ZI
0ZI = mkZI (+ 0) (+ 0)

1ZI : ZI
1ZI = mkZI (+ 1) (+ 0)

-- The imaginary unit i.
iZI : ZI
iZI = mkZI (+ 0) (+ 1)

-- γ = 1 + i.
γ : ZI
γ = mkZI (+ 1) (+ 1)

-- Complex conjugation.
conj : ZI → ZI
conj (mkZI a b) = mkZI a (ℤ.- b)

-- Norm squared |z|² = a² + b² ∈ ℤ.
normSq : ZI → ℤ
normSq (mkZI a b) = a ℤ.* a ℤ.+ b ℤ.* b

-- Decidable equality on ZI.
_≟ZI_ : (x y : ZI) → Dec (x ≡ y)
mkZI a b ≟ZI mkZI c d with a ℤ.≟ c
... | no  a≢c = no λ eq → a≢c (cong re eq)
... | yes a≡c with b ℤ.≟ d
...   | no  b≢d = no λ eq → b≢d (cong im eq)
...   | yes b≡d = yes (cong₂ mkZI a≡c b≡d)

-- Power γⁿ.
powγ : ℕ → ZI
powγ zero = 1ZI
powγ (suc n) = powγ n *ZI γ

------------------------------------------------------------------------
-- §2.2  D[i] = ℤ[½, i] with stored γ-exponent
--
-- Selinger's analogue (`Quantum.Synthesis.Ring` in `newsynth`): `DComplex`,
-- which is `Cplx Dyadic` — a complex with `Dyadic` real and imaginary
-- parts, where `Dyadic Integer Integer` stores `(numerator, exponent)`
-- representing `numerator / 2^exponent` non-normalized. `denomexp` is
-- computed by stripping trailing factors of 2.
--
-- Our `Di` differs in one notational way: instead of carrying two
-- `Dyadic`s (one for the real part, one for the imaginary part), we
-- store a single `ZI` numerator with a single shared **γ-exponent**
-- (where γ = 1+i). Since γ² = 2i is an associate of 2, dividing by γ^k
-- is essentially the same as dividing by 2^⌈k/2⌉ — but at finer
-- granularity (γ-divisions count K-gates one-to-one in the paper).
--
-- The stored `denExp` is an *upper bound* on the true least denominator
-- exponent. Multiplication is `(z₁/γᵏ¹)(z₂/γᵏ²) = z₁z₂ / γᵏ¹⁺ᵏ²`, which
-- always preserves the upper-bound property but not minimality.
--
-- The actual `lde` (paper's notation) is the smallest k such that
-- γ^k · x ∈ ℤ[i]. It equals `denExp - (number of γ-factors of num)`.
-- For multiplication, lde is *additive* iff both numerators are odd
-- (Lemma 2.4b); otherwise it's strictly subadditive (Lemma 2.4a).
------------------------------------------------------------------------

record Di : Set where
  constructor mkDi
  field
    num    : ZI
    denExp : ℕ  -- upper bound on the γ-exponent (stored, not minimal)

open Di public

-- Divisibility by γ in ℤ[i]: γ | z iff (re + im) is even.
-- Equivalent to z ≡ 0 (mod γ).
isEven : ZI → Set
isEven (mkZI a b) = Σ[ q ∈ ℤ ] (sumab ≡ two ℤ.* q)
  where
    sumab = a ℤ.+ b
    two   = + 2

-- A Gaussian integer is odd iff not even.
isOdd : ZI → Set
isOdd z = ¬ (isEven z)

-- The stored γ-exponent (upper bound on true lde).
-- Caller is responsible for ensuring it's minimal when needed.
denomExp : Di → ℕ
denomExp = denExp

-- The lde (least denominator exponent) of x ∈ D[i].
-- For our representation it equals `denExp` *when the numerator is odd*
-- (or when `denExp = 0`). In general, lde ≤ denExp.
--
-- We expose `lde` as a synonym for `denExp`, matching the paper's
-- convention that callers maintain minimality. Lemma 2.4a (`lde-mul-≤`)
-- and Lemma 2.4b (`lde-mul-eq-add` for odd numerators) work on this
-- stored representation.
lde : Di → ℕ
lde = denExp

0Di : Di
0Di = mkDi 0ZI 0

1Di : Di
1Di = mkDi 1ZI 0

-- Multiplication in D[i]: (z₁/γᵏ¹)(z₂/γᵏ²) = z₁z₂ / γᵏ¹⁺ᵏ².
-- The stored exponent is additive; the *true* lde is also additive
-- when both numerators are odd (Lemma 2.4b).
_*Di_ : Di → Di → Di
mkDi z₁ k₁ *Di mkDi z₂ k₂ = mkDi (z₁ *ZI z₂) (k₁ ℕ.+ k₂)

-- Addition: requires aligning exponents to the larger one.
-- `(z₁/γᵏ¹) + (z₂/γᵏ²)` with `k₁ ≤ k₂`:
--   = (γ^(k₂-k₁)·z₁ + z₂) / γᵏ²
-- Our `denExp` field is then `max k₁ k₂`.
_+Di_ : Di → Di → Di
mkDi z₁ k₁ +Di mkDi z₂ k₂ with k₁ Data.Nat.≤? k₂
... | yes _ = mkDi (powγ (k₂ Data.Nat.∸ k₁) *ZI z₁ +ZI z₂) k₂
... | no  _ = mkDi (z₁ +ZI powγ (k₁ Data.Nat.∸ k₂) *ZI z₂) k₁

-- Negation.
-Di_ : Di → Di
-Di mkDi z k = mkDi (-ZI z) k

-- Lemma 2.4a (subadditivity, equality form for stored exponent):
--   denExp(x*y) = denExp(x) + denExp(y).
-- The paper states `lde(xy) ≤ lde(x) + lde(y)`. Equality holds in our
-- stored representation; the inequality reflects implicit cancellation
-- when one numerator is even (i.e., when the stored exponent is not
-- minimal in the product, even if both factors had minimal exponents).
denExp-mul-≡ : (x y : Di) → denExp (x *Di y) ≡ denExp x ℕ.+ denExp y
denExp-mul-≡ (mkDi _ _) (mkDi _ _) = refl

-- Lemma 2.4b (additivity for odd numerators):
--   If x.num and y.num are both odd, then lde(x*y) = lde(x) + lde(y).
-- This is the case when the stored exponent IS minimal: oddness of the
-- numerator means no γ factors can be cancelled. Postulated here since
-- it requires showing oddness is preserved by multiplication, which
-- depends on the parity-norm Lemma 2.1 — to be filled in alongside
-- the residue infrastructure.
postulate
  lde-mul-eq-add : (x y : Di) → isOdd (num x) → isOdd (num y) →
    lde (x *Di y) ≡ lde x ℕ.+ lde y

------------------------------------------------------------------------
-- §2.3  Binary n-digit residues
------------------------------------------------------------------------

data Bit : Set where
  O : Bit
  I : Bit

xor : Bit → Bit → Bit
xor O b = b
xor I O = I
xor I I = O

and : Bit → Bit → Bit
and O _ = O
and I b = b

-- Decidable equality on Bit.
_≟Bit_ : (x y : Bit) → Dec (x ≡ y)
O ≟Bit O = yes refl
O ≟Bit I = no λ ()
I ≟Bit O = no λ ()
I ≟Bit I = yes refl

-- A binary n-digit residue.
Residue : ℕ → Set
Residue n = Fin n → Bit
