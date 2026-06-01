/-
  Kopt.Lde — Section 4's input class: matrices over D[i] with bookkeeping
  for the least denominator exponent.

  In the paper, A ∈ Clifford+CS is a 4×4 unitary with entries in D[i] = ℤ[½, i].
  We model A by storing its **scaled** numerator γ^l · A as a matrix over ℤ[i],
  together with a non-negative integer l = lde(A). Multiplication is
  γ^(l₁+l₂) · (A·B) = (γ^l₁ A)·(γ^l₂ B), which keeps numerators in ℤ[i] and
  exponents additive.

  The pattern of A is `ρ₁ˡ(A)` (`Pattern.residue1`) up to row/column
  permutation. We model it abstractly as a `Pattern` field, since the
  precise pattern depends on which permutations are chosen — this matches
  the paper's "for some L, R, ρ₁ˡ(LAR) = pattern P" formulation.
-/
import Kopt.Synthesis
import Kopt.Cliffords

namespace Kopt

open Kopt

/-! ## Matrices over D[i], represented by (numerator in ℤ[i], lde). -/

/--
  A 4×4 unitary over D[i], represented by its scaled numerator (a `Mat4` over
  ℤ[i]) together with the lde exponent `l ≥ 0`. The actual matrix is
  `numerator / γ^l`.

  We additionally carry the residue pattern `pat` of `ρ₁ˡ(A)` (after
  appropriate L, R permutations from Lemma 4.1).

  **Lemma 4.1 invariant** (`hpat_I_iff_l_zero`): the pattern is I iff the
  lde is 0. This is part of the *type* of a UnitaryDi, so any well-formed
  `UnitaryDi` automatically satisfies it. -/
structure UnitaryDi where
  numerator : Mat4
  l         : Nat
  pat       : Pattern
  /-- Lemma 4.1 invariant: pattern I iff lde 0. -/
  hpat_I_iff_l_zero : pat = Pattern.I ↔ l = 0

instance : Inhabited UnitaryDi where
  default :=
    { numerator := Mat4.id, l := 0, pat := Pattern.I,
      hpat_I_iff_l_zero := ⟨fun _ => rfl, fun _ => rfl⟩ }

namespace UnitaryDi

/-- The scaled-down lde of a UnitaryDi value. -/
def lde (A : UnitaryDi) : Nat := A.l

/-- The pattern of A. -/
def pattern (A : UnitaryDi) : Pattern := A.pat

/-- Lemma 4.1, ⇒ direction: pattern I implies lde 0. -/
theorem pat_I_imp_l_zero (A : UnitaryDi) (h : A.pat = Pattern.I) : A.l = 0 :=
  A.hpat_I_iff_l_zero.mp h

/-- Lemma 4.1, ⇐ direction: lde 0 implies pattern I. -/
theorem l_zero_imp_pat_I (A : UnitaryDi) (h : A.l = 0) : A.pat = Pattern.I :=
  A.hpat_I_iff_l_zero.mpr h

/-- Lemma 4.1 packaged: pat = I ↔ l = 0. -/
theorem pat_I_iff_l_zero (A : UnitaryDi) : A.pat = Pattern.I ↔ A.l = 0 :=
  A.hpat_I_iff_l_zero

/-- Lemma 4.1 contrapositive: pat ≠ I implies l > 0. -/
theorem pat_ne_I_imp_l_pos (A : UnitaryDi) (h : A.pat ≠ Pattern.I) : A.l > 0 := by
  rcases Nat.eq_zero_or_pos A.l with h0 | hp
  · exact absurd (l_zero_imp_pat_I A h0) h
  · exact hp

end UnitaryDi

/-! ## §5  Definition 5.1: optimal counts -/

/-- A is K-optimal at k iff there is a circuit implementing A with exactly
    k K gates and no circuit implementing A uses fewer K gates. -/
def IsKCOptimal (A : Mat4) (k : Nat) : Prop :=
  (∃ c : Circuit, Circuit.eval c = A ∧ Circuit.rkc c = k) ∧
  (∀ c : Circuit, Circuit.eval c = A → k ≤ Circuit.rkc c)

/-- CS-optimality predicate. -/
def IsCSOptimal (A : Mat4) (k : Nat) : Prop :=
  (∃ c : Circuit, Circuit.eval c = A ∧ Circuit.rcs c = k) ∧
  (∀ c : Circuit, Circuit.eval c = A → k ≤ Circuit.rcs c)

/-- Length-optimality predicate. -/
def IsLenOptimal (A : Mat4) (k : Nat) : Prop :=
  (∃ c : Circuit, Circuit.eval c = A ∧ Circuit.rlen c = k) ∧
  (∀ c : Circuit, Circuit.eval c = A → k ≤ Circuit.rlen c)

end Kopt
