/-
  Kopt.Optimality — Section 5 of Bian & Feng (CS-bound side).

  The K-optimality theorem (`is_kc_optimal`) and Lemma 4.6 (`lemma_4_6`)
  live in Kopt.Synth. This file packages the CS-bound side of §5
  (Theorem `thm:csbd`) and the asymptotic CS-near-optimal corollary.
-/
import Kopt.Synth

namespace Kopt

open Kopt

/-! ## §5  Theorem thm:csbd: kc/2 - 1 ≤ cs ≤ kc + 1

    Paper proof (recapped):
      (Upper bound) Every Clifford+CS operator A can be written as
        A = P₀·K₁·P₁·K₁·…·Pₙ
      (Equation `eq:ccs-k`), with each generalized permutation Pᵢ using ≤ 1
      CS gate and 0 K gates. Hence cs(A) ≤ rkc(A) + 1 ≤ kc(A) + 1.

      (Lower bound) Every Clifford+CS operator A can be written as
        A = C₀·CS·C₁·CS·…·Cₙ
      (Equation `eq:ccs`), with each Clifford part Cᵢ using ≤ 2 K gates
      (by enumeration over the finite Clifford group). Hence
        kc(A) ≤ 2·(rcs(A) + 1) ≤ 2·(cs(A) + 1)
      whence kc(A)/2 − 1 ≤ cs(A).

    We package the implications algebraically: given hypotheses about the
    structure of `A`'s decompositions, conclude the bound. -/

/-- (Theorem 5.2 upper bound, algebraic core.) If
      cs(A) ≤ rkc(c') + 1   for the synth circuit c'
    and rkc(c') ≤ kc(A) (which holds because c' implements A), then
      cs(A) ≤ kc(A) + 1. -/
theorem cs_upper_bound (A : Mat4) (kc cs : Nat)
    (h_kc : IsKCOptimal A kc) (h_cs : IsCSOptimal A cs)
    (h_synth_rcs : ∃ c', Circuit.eval c' = A ∧ Circuit.rcs c' ≤ kc + 1) :
    cs ≤ kc + 1 := by
  rcases h_synth_rcs with ⟨c', he, hrcs⟩
  have hge : cs ≤ Circuit.rcs c' := h_cs.2 c' he
  exact le_trans hge hrcs

/-- (Theorem 5.2 lower bound, algebraic core.) If kc(A) ≤ 2·(cs(A) + 1),
    then kc(A)/2 − 1 ≤ cs(A) (over Int, to handle the subtraction). -/
theorem cs_lower_bound (kc cs : Nat) (h : (kc : Int) ≤ 2 * ((cs : Int) + 1)) :
    (kc : Int) / 2 - 1 ≤ (cs : Int) := by omega

/-- (Theorem 5.2 packaged.) Given both hypotheses, we get
    `kc/2 − 1 ≤ cs ≤ kc + 1`. -/
theorem cs_bound (A : Mat4) (kc cs : Nat)
    (h_kc : IsKCOptimal A kc) (h_cs : IsCSOptimal A cs)
    (h_synth_rcs : ∃ c', Circuit.eval c' = A ∧ Circuit.rcs c' ≤ kc + 1)
    (h_clifford : (kc : Int) ≤ 2 * ((cs : Int) + 1)) :
    (kc : Int) / 2 - 1 ≤ (cs : Int) ∧ (cs : Int) ≤ (kc : Int) + 1 := by
  refine ⟨cs_lower_bound kc cs h_clifford, ?_⟩
  have h_upper : cs ≤ kc + 1 := cs_upper_bound A kc cs h_kc h_cs h_synth_rcs
  exact_mod_cast h_upper

/-! ## §5  Corollary 5.7 (CS-near-optimal): rcs / cs(A) ≤ 2 + 4/(k-2)

    From cs(A) ≥ k/2 − 1 (lower bound) and rcs(c') ≤ k + 1 (upper bound),
        rcs(c') / cs(A) ≤ (k + 1) / (k/2 − 1) = 2 + 4/(k − 2).
    So asymptotically rcs is at most 2× optimal. -/

/-- The CS upper bound (k+1) is at most 2·(k/2 − 1) + 4 for k ≥ 4, i.e.,
    rcs(synth) ≤ 2·cs(A) + 4 asymptotically. (We give the integer form,
    which avoids division.) -/
theorem cs_near_optimal_integer_form (k cs : Nat)
    (h_lower : (k : Int) / 2 - 1 ≤ (cs : Int))
    (h_upper : (cs : Int) ≤ (k : Int) + 1) :
    (k : Int) + 1 ≤ 2 * (cs : Int) + 4 := by omega

/-! ## §5  Corollary thm:main (achievability bookkeeping)

    For any non-I pattern p at lde l > 0, the synthesis produces a circuit
    with K-count exactly prkc(l, p), and total length at most 9·(prkc + 1) + prkc
    = 10·prkc + 9. We give the achievability layer here. -/

/-- The synth K-skeleton has rkc = prkc. -/
theorem synth_skeleton_rkc (l : Nat) (p : Pattern) :
    Circuit.rkc (synthKSkeleton l p) = Pattern.prkc l p :=
  synthKSkeleton_rkc l p

/-! ## Remark (l - 2 ≤ cs ≤ 2l + 1)

    Combining `cs_bound` with `prkc_le_two_l` (so kc ≤ 2l) gives the
    paper's remark immediately following Theorem `thm:csbd`. -/

theorem cs_bound_in_lde (A : Mat4) (l : Nat) (p : Pattern)
    (hp : p ≠ Pattern.I) (hpos : l > 0)
    (kc cs : Nat)
    (h_kc : IsKCOptimal A kc) (h_cs : IsCSOptimal A cs)
    (h_kc_eq_prkc : kc = Pattern.prkc l p)
    (h_synth_rcs : ∃ c', Circuit.eval c' = A ∧ Circuit.rcs c' ≤ kc + 1)
    (h_clifford : (kc : Int) ≤ 2 * ((cs : Int) + 1)) :
    (cs : Int) ≤ 2 * (l : Int) + 1 := by
  have hbnd := cs_bound A kc cs h_kc h_cs h_synth_rcs h_clifford
  -- cs ≤ kc + 1 ≤ 2l + 1
  have h_kc_le_2l : (kc : Int) ≤ 2 * (l : Int) := by
    rw [h_kc_eq_prkc]; exact_mod_cast Pattern.prkc_le_two_l l p
  omega

end Kopt
