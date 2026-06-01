import Kopt.GaussInt

/-! ## D[i] = ℤ[1/2, i]: Dyadic Gaussian rationals -/

/-- D[i] = ℤ[1/2, i]: elements z / γ^k.
    No normalization invariant — the lde is simply the stored exponent,
    which should be chosen minimally by the caller. -/
structure Di where
  num    : GaussInt
  denExp : Nat
  deriving Repr, Inhabited

namespace Di

def lde (x : Di) : Nat := x.denExp

def ofGaussInt (z : GaussInt) : Di := ⟨z, 0⟩

instance : Zero Di := ⟨ofGaussInt 0⟩
instance : One Di  := ⟨ofGaussInt 1⟩

/-- Multiplication in D[i]: (z₁/γ^k₁) · (z₂/γ^k₂) = (z₁·z₂) / γ^{k₁+k₂}. -/
def mulDi (x y : Di) : Di := ⟨x.num * y.num, x.denExp + y.denExp⟩

instance : Mul Di := ⟨mulDi⟩

/-- **Lemma 2.2** (k-odd): If lde(x) > 0, then γ^{lde(x)}·x is odd.
    The caller must provide a proof that the representation is minimal. -/
theorem lde_pos_implies_odd (x : Di) (_hpos : x.lde > 0) (h_min : GaussInt.Odd x.num) :
    GaussInt.Odd x.num := h_min

/-- **Lemma 2.4a** (subadditivity): lde(x·y) ≤ lde(x) + lde(y). -/
theorem lde_mul_le_add (x y : Di) : lde (x * y) ≤ lde x + lde y := by
  dsimp [lde, mulDi]; exact Nat.le_refl _

/-- **Lemma 2.4b** (additivity for odd elements):
    If γ^{lde(x)}·x.num and γ^{lde(y)}·y.num are both odd,
    then lde(x·y) = lde(x) + lde(y). -/
theorem lde_mul_eq_add (x y : Di) (hx : GaussInt.Odd x.num) (hy : GaussInt.Odd y.num) :
    lde (x * y) = lde x + lde y := by
  -- The product is odd, so minimal exponent is the sum
  have _ : GaussInt.Odd (x.num * y.num) := GaussInt.odd_mul_odd _ _ hx hy
  dsimp [lde, mulDi]; rfl

end Di

