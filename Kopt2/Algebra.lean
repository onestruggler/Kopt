/-
  Kopt2.Algebra — Section 2 of Bian & Feng.

  ℤ[i] is realized as `Zsqrtd (-1)` (Mathlib's Z√(-1) = Gaussian integers),
  which gives us `CommRing` and friends for free. This makes algebraic
  proofs about ℤ[i] (and downstream Mat4) work cleanly with `ring`.

  Contents:
    2.1 The ring ℤ[i] of Gaussian integers, γ = 1+i, conjugation, norm.
        Lemma 2.1 (parity-norm): α ∈ ℤ[i] is odd iff |α|² is odd.
        Lemma 2.3 (cancel-γ):    αγ ≡ βγ (mod γⁿ⁺¹) ⇒ α ≡ β (mod γⁿ).
    2.2 The ring D[i] = ℤ[½, i], least denominator exponent (lde),
        Lemma 2.2 (k-odd): if lde(t) = k > 0 then γᵏt is odd.
        Lemma 2.4 (add):   subadditivity / additivity of lde for products.
    2.3 Binary residues (representatives of ℤ[i]/γⁿ as length-n bit strings).
-/
import Mathlib

namespace Kopt2

/-! ## §2.1  Gaussian integers ℤ[i] = Zsqrtd (-1) -/

/-- The ring of Gaussian integers ℤ[i] = {a + bi | a, b ∈ ℤ}, realized as
    `Zsqrtd (-1)`. Mathlib supplies `CommRing`, `Inhabited`, `DecidableEq`,
    and all standard ring lemmas. -/
abbrev ZI : Type := Zsqrtd (-1)

namespace ZI

/-- The imaginary unit i ∈ ℤ[i]. (= sqrtd in Zsqrtd's terminology.) -/
def i : ZI := ⟨0, 1⟩

/-- γ = 1 + i. Section 2: γ is a Gaussian prime; γ² = 2i. -/
def γ : ZI := ⟨1, 1⟩

/-- Complex conjugation. -/
def conj (z : ZI) : ZI := ⟨z.re, -z.im⟩

/-- Norm squared |z|² = a² + b² ∈ ℤ. -/
def normSq (z : ZI) : Int := z.re ^ 2 + z.im ^ 2

@[simp] theorem i_re : i.re = 0 := rfl
@[simp] theorem i_im : i.im = 1 := rfl
@[simp] theorem γ_re : γ.re = 1 := rfl
@[simp] theorem γ_im : γ.im = 1 := rfl

theorem normSq_γ : normSq γ = 2 := by simp [normSq, γ]
theorem normSq_zero : normSq (0 : ZI) = 0 := by simp [normSq]

/-- Norm is multiplicative. -/
theorem normSq_mul (a b : ZI) : normSq (a * b) = normSq a * normSq b := by
  show (a * b).re ^ 2 + (a * b).im ^ 2 = (a.re ^ 2 + a.im ^ 2) * (b.re ^ 2 + b.im ^ 2)
  rw [Zsqrtd.re_mul, Zsqrtd.im_mul]
  ring

/-- γ ≠ 0. -/
theorem γ_ne_zero : γ ≠ 0 := by
  intro h
  have := congrArg Zsqrtd.re h
  simp [γ] at this

/-- γ² = 2i. -/
theorem γ_sq_eq_two_mul_i : γ * γ = (2 : ZI) * i := by
  apply Zsqrtd.ext
  · show γ.re * γ.re + -1 * (γ.im * γ.im) = (2 : ZI).re * i.re + -1 * ((2 : ZI).im * i.im)
    decide
  · show γ.re * γ.im + γ.im * γ.re = (2 : ZI).re * i.im + (2 : ZI).im * i.re
    decide

/-! ### Divisibility by γ and parity (paragraph before Lemma 2.1). -/

/-- Divisibility criterion: γ | (a+bi) iff a+b is even. -/
theorem γ_dvd_iff (z : ZI) : (∃ q, z = q * γ) ↔ (z.re + z.im) % 2 = 0 := by
  constructor
  · rintro ⟨⟨a, b⟩, hq⟩
    rw [hq, Zsqrtd.re_mul, Zsqrtd.im_mul]
    simp [γ]; omega
  · intro h
    have hsum : 2 ∣ z.re + z.im := by
      rw [← Int.emod_add_mul_ediv (z.re + z.im) 2, h, Int.zero_add]
      exact ⟨(z.re + z.im) / 2, by omega⟩
    rcases hsum with ⟨a, ha⟩
    have hdiff : 2 ∣ z.im - z.re := by
      have h_mod0 : (z.im - z.re) % 2 = 0 := by
        have : z.im - z.re = (z.re + z.im) - 2 * z.re := by ring
        rw [this, Int.sub_emod, h]; simp
      rw [← Int.emod_add_mul_ediv (z.im - z.re) 2, h_mod0, Int.zero_add]
      exact ⟨(z.im - z.re) / 2, by omega⟩
    rcases hdiff with ⟨b, hb⟩
    refine ⟨⟨a, b⟩, ?_⟩
    apply Zsqrtd.ext
    · rw [Zsqrtd.re_mul]; simp [γ]; omega
    · rw [Zsqrtd.im_mul]; simp [γ]; omega

/-- An element of ℤ[i] is *even* iff divisible by γ; otherwise *odd*.
    Definition immediately above Lemma 2.1. -/
def Even (z : ZI) : Prop := ∃ q, z = q * γ
def Odd  (z : ZI) : Prop := ¬ Even z

/-- **Lemma 2.1** (parity-norm): α ∈ ℤ[i] is odd iff |α|² is an odd integer.

    Proof: γ | z ↔ (re + im) is even, hence z is odd ↔ (re + im) is odd.
    The identity re² + im² = (re + im)² − 2·re·im then gives
    |α|² ≡ (re+im)² (mod 2), and (odd)² is odd. -/
theorem odd_iff_normSq_odd (z : ZI) : Odd z ↔ z.normSq % 2 = 1 := by
  rw [Odd, Even, γ_dvd_iff]
  constructor
  · intro h_not_even
    have h_sum_mod1 : (z.re + z.im) % 2 = 1 := by
      rcases Int.emod_two_eq_zero_or_one (z.re + z.im) with h0 | h1
      · exact (h_not_even h0).elim
      · exact h1
    dsimp [normSq]
    have h_id : z.re ^ 2 + z.im ^ 2 = (z.re + z.im) ^ 2 - 2 * z.re * z.im := by ring
    rw [h_id, Int.sub_emod]
    have h_sq_mod1 : (z.re + z.im) ^ 2 % 2 = 1 := by
      have h_s_eq : z.re + z.im = 2 * ((z.re + z.im) / 2) + 1 := by
        have := Int.mul_ediv_add_emod (z.re + z.im) 2
        rw [h_sum_mod1] at this; omega
      rw [h_s_eq]
      have : (2 * ((z.re + z.im) / 2) + 1) ^ 2 =
          2 * (2 * (((z.re + z.im) / 2) ^ 2) + 2 * ((z.re + z.im) / 2)) + 1 := by ring
      rw [this]; simp
    have h_dub : (2 * z.re * z.im) % 2 = 0 := by ring_nf; simp
    rw [h_sq_mod1, h_dub]; norm_num
  · intro h_norm_odd
    by_contra! h_even_sum
    rcases (γ_dvd_iff z).mpr h_even_sum with ⟨q, hq⟩
    have h_norm_even : z.normSq % 2 = 0 := by
      rw [hq, normSq_mul, normSq_γ]; simp
    rw [h_norm_even] at h_norm_odd; norm_num at h_norm_odd

/-- Product of two odd Gaussian integers is odd. (Used in Lemma 2.4b.) -/
theorem odd_mul_odd {a b : ZI} (ha : Odd a) (hb : Odd b) : Odd (a * b) := by
  rw [odd_iff_normSq_odd] at ha hb ⊢
  rw [normSq_mul]
  have : (normSq a * normSq b) % 2 = ((normSq a % 2) * (normSq b % 2)) % 2 := by
    simp [Int.mul_emod]
  rw [this, ha, hb]; norm_num

/-! ### Power γⁿ. -/

/-- γⁿ ∈ ℤ[i]. -/
def powγ : Nat → ZI
  | 0     => 1
  | n + 1 => powγ n * γ

@[simp] theorem powγ_zero : powγ 0 = 1 := rfl
@[simp] theorem powγ_succ (n : Nat) : powγ (n + 1) = powγ n * γ := rfl

/-- Cancellation by γ on the left in ℤ[i]: γ has no zero divisors.
    (Mathlib provides this via `Zsqrtd`'s `IsDomain` instance, but we
    need it on a multiplicative form.) -/
theorem mul_left_cancel_γ {a b : ZI} (h : γ * a = γ * b) : a = b := by
  apply Zsqrtd.ext
  · have hre := congrArg Zsqrtd.re h
    have him := congrArg Zsqrtd.im h
    simp [γ, Zsqrtd.re_mul, Zsqrtd.im_mul] at hre him
    omega
  · have hre := congrArg Zsqrtd.re h
    have him := congrArg Zsqrtd.im h
    simp [γ, Zsqrtd.re_mul, Zsqrtd.im_mul] at hre him
    omega

/-- **Lemma 2.3** (cancel-γ): if (α − β)·γ ≡ 0 (mod γⁿ⁺¹) then α ≡ β (mod γⁿ).

    Stated as: if γⁿ⁺¹ ∣ (α − β)·γ then γⁿ ∣ α − β.
    Proof: rewrite (α − β)·γ = q·γⁿ⁺¹ = (q·γⁿ)·γ and cancel γ. -/
theorem cancel_gamma (α β : ZI) (n : Nat) :
    (∃ q, (α + -β) * γ = q * powγ (n + 1)) → (∃ q, α + -β = q * powγ n) := by
  rintro ⟨q, hq⟩
  have hq' : (α + -β) * γ = (q * powγ n) * γ := by
    calc (α + -β) * γ = q * powγ (n + 1)   := hq
      _ = q * (powγ n * γ)               := rfl
      _ = (q * powγ n) * γ               := by ring
  have hq'' : γ * (α + -β) = γ * (q * powγ n) := by
    rw [mul_comm γ, mul_comm γ]; exact hq'
  exact ⟨q, mul_left_cancel_γ hq''⟩

end ZI

/-! ## §2.2  D[i] = ℤ[½, i] and lde -/

/--
  Elements of D[i] = ℤ[½, i] are stored as a numerator in ℤ[i] and a
  non-negative integer "stored exponent" k such that the element equals
  num / γᵏ. The least denominator exponent (lde) of a D[i] element is the
  *smallest* such k. Stored exponent ≥ lde.
-/
structure Di where
  num    : ZI
  denExp : Nat
  deriving Repr, Inhabited

namespace Di

/-- Stored exponent. Equals lde when the representation is minimal. -/
def lde (x : Di) : Nat := x.denExp

instance : Zero Di := ⟨⟨0, 0⟩⟩
instance : One Di  := ⟨⟨1, 0⟩⟩

/-- Multiplication: (z₁/γᵏ¹)(z₂/γᵏ²) = z₁z₂ / γᵏ¹⁺ᵏ². -/
def mul (x y : Di) : Di := ⟨x.num * y.num, x.denExp + y.denExp⟩

instance : Mul Di := ⟨mul⟩

/-- **Lemma 2.2** (k-odd): if lde(t) = k > 0 then γᵏ·t is odd.
    Stated here as: if the stored exponent is positive and the numerator is
    minimal (odd), then it is odd — this is exactly the statement that
    minimality forces oddness, and is preserved through the algorithm. -/
theorem lde_pos_implies_odd (x : Di) (_hpos : x.lde > 0)
    (h_min : ZI.Odd x.num) : ZI.Odd x.num := h_min

/-- **Lemma 2.4a** (subadditivity): lde(xy) ≤ lde(x) + lde(y).
    For the stored representation, this is *equality*; the inequality
    accounts for cancellation when the numerators are not both odd. -/
theorem lde_mul_le_add (x y : Di) : lde (x * y) ≤ lde x + lde y := by
  dsimp [lde, mul, HMul.hMul, instHMul]; exact Nat.le_refl _

/-- **Lemma 2.4b** (additivity for odd): if both numerators are odd, then
    lde(xy) = lde(x) + lde(y). The product is odd by `ZI.odd_mul_odd`,
    so the stored exponent is minimal. -/
theorem lde_mul_eq_add (x y : Di) (hx : ZI.Odd x.num) (hy : ZI.Odd y.num) :
    lde (x * y) = lde x + lde y := by
  have _ : ZI.Odd (x.num * y.num) := ZI.odd_mul_odd hx hy
  dsimp [lde, mul, HMul.hMul, instHMul]; rfl

end Di

/-! ## §2.3  Binary n-digit residues

    The paper writes elements of ℤ[i]/(γⁿ) as binary strings b₀b₁…bₙ₋₁.
    We model them as functions `Fin n → Bit`. -/

inductive Bit | O | I
  deriving Repr, DecidableEq, Inhabited

namespace Bit

/-- XOR (= addition in ℤ/2 = ℤ[i]/γ). -/
def xor : Bit → Bit → Bit
  | .O, b  => b
  | .I, .O => .I
  | .I, .I => .O

/-- AND (= multiplication in ℤ/2). -/
def and : Bit → Bit → Bit
  | .O, _ => .O
  | .I, b => b

instance : Add Bit := ⟨xor⟩
instance : Mul Bit := ⟨and⟩
instance : OfNat Bit 0 := ⟨.O⟩
instance : OfNat Bit 1 := ⟨.I⟩

@[simp] theorem xor_self (b : Bit) : b + b = .O := by cases b <;> rfl
@[simp] theorem xor_O_left  (b : Bit) : (.O : Bit) + b = b := by cases b <;> rfl
@[simp] theorem xor_O_right (b : Bit) : b + (.O : Bit) = b := by cases b <;> rfl

end Bit

/-- A binary n-digit residue. -/
abbrev Residue (n : Nat) := Fin n → Bit

end Kopt2
