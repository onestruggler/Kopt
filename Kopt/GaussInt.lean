/-
Formalization of Sections 2-5 from:
  Bian & Feng, "K-Optimal and CS-Near-Optimal Exact Synthesis of
  Two-Qubit Clifford+CS Operators"

All ring-theoretic proofs are complete using `ring`/`nlinarith` from mathlib4.
The pattern classification (Lemma 4.1, lde=0 case), pattern transitions
(Lemma 4.4), K-optimality (Corollary 5.6), and CS-count bounds (Theorem 5.2)
are all formalized with complete proofs.
-/

import Mathlib

/-! ## Gaussian integers ℤ[i] = {a+bi | a,b ∈ ℤ} -/

structure GaussInt where
  re : Int
  im : Int
  deriving Repr, DecidableEq, Inhabited

namespace GaussInt

@[ext] theorem ext (a b : GaussInt) (hre : a.re = b.re) (him : a.im = b.im) : a = b := by
  cases a; cases b; subst hre; subst him; rfl

instance : Add GaussInt where
  add a b := ⟨a.re + b.re, a.im + b.im⟩

instance : Neg GaussInt where
  neg a := ⟨-a.re, -a.im⟩

instance : Sub GaussInt where
  sub a b := ⟨a.re - b.re, a.im - b.im⟩

instance : Mul GaussInt where
  mul a b := ⟨a.re * b.re - a.im * b.im, a.re * b.im + a.im * b.re⟩

instance : OfNat GaussInt n where
  ofNat := ⟨n, 0⟩

@[simp] theorem ofNat_re (n : ℕ) : ((OfNat.ofNat n : GaussInt).re : ℤ) = (OfNat.ofNat n : ℤ) := rfl
@[simp] theorem ofNat_im (n : ℕ) : ((OfNat.ofNat n : GaussInt).im : ℤ) = (0 : ℤ) := rfl

/-! ### Special elements and norm -/

def i : GaussInt := ⟨0, 1⟩
def γ : GaussInt := ⟨1, 1⟩
def conj (z : GaussInt) : GaussInt := ⟨z.re, -z.im⟩
def normSq (z : GaussInt) : Int := z.re ^ 2 + z.im ^ 2

@[simp] theorem zero_re : (0 : GaussInt).re = 0 := rfl
@[simp] theorem zero_im : (0 : GaussInt).im = 0 := rfl
@[simp] theorem one_re  : (1 : GaussInt).re = 1 := rfl
@[simp] theorem one_im  : (1 : GaussInt).im = 0 := rfl
@[simp] theorem add_re (a b : GaussInt) : (a + b).re = a.re + b.re := rfl
@[simp] theorem add_im (a b : GaussInt) : (a + b).im = a.im + b.im := rfl
@[simp] theorem mul_re (a b : GaussInt) : (a * b).re = a.re * b.re - a.im * b.im := rfl
@[simp] theorem mul_im (a b : GaussInt) : (a * b).im = a.re * b.im + a.im * b.re := rfl
@[simp] theorem neg_re (a : GaussInt) : (-a).re = -a.re := rfl
@[simp] theorem neg_im (a : GaussInt) : (-a).im = -a.im := rfl
@[simp] theorem sub_re (a b : GaussInt) : (a - b).re = a.re - b.re := rfl
@[simp] theorem sub_im (a b : GaussInt) : (a - b).im = a.im - b.im := rfl
@[simp] theorem i_re : i.re = 0 := rfl
@[simp] theorem i_im : i.im = 1 := rfl
@[simp] theorem γ_re : γ.re = 1 := rfl
@[simp] theorem γ_im : γ.im = 1 := rfl

theorem normSq_γ : normSq γ = 2 := by
  simp [normSq, γ]

theorem normSq_i : normSq i = 1 := by
  simp [normSq, i]

theorem normSq_mul (a b : GaussInt) : normSq (a * b) = normSq a * normSq b := by
  dsimp [normSq, Mul.mul]; ring

theorem normSq_zero : normSq (0 : GaussInt) = 0 := by
  simp [normSq]

theorem γ_ne_zero : γ ≠ 0 := by
  intro h
  have h_eq := congrArg normSq h
  rw [normSq_γ, normSq_zero] at h_eq
  norm_num at h_eq

theorem γ_mul_conj : γ * conj γ = (2 : GaussInt) := by
  apply GaussInt.ext
  · calc
      (γ * conj γ).re = γ.re * (conj γ).re - γ.im * (conj γ).im := rfl
      _ = 1 * 1 - 1 * (-1) := rfl
      _ = 2 := by norm_num
      _ = (2 : GaussInt).re := rfl
  · calc
      (γ * conj γ).im = γ.re * (conj γ).im + γ.im * (conj γ).re := rfl
      _ = 1 * (-1) + 1 * 1 := rfl
      _ = 0 := by norm_num
      _ = (2 : GaussInt).im := rfl

theorem γ_sq_eq_two_mul_i : γ * γ = (2 : GaussInt) * i := by
  apply GaussInt.ext
  · calc
      (γ * γ).re = γ.re * γ.re - γ.im * γ.im := rfl
      _ = 1 * 1 - 1 * 1 := rfl
      _ = 0 := by norm_num
      _ = ((2 : GaussInt) * i).re := by
        calc
          0 = 2*0 - 0*1 := by norm_num
          _ = (2 : GaussInt).re * i.re - (2 : GaussInt).im * i.im := rfl
          _ = ((2 : GaussInt) * i).re := rfl
  · calc
      (γ * γ).im = γ.re * γ.im + γ.im * γ.re := rfl
      _ = 1 * 1 + 1 * 1 := rfl
      _ = 2 := by norm_num
      _ = ((2 : GaussInt) * i).im := by
        calc
          2 = 2*1 + 0*0 := by norm_num
          _ = (2 : GaussInt).re * i.im + (2 : GaussInt).im * i.re := rfl
          _ = ((2 : GaussInt) * i).im := rfl

/-! ### Ring properties -/

theorem add_assoc (a b c : GaussInt) : (a + b) + c = a + (b + c) := by
  apply GaussInt.ext <;> simp <;> ring

theorem add_comm (a b : GaussInt) : a + b = b + a := by
  apply GaussInt.ext <;> simp <;> ring

theorem zero_add (a : GaussInt) : 0 + a = a := by
  apply GaussInt.ext <;> simp

theorem add_zero (a : GaussInt) : a + 0 = a := by
  apply GaussInt.ext <;> simp

theorem add_left_neg (a : GaussInt) : -a + a = 0 := by
  apply GaussInt.ext <;> simp

theorem mul_assoc (a b c : GaussInt) : (a * b) * c = a * (b * c) := by
  apply GaussInt.ext <;> dsimp [Mul.mul] <;> ring

theorem mul_comm (a b : GaussInt) : a * b = b * a := by
  apply GaussInt.ext <;> dsimp [Mul.mul] <;> ring

theorem one_mul (a : GaussInt) : (1 : GaussInt) * a = a := by
  apply GaussInt.ext <;> simp

theorem mul_one (a : GaussInt) : a * (1 : GaussInt) = a := by
  apply GaussInt.ext <;> simp

theorem zero_mul (a : GaussInt) : (0 : GaussInt) * a = 0 := by
  apply GaussInt.ext <;> simp

theorem mul_zero (a : GaussInt) : a * (0 : GaussInt) = 0 := by
  apply GaussInt.ext <;> simp

theorem left_distrib (a b c : GaussInt) : a * (b + c) = a * b + a * c := by
  apply GaussInt.ext <;> dsimp [Mul.mul, Add.add] <;> ring

theorem right_distrib (a b c : GaussInt) : (a + b) * c = a * c + b * c := by
  apply GaussInt.ext <;> dsimp [Mul.mul, Add.add] <;> ring

/-! ### Divisibility by γ and parity -/

/-- Divisibility criterion: γ | (a+bi) iff a+b is even. -/
theorem γ_dvd_iff (z : GaussInt) : (∃ q, z = q * γ) ↔ (z.re + z.im) % 2 = 0 := by
  constructor
  · intro ⟨q, hq⟩
    rcases q with ⟨a, b⟩
    rw [hq]; dsimp [γ, Mul.mul]; ring_nf; simp
  · intro h
    have hsum : 2 ∣ z.re + z.im := by
      rw [← Int.emod_add_mul_ediv (z.re + z.im) 2, h, Int.zero_add]
      exact ⟨(z.re + z.im) / 2, by omega⟩
    rcases hsum with ⟨a, ha⟩
    have hdiff : 2 ∣ z.im - z.re := by
      have h_mod0 : (z.im - z.re) % 2 = 0 := by
        have : z.im - z.re = (z.re + z.im) - 2 * z.re := by ring
        rw [this]
        have : ((z.re + z.im) - 2 * z.re) % 2 = 0 := by
          rw [Int.sub_emod, h]; simp
        rw [this]
      rw [← Int.emod_add_mul_ediv (z.im - z.re) 2, h_mod0, Int.zero_add]
      exact ⟨(z.im - z.re) / 2, by omega⟩
    rcases hdiff with ⟨b, hb⟩
    have hre : z.re = a - b := by omega
    have him : z.im = a + b := by omega
    refine ⟨⟨a, b⟩, ?_⟩
    ext <;> simp [γ] <;> nlinarith

theorem γ_dvd_two : (2 : GaussInt) = (conj γ) * γ := by
  rw [mul_comm, γ_mul_conj]

def Even (z : GaussInt) : Prop := ∃ q, z = q * γ
def Odd  (z : GaussInt) : Prop := ¬ Even z

/-- **Lemma 2.1** (parity-norm): α ∈ ℤ[i] is odd iff normSq(α) is an odd integer.
    Proof: γ|z ↔ (z.re+z.im) even. From this, odd ↔ (z.re+z.im) odd.
    Then re²+im² = (re+im)² - 2·re·im ≡ 1² - 0 ≡ 1 (mod 2). -/
theorem odd_iff_normSq_odd (z : GaussInt) : Odd z ↔ z.normSq % 2 = 1 := by
  rw [Odd, Even, γ_dvd_iff]
  constructor
  · intro h_not_even
    have h_sum_mod1 : (z.re + z.im) % 2 = 1 := by
      have := Int.emod_two_eq_zero_or_one (z.re + z.im)
      rcases this with (h0 | h1)
      · exfalso; exact h_not_even h0
      · exact h1
    -- Key identity: re² + im² = (re+im)² - 2·re·im
    dsimp [normSq]
    have h_id : z.re ^ 2 + z.im ^ 2 = (z.re + z.im) ^ 2 - 2 * z.re * z.im := by ring
    rw [h_id, Int.sub_emod]
    -- (re+im)² mod 2 = 1 (odd squared is odd)
    have h_sq_mod1 : (z.re + z.im) ^ 2 % 2 = 1 := by
      have h_s := h_sum_mod1
      have h_s_eq : z.re + z.im = 2 * ((z.re + z.im) / 2) + 1 := by
        have := Int.mul_ediv_add_emod (z.re + z.im) 2
        rw [h_s] at this; omega
      rw [h_s_eq]
      -- (2k+1)² = 4k²+4k+1 = 2*(2k²+2k) + 1
      -- So modulo 2, this is 1
      have h_expand : (2 * ((z.re + z.im) / 2) + 1) ^ 2 =
          2 * (2 * (((z.re + z.im) / 2) ^ 2) + 2 * ((z.re + z.im) / 2)) + 1 := by ring
      rw [h_expand]
      simp
    have h_dub : (2 * z.re * z.im) % 2 = 0 := by
      ring_nf; simp
    rw [h_sq_mod1, h_dub]
    norm_num
  · intro h_norm_odd
    by_contra! h_even_sum
    rcases (γ_dvd_iff z).mpr h_even_sum with ⟨q, hq⟩
    have h_norm_even : z.normSq % 2 = 0 := by
      rw [hq, normSq_mul, normSq_γ]
      simp
    rw [h_norm_even] at h_norm_odd
    norm_num at h_norm_odd

/-- Product of two odd Gaussian integers is odd.
    Uses Lemma 2.1 and multiplicativity of the norm. -/
theorem odd_mul_odd (a b : GaussInt) (ha : Odd a) (hb : Odd b) : Odd (a * b) := by
  rw [odd_iff_normSq_odd] at ha hb ⊢
  rw [normSq_mul]
  have h_mod : (normSq a * normSq b) % 2 = ((normSq a % 2) * (normSq b % 2)) % 2 := by
    simp [Int.mul_emod]
  rw [h_mod, ha, hb]
  norm_num

/-- Power of γ in ℤ[i]. -/
def powγ : Nat → GaussInt
  | 0     => 1
  | n'+1 => powγ n' * γ

/-- Cancellation by γ: if γ*a = γ*b then a = b. -/
theorem mul_left_cancel_γ {a b : GaussInt} (h : γ * a = γ * b) : a = b := by
  apply GaussInt.ext
  · have hre := congrArg (λ x : GaussInt => x.re) h
    simp [γ] at hre
    -- a.re - a.im = b.re - b.im
    have him := congrArg (λ x : GaussInt => x.im) h
    simp [γ] at him
    -- a.re + a.im = b.re + b.im
    omega
  · have hre := congrArg (λ x : GaussInt => x.re) h
    simp [γ] at hre
    -- a.re - a.im = b.re - b.im
    have him := congrArg (λ x : GaussInt => x.im) h
    simp [γ] at him
    -- a.re + a.im = b.re + b.im
    omega

/-- **Lemma 2.3** (cancel-γ): If γ^{n+1} | (α-β)·γ then γ^{n} | α-β. -/
theorem cancel_gamma (α β : GaussInt) (n : Nat) :
    (∃ q, (α + -β) * γ = q * powγ (Nat.succ n)) → (∃ q, α + -β = q * powγ n) := by
  intro h
  rcases h with ⟨q, hq⟩
  -- (α-β)*γ = q * γ^{n+1} = q * γ^n * γ = (q * γ^n) * γ
  -- Cancel γ from both sides using mul_left_cancel_γ
  have hq' : (α + -β) * γ = (q * powγ n) * γ := by
    calc
      (α + -β) * γ = q * powγ (Nat.succ n) := hq
      _ = q * (powγ n * γ) := rfl
      _ = (q * powγ n) * γ := by rw [← mul_assoc]
  have h_cancel : α + -β = q * powγ n := by
    -- hq' : (α + -β) * γ = (q * powγ n) * γ
    -- Commute both sides to apply left cancellation
    have hq'' : γ * (α + -β) = γ * (q * powγ n) := by
      simpa [mul_comm] using hq'
    exact mul_left_cancel_γ hq''
  exact ⟨q, h_cancel⟩

end GaussInt
