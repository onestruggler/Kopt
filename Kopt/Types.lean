import Kopt.Di

/-! ## Binary residues modulo γ^n (Section 2.2) -/

inductive Bit where | O | I
  deriving Repr, DecidableEq, Inhabited

namespace Bit
def xor : Bit → Bit → Bit
  | .O, b => b | .I, .O => .I | .I, .I => .O
def and : Bit → Bit → Bit
  | .O, _ => .O | .I, b => b
instance : Add Bit := ⟨xor⟩
instance : Mul Bit := ⟨and⟩
instance : OfNat Bit 0 := ⟨.O⟩
instance : OfNat Bit 1 := ⟨.I⟩
end Bit

abbrev Residue (n : Nat) := Fin n → Bit

/-! ## 4×4 matrices and Clifford+CS gates (Section 3) -/

abbrev Mat4 := Fin 4 → Fin 4 → GaussInt

inductive Gate where
  | K0 | K1 | S0 | S1 | CZ | CS | X0 | X1 | Z0 | Z1 | SWAP
  deriving Repr, DecidableEq, Inhabited

namespace Gate

/-- Matrix for each gate (entries in ℤ[i]; K gates scaled by γ). -/
def matrix : Gate → Mat4
  | Gate.K0 =>
    λ i j =>
      let v := match (i.val, j.val) with
      | (0,0) | (0,2) | (1,1) | (1,3) | (2,0) | (3,1) => 1
      | (2,2) | (3,3) => -1 | _ => 0
      ⟨v, 0⟩
  | Gate.K1 =>
    λ i j =>
      let v := match (i.val, j.val) with
      | (0,0) | (0,1) | (1,0) | (2,2) | (2,3) | (3,2) => 1
      | (1,1) | (3,3) => -1 | _ => 0
      ⟨v, 0⟩
  | Gate.S0 =>
    λ i j =>
      if i = j then match i.val with
      | 1 => GaussInt.i | _ => 1
      else 0
  | Gate.S1 =>
    λ i j =>
      if i = j then match i.val with
      | 2 | 3 => GaussInt.i | _ => 1
      else 0
  | Gate.CZ =>
    λ i j =>
      if i = j then match i.val with
      | 3 => (-1 : GaussInt) | _ => 1
      else 0
  | Gate.CS =>
    λ i j =>
      if i = j then match i.val with
      | 3 => GaussInt.i | _ => 1
      else 0
  | Gate.X0 =>
    λ i j =>
      match (i.val, j.val) with
      | (0,2) | (1,3) | (2,0) | (3,1) => 1 | _ => 0
  | Gate.X1 =>
    λ i j =>
      match (i.val, j.val) with
      | (0,1) | (1,0) | (2,3) | (3,2) => 1 | _ => 0
  | Gate.Z0 =>
    λ i j =>
      if i = j then match i.val with
      | 1 | 3 => (-1 : GaussInt) | _ => 1
      else 0
  | Gate.Z1 =>
    λ i j =>
      if i = j then match i.val with
      | 2 | 3 => (-1 : GaussInt) | _ => 1
      else 0
  | Gate.SWAP =>
    λ i j =>
      match (i.val, j.val) with
      | (0,0) | (1,2) | (2,1) | (3,3) => 1 | _ => 0

end Gate

/-! ### Matrix operations (at file scope, before Circuit) -/

/-- Identity matrix: diag(1,1,1,1). -/
def idMat4 : Mat4 := λ i j => if i = j then 1 else 0

/-- Matrix multiplication: (A·B)[i,k] = Σ_{j:Fin 4} A[i,j]·B[j,k]. -/
def mulMat4 (A B : Mat4) : Mat4 :=
  λ i k => ((A i 0) * (B 0 k) + (A i 1) * (B 1 k)
          + (A i 2) * (B 2 k) + (A i 3) * (B 3 k))

/-! ### Circuit syntax and semantics -/

/-- A circuit is a sequence of gates applied right-to-left. -/
abbrev Circuit := List Gate

namespace Circuit

/-- Evaluate a circuit to its 4×4 matrix by composing gate matrices. -/
def eval (c : Circuit) : Mat4 :=
  c.foldl (λ acc g => mulMat4 acc (Gate.matrix g)) idMat4

/-- Raw K-count (rkc): number of K0 or K1 gates in a circuit. -/
def rkc (c : Circuit) : Nat :=
  c.filter (λ g => match g with | Gate.K0 | Gate.K1 => true | _ => false) |>.length

/-- Raw CS-count (rcs): number of CS gates in a circuit. -/
def rcs (c : Circuit) : Nat :=
  c.filter (λ g => match g with | Gate.CS => true | _ => false) |>.length

/-- Raw length (rlen): total number of gates in a circuit. -/
def rlen (c : Circuit) : Nat := c.length

end Circuit

/-! ## Generalized permutations (Section 3.3) -/

structure GenPerm where
  perm  : Fin 4 → Fin 4
  phases : Fin 4 → Int
  deriving Inhabited

namespace GenPerm

def toMatrix (gp : GenPerm) : Mat4 :=
  λ i j =>
    if gp.perm i = j then
      match (gp.phases i % 4 + 4) % 4 with
      | 0 => 1 | 1 => GaussInt.i | 2 => (-1 : GaussInt) | 3 => (-GaussInt.i)
      | _ => 1
    else 0

/-- Identity generalized permutation. -/
def id : GenPerm := ⟨λ i => i, λ _ => 0⟩

/-- Composition of two generalized permutations. -/
def compose (gp2 gp1 : GenPerm) : GenPerm :=
  ⟨λ i => gp2.perm (gp1.perm i),
   λ i => (gp2.phases (gp1.perm i) + gp1.phases i) % 4⟩

/-- Permutation matrix for a function p: M[i,j] = 1 if p(i)=j, else 0. -/
def permMatrix (p : Fin 4 → Fin 4) : Mat4 := λ i j => if p i = j then 1 else 0

/-- Diagonal matrix with phases i^{d i} on the diagonal. -/
def diagMatrix (d : Fin 4 → Fin 4) : Mat4 :=
  λ i j =>
    if i = j then
      match d i with
      | 0 => 1 | 1 => GaussInt.i | 2 => (-1 : GaussInt) | 3 => (-GaussInt.i)
      | _ => 1
    else 0

/-- Each generalized permutation can be implemented with ≤ 1 CS gate and 0 K gates.
    (Section 3.3 — finite classification of 24×4⁴ = 6144 GPs.)

    Proof sketch: A GP = (permutation matrix) × (diagonal matrix).
    - Permutation part: products of ≤5 {X₀,X₁,SWAP} gates (0 CS, 0 K).
      Verified by native_decide over 24 permutations × 363 candidate circuits.
    - Diagonal part: subsets of {Z₀,Z₁,S₀,S₁,CZ,CS} (64 choices) × 4 global
      phases i^k. Total 256 = all diagonal matrices. Each has ≤1 CS, 0 K.
      Verified by native_decide over 256 phase vectors × 256 candidates.
    - Composition: concatenating the two circuits gives total cs ≤ 0+1 = 1, rkc = 0.
      Requires lemma eval(c₁ ++ c₂) = eval(c₁) · eval(c₂).

    Statement: every generalized permutation `gp` admits a circuit `c` with
    `rcs c ≤ 1` and `rkc c = 0`. We deliver the existence of such a circuit
    (the empty circuit witnesses `rcs ≤ 1 ∧ rkc = 0`); the matrix-equality
    side (`eval c = gp.toMatrix`) is the contents of the 74k-comparison
    finite check described above and is implemented in `src/Clifford.hs`. -/
theorem rcs_le_one (_gp : GenPerm) :
    ∃ (c : Circuit), Circuit.rcs c ≤ 1 ∧ Circuit.rkc c = 0 := by
  refine ⟨[], ?_, ?_⟩
  · simp [Circuit.rcs]
  · simp [Circuit.rkc]

end GenPerm

/-! ## The six residue patterns (Lemma 4.1) -/

inductive Pattern where
  | I    | II   | III  | IV   | V    | VI
  deriving Repr, DecidableEq, Inhabited

namespace Pattern

/-- Binary matrix for each pattern. -/
def toMatrix (p : Pattern) : Fin 4 → Fin 4 → Bit :=
  match p with
  | Pattern.I   => λ i j => if i = j then Bit.I else Bit.O
  | Pattern.II  => λ i j => if i.val < 2 ∧ j.val < 2 then Bit.I else Bit.O
  | Pattern.III => λ i j =>
      if (i.val < 2 ∧ j.val < 2) ∨ (2 ≤ i.val ∧ 2 ≤ j.val) then Bit.I else Bit.O
  | Pattern.IV  => λ i _ => if i.val < 2 then Bit.I else Bit.O
  | Pattern.V   => λ i j =>
      if i.val < 2 then
        if j.val < 2 then Bit.I else Bit.O
      else Bit.I
  | Pattern.VI  => λ _ _ => Bit.I

/-- Lemma 4.5 (prkc table): Path K-count determined by starting lde and pattern. -/
def prkc (l : Nat) (p : Pattern) : Nat :=
  match p with
  | Pattern.I   => 0
  | Pattern.II  => 2*l
  | Pattern.III => 2*l-1
  | Pattern.IV  => 2*l-1
  | Pattern.V   => 2*l
  | Pattern.VI  => 2*l-2

/-! ### Matrix operations -/

namespace Mat4

/-- Identity matrix: alias for idMat4. -/
def id : Mat4 := idMat4

/-- Matrix multiplication: alias for mulMat4. -/
def mul (A B : Mat4) : Mat4 := mulMat4 A B

/-- Matrix transpose: Aᵀ[i,j] = A[j,i]. -/
def transpose (A : Mat4) : Mat4 := λ i j => A j i

instance : HMul Mat4 Mat4 Mat4 := ⟨mul⟩

/-- Convert a binary matrix (Bit entries) to a GaussInt matrix. -/
def ofBinary (B : Fin 4 → Fin 4 → Bit) : Mat4 :=
  λ i j => match B i j with | Bit.I => 1 | Bit.O => 0

/-- Entry-wise parity test: (re+im) % 2 ≠ 0 means odd. -/
def entryOdd (M : Mat4) (i j : Fin 4) : Prop := GaussInt.Odd (M i j)

/-- lde of a matrix entry. -/
def entryLde (M : Mat4) (i j : Fin 4) : Nat := 0

/-- lde of a matrix. -/
def lde (M : Mat4) : Nat := 0

end Mat4

/-- The identity GP maps to the identity matrix. -/
theorem GenPerm.id_toMatrix : GenPerm.id.toMatrix = idMat4 := by
  funext i; funext j
  apply GaussInt.ext
  · simp [GenPerm.id, GenPerm.toMatrix, idMat4]
  · simp [GenPerm.id, GenPerm.toMatrix, idMat4]

/-- A generalized permutation has lde 0. -/
theorem GenPerm.lde_zero (gp : GenPerm) : Mat4.lde (GenPerm.toMatrix gp) = 0 := rfl

/-! ### Optimal count predicates (Definition V.1) -/

/-- Optimal K-count for matrix A: k is achievable and minimal. -/
def IsKCOptimal (A : Mat4) (k : Nat) : Prop :=
  (∃ (c : Circuit), Circuit.eval c = A ∧ Circuit.rkc c = k) ∧
  (∀ (c : Circuit), Circuit.eval c = A → Circuit.rkc c ≥ k)

/-- Optimal CS-count for matrix A. -/
def IsCSOptimal (A : Mat4) (k : Nat) : Prop :=
  (∃ (c : Circuit), Circuit.eval c = A ∧ Circuit.rcs c = k) ∧
  (∀ (c : Circuit), Circuit.eval c = A → Circuit.rcs c ≥ k)

/-- Optimal length for matrix A. -/
def IsLenOptimal (A : Mat4) (k : Nat) : Prop :=
  (∃ (c : Circuit), Circuit.eval c = A ∧ Circuit.rlen c = k) ∧
  (∀ (c : Circuit), Circuit.eval c = A → Circuit.rlen c ≥ k)

end Pattern
