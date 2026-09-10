import Mathlib
import RequestProject.SzaboMatrices
import RequestProject.SzaboDeterminant

/-!
# Basic patterns for undergraduate linear-algebra exam proofs

This file is the "proof patterns" chapter of the guide.  Each section is one
standard exam manoeuvre, stated and proved in Lean, with a note on how it looks
as a circuit diagram.

1. **Axiom chasing in a vector space** (`Pattern.zero_smul'`, …): everything is
   forced by the axioms; diagrammatically these are the unit laws of the
   scalar boxes.
2. **Kernel and injectivity** (`Pattern.injective_iff_ker_eq_bot`): the classic
   "show `ker f = 0`" step.
3. **Inverses** (`Pattern.inverse_unique`, `Pattern.mul_eq_one_comm'`,
   `Pattern.inv_mul_rev`): Szabó §4; diagrammatically the yanking equations.
4. **Rank–nullity** (`Pattern.rank_nullity`).
5. **Trace and determinant invariants** (`Pattern.trace_conj`,
   `Pattern.det_conj`): the trace is a closed loop, so it can be slid around.
6. **Independence of two vectors** (`Pattern.linearIndependent_pair_iff'`).
7. **Homogeneous systems** (`Pattern.exists_nontrivial_solution_iff_det_eq_zero`):
   Szabó §5 and §3 together.
-/

namespace Pattern

open Matrix Szabo

/-! ## 1. Axiom chasing -/

section VectorSpace

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- `0 • v = 0`, proved by the standard cancellation trick. -/
theorem zero_smul' (v : V) : (0 : K) • v = 0 := by
  have h : (0 : K) • v + (0 : K) • v = (0 : K) • v + 0 := by
    rw [← add_smul, add_zero, add_zero]
  exact (add_left_cancel h)

/-- `a • 0 = 0`. -/
theorem smul_zero' (a : K) : a • (0 : V) = 0 := by
  have h : a • (0 : V) + a • (0 : V) = a • (0 : V) + 0 := by
    rw [← smul_add, add_zero, add_zero]
  exact (add_left_cancel h)

/-- `(-1) • v = -v`. -/
theorem neg_one_smul' (v : V) : (-1 : K) • v = -v := by
  have h : v + (-1 : K) • v = 0 := by
    calc v + (-1 : K) • v = (1 : K) • v + (-1 : K) • v := by rw [one_smul]
      _ = ((1 : K) + (-1 : K)) • v := by rw [add_smul]
      _ = (0 : K) • v := by norm_num
      _ = 0 := zero_smul' v
  exact eq_neg_of_add_eq_zero_left (by rwa [add_comm] at h)

/-- **A product is zero only if a factor is**: the key step in almost every
independence argument. -/
theorem smul_eq_zero' {a : K} {v : V} (h : a • v = 0) : a = 0 ∨ v = 0 := by
  by_cases ha : a = 0
  · exact Or.inl ha
  · right
    calc v = (1 : K) • v := (one_smul K v).symm
      _ = (a⁻¹ * a) • v := by rw [inv_mul_cancel₀ ha]
      _ = a⁻¹ • (a • v) := (smul_smul a⁻¹ a v).symm
      _ = a⁻¹ • (0 : V) := by rw [h]
      _ = 0 := smul_zero' _

/-- The zero vector is unique. -/
theorem zero_unique (z : V) (h : ∀ v : V, v + z = v) : z = 0 := by
  simpa using h 0

/-- Additive inverses are unique. -/
theorem neg_unique (v w : V) (h : v + w = 0) : w = -v :=
  eq_neg_of_add_eq_zero_right h

end VectorSpace

/-! ## 2. Kernel and injectivity -/

section Kernel

variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

/-- A linear map is injective iff its kernel is trivial. -/
theorem injective_iff_ker_eq_bot (f : V →ₗ[K] W) :
    Function.Injective f ↔ LinearMap.ker f = ⊥ := by
  constructor
  · intro hf
    apply LinearMap.ker_eq_bot'.2
    intro x hx
    exact hf (by simpa using hx)
  · intro hker x y hxy
    have hmem : x - y ∈ LinearMap.ker f := by
      simp [LinearMap.mem_ker, map_sub, hxy]
    rw [hker] at hmem
    have : x - y = 0 := by simpa using hmem
    exact sub_eq_zero.mp this

end Kernel

/-! ## 3. Inverses (Szabó §4) -/

section Inverses

variable {K : Type*} [Field K] {n : ℕ}

/-- **The inverse of a matrix is unique** — the exam-standard three-line
computation `B = B(AC) = (BA)C = C`.  Diagrammatically this is "yanking" a
zig-zag straight. -/
theorem inverse_unique (A B C : Mat K n n) (hB : mmul B A = 1) (hC : mmul A C = 1) :
    B = C := by
  calc B = mmul B 1 := (mmul_E B).symm
    _ = mmul B (mmul A C) := by rw [hC]
    _ = mmul (mmul B A) C := (mmul_assoc B A C).symm
    _ = mmul 1 C := by rw [hB]
    _ = C := by rw [← E_eq_one, E_mmul]

/-- A one-sided inverse of a square matrix is two-sided. -/
theorem mul_eq_one_comm' (A B : Mat K n n) (h : mmul A B = 1) : mmul B A = 1 := by
  rw [mmul_eq_hMul] at h ⊢
  exact mul_eq_one_comm.mp h

/-- `(AB)⁻¹ = B⁻¹A⁻¹`: inverting reverses the order, exactly as transposition
does in Szabó 2.7(iv). -/
theorem inv_mul_rev (A B A' B' : Mat K n n)
    (hA : mmul A A' = 1) (hB : mmul B B' = 1) :
    mmul (mmul A B) (mmul B' A') = 1 := by
  calc mmul (mmul A B) (mmul B' A')
      = mmul A (mmul B (mmul B' A')) := mmul_assoc A B _
    _ = mmul A (mmul (mmul B B') A') := by rw [mmul_assoc]
    _ = mmul A (mmul 1 A') := by rw [hB]
    _ = mmul A A' := by rw [← E_eq_one, E_mmul]
    _ = 1 := hA

end Inverses

/-! ## 4. Rank–nullity -/

section RankNullity

variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
variable [FiniteDimensional K V]

/-- **Rank–nullity theorem**: `dim im f + dim ker f = dim V`. -/
theorem rank_nullity (f : V →ₗ[K] W) :
    Module.finrank K (LinearMap.range f) + Module.finrank K (LinearMap.ker f) =
      Module.finrank K V :=
  LinearMap.finrank_range_add_finrank_ker f

end RankNullity

/-! ## 5. Trace and determinant invariants -/

section Invariants

variable {K : Type*} [Field K] {n : ℕ}

/-- **The trace is a closed loop**, so conjugation does not change it:
`tr (P⁻¹ A P) = tr A`. -/
theorem trace_conj (A P Q : Mat K n n) (h : mmul Q P = 1) :
    (mmul (mmul Q A) P).trace = A.trace := by
  simp only [mmul_eq_hMul] at h ⊢
  have h' : P * Q = 1 := mul_eq_one_comm.mp h
  rw [Matrix.trace_mul_comm (Q * A) P, ← Matrix.mul_assoc, h', Matrix.one_mul]

/-- The determinant is likewise invariant under conjugation. -/
theorem det_conj (A P Q : Mat K n n) (h : mmul Q P = 1) :
    (mmul (mmul Q A) P).det = A.det := by
  simp only [mmul_eq_hMul] at h ⊢
  rw [Matrix.det_mul, Matrix.det_mul]
  have hdet : Q.det * P.det = 1 := by
    rw [← Matrix.det_mul, h, Matrix.det_one]
  calc Q.det * A.det * P.det = (Q.det * P.det) * A.det := by ring
    _ = A.det := by rw [hdet, one_mul]

/-- `det (AB) = det A · det B`, in the textbook's notation. -/
theorem det_mul' (A B : Mat K n n) : sdet (mmul A B) = sdet A * sdet B :=
  sdet_mmul A B

end Invariants

/-! ## 6. Independence of two vectors -/

section Independence

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The working definition of independence used in exams, for a pair. -/
theorem linearIndependent_pair_iff' (v w : V) :
    LinearIndependent K ![v, w] ↔ ∀ a b : K, a • v + b • w = 0 → a = 0 ∧ b = 0 := by
  rw [LinearIndependent.pair_iff]

/-- Two vectors are dependent as soon as one is a multiple of the other. -/
theorem not_linearIndependent_of_smul (v w : V) (a : K) (hw : w = a • v) :
    ¬ LinearIndependent K ![v, w] := by
  rw [linearIndependent_pair_iff']
  intro h
  have := h a (-1) (by rw [hw]; module)
  exact absurd this.2 (by norm_num)

end Independence

/-! ## 7. Homogeneous systems -/

section Systems

variable {K : Type*} [Field K] {n : ℕ}

/-- **A homogeneous square system has a nontrivial solution iff the
determinant vanishes** (Szabó §3 and §5).  Diagrammatically: the circuit of `A`
is not injective exactly when its determinant scalar is `0`. -/
theorem exists_nontrivial_solution_iff_det_eq_zero (A : Mat K n n) :
    (∃ v : Fin n → K, v ≠ 0 ∧ A.mulVec v = 0) ↔ sdet A = 0 := by
  rw [sdet_eq_det]
  exact Matrix.exists_mulVec_eq_zero_iff

end Systems

end Pattern
