/-
# Instance 4 (Linear algebra): the determinant is the *strict* case of the same pattern

Square matrices form a one-object composition system, and `|det|` is a cost on
it valued in the ordered monoid `(ℝ≥0, ·, 1)` — the same monoid as for the
operator norm.  The difference is only laxness: the operator norm satisfies
`‖g ∘ f‖ ≤ ‖f‖ · ‖g‖`, while the determinant satisfies the corresponding
*equality*.  So "multiplicativity of the determinant" and "submultiplicativity
of the operator norm" are one statement, read strictly and laxly.

The invariant-theoretic reading is the usual one: a strict cost is a functor to
a monoid, hence an invariant of the arrow up to composition.
-/
import CurriculumPatterns.LaxCost

namespace CurriculumPatterns

open scoped NNReal

variable (d : ℕ)

/-- Square matrices of a fixed size as a one-object composition system, with
composition given by matrix multiplication in diagrammatic order. -/
@[reducible] def matrixSystem : CompSystem.{0, _} where
  Obj := PUnit
  Hom _ _ := Matrix (Fin d) (Fin d) ℝ
  id _ := 1
  comp A B := B * A

/-- `|det|` as a cost on matrices, combined by multiplication. -/
def detCost : LaxCost (matrixSystem d) ℝ≥0 where
  op a b := a * b
  unit := 1
  op_mono h₁ h₂ := mul_le_mul' h₁ h₂
  cost A := ‖A.det‖₊
  cost_id _ := by simp
  cost_comp A B := by
    simp [Matrix.det_mul, mul_comm]

/-- The determinant cost is **strict**: it is a functor, not merely a lax one. -/
theorem detCost_isStrict : (detCost d).IsStrict where
  cost_id_eq _ := by simp [detCost]
  cost_comp_eq A B := by
    simp [detCost, Matrix.det_mul, mul_comm]

variable {d}

/-- Iterating one arrow of `matrixSystem d` is taking matrix powers. -/
theorem matrixChain_const (A : Matrix (Fin d) (Fin d) ℝ) (n : ℕ) :
    (matrixSystem d).chain (fun _ => PUnit.unit) (fun _ => A) n = A ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [CompSystem.chain_succ, matrixSystem, ih]
      rw [pow_succ']

/-- **Multiplicativity of the determinant along a power, obtained from the
generic strict pattern**: `|det (Aⁿ)| = |det A|ⁿ`. -/
theorem nnnorm_det_pow (A : Matrix (Fin d) (Fin d) ℝ) (n : ℕ) :
    ‖(A ^ n).det‖₊ = ‖A.det‖₊ ^ n := by
  have h := (detCost d).cost_chain_eq (detCost_isStrict d)
    (fun _ => PUnit.unit) (fun _ => A) n
  rw [matrixChain_const] at h
  simp only [detCost, opChain_mul_const] at h
  exact h

end CurriculumPatterns
