import Mathlib
import RequestProject.SzaboMatrices

/-!
# Szabó, §3.1: the `n`-th order determinant

Definition 3.1 of the notes introduces the determinant *recursively*, by
expansion along the first row:

`|A| = a₁₁ D₁₁ - a₁₂ D₁₂ + ⋯ + (-1)^{n+1} a₁ₙ D₁ₙ`,

where `D₁ₖ` is the determinant of the matrix obtained by deleting the first row
and the `k`-th column.

We formalise exactly this recursion (`Szabo.sdet`) and prove that it computes
the same value as Mathlib's determinant (`Szabo.sdet_eq_det`), so the textbook
definition and the library's Leibniz-formula definition agree.  The `n = 2` and
`n = 3` cases displayed in the notes are then immediate.

Diagrammatically, `sdet` is the "antisymmetriser" scalar of a circuit: for
`n = 2` it is the value of the classic `2 × 2` crossing/cap circuit,
`a₁₁a₂₂ - a₁₂a₂₁`.
-/

namespace Szabo

open Matrix

variable {T : Type*} [CommRing T]

/-- §3.1 Definíció: the determinant defined recursively by expansion along the
first row.  The empty determinant is `1` (an empty product), and the minor
`A.submatrix Fin.succ k.succAbove` is Szabó's `D₁ₖ`: delete row 1 and column
`k`. -/
def sdet : {n : ℕ} → Mat T n n → T
  | 0, _ => 1
  | (n + 1), A =>
      ∑ k : Fin (n + 1), (-1) ^ (k : ℕ) * A 0 k * sdet (A.submatrix Fin.succ k.succAbove)

@[simp] theorem sdet_zero (A : Mat T 0 0) : sdet A = 1 := by rw [sdet]

theorem sdet_succ {n : ℕ} (A : Mat T (n + 1) (n + 1)) :
    sdet A =
      ∑ k : Fin (n + 1), (-1) ^ (k : ℕ) * A 0 k * sdet (A.submatrix Fin.succ k.succAbove) := by
  rw [sdet]

/-- The recursive textbook definition agrees with Mathlib's determinant. -/
theorem sdet_eq_det : ∀ {n : ℕ} (A : Mat T n n), sdet A = A.det
  | 0, A => by simp
  | (n + 1), A => by
      rw [sdet_succ, Matrix.det_succ_row_zero]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [sdet_eq_det]

/-- §3.1, the case `n = 1`. -/
theorem sdet_fin_one (A : Mat T 1 1) : sdet A = A 0 0 := by
  simp [sdet_eq_det, Matrix.det_unique]

/-- §3.1, the displayed case `n = 2`: `|A| = a₁₁a₂₂ - a₁₂a₂₁`. -/
theorem sdet_fin_two (A : Mat T 2 2) : sdet A = A 0 0 * A 1 1 - A 0 1 * A 1 0 := by
  rw [sdet_eq_det, Matrix.det_fin_two]

/-- §3.1, the displayed case `n = 3` (the "Sarrus rule"). -/
theorem sdet_fin_three (A : Mat T 3 3) :
    sdet A =
      A 0 0 * A 1 1 * A 2 2 + A 0 1 * A 1 2 * A 2 0 + A 0 2 * A 1 0 * A 2 1
        - A 0 2 * A 1 1 * A 2 0 - A 0 0 * A 1 2 * A 2 1 - A 0 1 * A 1 0 * A 2 2 := by
  rw [sdet_eq_det, Matrix.det_fin_three]
  ring

/-- The determinant of the identity matrix is `1`: a bundle of plain wires
contributes no scalar. -/
theorem sdet_E (n : ℕ) : sdet (E T n) = 1 := by
  rw [sdet_eq_det, E_eq_one, Matrix.det_one]

/-- Multiplicativity of the determinant, in the textbook's notation. -/
theorem sdet_mmul {n : ℕ} (A B : Mat T n n) : sdet (mmul A B) = sdet A * sdet B := by
  rw [sdet_eq_det, sdet_eq_det, sdet_eq_det, mmul_eq_hMul, Matrix.det_mul]

/-- The determinant is invariant under transposition. -/
theorem sdet_mtrans {n : ℕ} (A : Mat T n n) : sdet (mtrans A) = sdet A := by
  rw [sdet_eq_det, sdet_eq_det, mtrans_eq_transpose, Matrix.det_transpose]

end Szabo
