/-
# Lineáris algebra I

A kurzus néhány központi tétele és tipikus számolása:

* `rank_nullity` — **dimenziótétel**: `dim Im f + dim Ker f = dim V`;
* `det_two_by_two` — a 2×2-es determináns képlete;
* `isUnit_iff_det_ne_zero` — egy négyzetes mátrix pontosan akkor invertálható,
  ha a determinánsa nem nulla;
* `cramer_two` — Cramer-szabály 2×2-es egyenletrendszerre: nemnulla determináns
  esetén egyértelmű a megoldás (és meg is adjuk);
* `eigen_example` — sajátérték-számítás egy konkrét mátrixra.
-/
import Mathlib

namespace SZTE.LinAlg

open Module Matrix

/-- **Dimenziótétel** (rang–nullitás tétel). -/
theorem rank_nullity {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [AddCommGroup W] [Module K W] (f : V →ₗ[K] W) :
    finrank K (LinearMap.range f) + finrank K (LinearMap.ker f) = finrank K V :=
  LinearMap.finrank_range_add_finrank_ker f

/-- A 2×2-es mátrix determinánsa. -/
theorem det_two_by_two (a b c d : ℝ) :
    (Matrix.of ![![a, b], ![c, d]]).det = a * d - b * c := by
  simp [Matrix.det_fin_two]

/-- Egy négyzetes mátrix pontosan akkor invertálható, ha determinánsa nem nulla. -/
theorem isUnit_iff_det_ne_zero {K : Type*} [Field K] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) K) : IsUnit A ↔ A.det ≠ 0 := by
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]

/-- **Cramer-szabály** 2×2-re: ha `ad - bc ≠ 0`, akkor az
`a x + b y = e`, `c x + d y = f` rendszernek pontosan egy megoldása van,
mégpedig `x = (ed - bf)/(ad - bc)`, `y = (af - ec)/(ad - bc)`. -/
theorem cramer_two {a b c d e f : ℝ} (h : a * d - b * c ≠ 0) :
    ∃! p : ℝ × ℝ, a * p.1 + b * p.2 = e ∧ c * p.1 + d * p.2 = f := by
  refine ⟨((e * d - b * f) / (a * d - b * c), (a * f - e * c) / (a * d - b * c)), ⟨?_, ?_⟩, ?_⟩
  · show a * ((e * d - b * f) / (a * d - b * c)) + b * ((a * f - e * c) / (a * d - b * c)) = e
    rw [show a * ((e * d - b * f) / (a * d - b * c)) + b * ((a * f - e * c) / (a * d - b * c))
        = (a * (e * d - b * f) + b * (a * f - e * c)) / (a * d - b * c) by ring,
      div_eq_iff h]
    ring
  · show c * ((e * d - b * f) / (a * d - b * c)) + d * ((a * f - e * c) / (a * d - b * c)) = f
    rw [show c * ((e * d - b * f) / (a * d - b * c)) + d * ((a * f - e * c) / (a * d - b * c))
        = (c * (e * d - b * f) + d * (a * f - e * c)) / (a * d - b * c) by ring,
      div_eq_iff h]
    ring
  · rintro ⟨x, y⟩ ⟨h1, h2⟩
    simp only at h1 h2
    have hx : x * (a * d - b * c) = e * d - b * f := by linear_combination d * h1 - b * h2
    have hy : y * (a * d - b * c) = a * f - e * c := by linear_combination a * h2 - c * h1
    have hx' : x = (e * d - b * f) / (a * d - b * c) := by rw [eq_div_iff h]; exact hx
    have hy' : y = (a * f - e * c) / (a * d - b * c) := by rw [eq_div_iff h]; exact hy
    simp [hx', hy']

/-- Konkrét sajátérték-számítás: az `!![2,1;1,2]` mátrix sajátértékei 3 és 1,
a hozzájuk tartozó sajátvektorok `(1,1)` illetve `(1,-1)`. -/
theorem eigen_example :
    (!![2, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ ![1, 1] = (3 : ℝ) • ![1, 1] ∧
    (!![2, 1; 1, 2] : Matrix (Fin 2) (Fin 2) ℝ) *ᵥ ![1, -1] = (1 : ℝ) • ![1, -1] := by
  constructor <;> ext i <;> fin_cases i <;>
    norm_num [Matrix.mulVec, Matrix.vecHead, Matrix.vecTail]

end SZTE.LinAlg
