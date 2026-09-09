/-
# Instance 1 (Analysis / Calculus): the triangle inequality is a lax cost

A (pseudo)metric space `X` is read as the **indiscrete** composition system on
`X`: exactly one arrow `a ⟶ b` for every pair of points, composition being
"go via `b`".  The cost of that arrow is the distance, combined additively.
The two laxness axioms are then literally

* `dist a a ≤ 0`  (identity costs nothing), and
* `dist a c ≤ dist a b + dist b c`  (the triangle inequality).

Feeding this into the generic `LaxCost.cost_chain` produces the polygon
inequality of first-year analysis, with no analysis in the proof.
-/
import CurriculumPatterns.LaxCost

namespace CurriculumPatterns

open scoped NNReal

variable (X : Type*) [PseudoMetricSpace X]

/-- The indiscrete composition system on a metric space: one arrow between any
two points. -/
@[reducible] def metricSystem : CompSystem.{_, 0} where
  Obj := X
  Hom _ _ := PUnit
  id _ := PUnit.unit
  comp _ _ := PUnit.unit

/-- Distance as a lax cost on `metricSystem X`, with costs combined by addition.
`cost_id` is `dist a a = 0` and `cost_comp` is the triangle inequality. -/
def distCost : LaxCost (metricSystem X) ℝ≥0 where
  op a b := a + b
  unit := 0
  op_mono h₁ h₂ := add_le_add h₁ h₂
  cost {a b} _ := nndist a b
  cost_id a := by simp
  cost_comp {a b c} _ _ := nndist_triangle a b c

variable {X}

/-- **Polygon inequality, obtained from the generic pattern.**
`dist (x 0) (x n) ≤ ∑ i < n, dist (x i) (x (i+1))` is exactly `cost_chain` for
the additive distance cost. -/
theorem nndist_le_range_sum_nndist (x : ℕ → X) (n : ℕ) :
    nndist (x 0) (x n) ≤ ∑ i ∈ Finset.range n, nndist (x i) (x (i + 1)) := by
  have h := (distCost X).cost_chain x (fun i => PUnit.unit) n
  simpa [distCost, opChain_add] using h

/-- The same statement over `ℝ`, matching the textbook formulation. -/
theorem dist_le_range_sum_dist_of_pattern (x : ℕ → X) (n : ℕ) :
    dist (x 0) (x n) ≤ ∑ i ∈ Finset.range n, dist (x i) (x (i + 1)) := by
  have h' := (NNReal.coe_le_coe).2 (nndist_le_range_sum_nndist x n)
  push_cast [← dist_nndist] at h'
  exact h'

end CurriculumPatterns
