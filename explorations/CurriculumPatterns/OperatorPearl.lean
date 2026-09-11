/-
# Instance 2 (Linear algebra): submultiplicativity of the operator norm is a lax cost

The bounded operators on a normed space form a **one-object** composition system
(a monoid).  The cost of an operator is its norm, combined *multiplicatively*.
The two laxness axioms are then

* `‖id‖ ≤ 1`  (identity costs nothing), and
* `‖g ∘ f‖ ≤ ‖f‖ · ‖g‖`  (submultiplicativity),

which is the same shape as the triangle inequality of `MetricPearl.lean`, only
read in the ordered monoid `(ℝ≥0, ·, 1)` instead of `(ℝ≥0, +, 0)`.  The generic
`LaxCost.cost_chain` then yields the power bound `‖fⁿ‖ ≤ ‖f‖ⁿ` used for
Neumann series, spectral radius estimates and convergence of iterations.
-/
import CurriculumPatterns.LaxCost

namespace CurriculumPatterns

open scoped NNReal

variable (𝕜 : Type*) [NontriviallyNormedField 𝕜]
variable (E : Type*) [SeminormedAddCommGroup E] [NormedSpace 𝕜 E]

/-- Bounded operators on `E` as a one-object composition system. -/
@[reducible] def operatorSystem : CompSystem.{0, _} where
  Obj := PUnit
  Hom _ _ := E →L[𝕜] E
  id _ := ContinuousLinearMap.id 𝕜 E
  comp f g := g.comp f

/-- The operator norm as a lax cost, with costs combined by multiplication. -/
noncomputable def opNormCost : LaxCost (operatorSystem 𝕜 E) ℝ≥0 where
  op a b := a * b
  unit := 1
  op_mono h₁ h₂ := mul_le_mul' h₁ h₂
  cost f := ‖f‖₊
  cost_id _ := by
    have : ‖ContinuousLinearMap.id 𝕜 E‖ ≤ (1 : ℝ) := ContinuousLinearMap.norm_id_le
    exact_mod_cast this
  cost_comp f g := by
    have h : ‖g.comp f‖ ≤ ‖g‖ * ‖f‖ := ContinuousLinearMap.opNorm_comp_le g f
    have : ‖g.comp f‖₊ ≤ ‖f‖₊ * ‖g‖₊ := by
      rw [mul_comm] at h
      exact_mod_cast h
    exact this

variable {𝕜 E}

/-- Iterating a single arrow in the one-object system is taking powers. -/
theorem chain_const_eq_pow (f : E →L[𝕜] E) (n : ℕ) :
    (operatorSystem 𝕜 E).chain (fun _ => PUnit.unit) (fun _ => f) n = f ^ n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [CompSystem.chain_succ, ih, operatorSystem]
      rw [pow_succ']
      rfl

/-- **The power bound, obtained from the generic pattern**: `‖fⁿ‖ ≤ ‖f‖ⁿ`. -/
theorem nnnorm_pow_le_of_pattern (f : E →L[𝕜] E) (n : ℕ) :
    ‖f ^ n‖₊ ≤ ‖f‖₊ ^ n := by
  have h := (opNormCost 𝕜 E).cost_chain (fun _ => PUnit.unit) (fun _ => f) n
  rw [chain_const_eq_pow] at h
  simpa [opNormCost, opChain_mul_const] using h

/-- The same statement over `ℝ`, as it appears in the linear algebra course. -/
theorem norm_pow_le_of_pattern (f : E →L[𝕜] E) (n : ℕ) :
    ‖f ^ n‖ ≤ ‖f‖ ^ n := by
  have h' := (NNReal.coe_le_coe).2 (nnnorm_pow_le_of_pattern f n)
  push_cast at h'
  exact h'

end CurriculumPatterns
