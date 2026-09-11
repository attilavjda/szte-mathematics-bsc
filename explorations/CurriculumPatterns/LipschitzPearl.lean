/-
# Instance 3 (Analysis, again): Lipschitz constants compose multiplicatively

Self-maps of a metric space carrying a Lipschitz constant form a one-object
composition system, and the constant is a lax cost combined *multiplicatively* —
exactly the ordered monoid of `OperatorPearl.lean`, on an object of the analysis
course rather than of the linear algebra course.

The payoff extracted from the generic `LaxCost.cost_chain` is the contraction
estimate `LipschitzWith (K ^ n) f^[n]` behind the Banach fixed point theorem.
-/
import CurriculumPatterns.LaxCost

namespace CurriculumPatterns

open scoped NNReal

variable (X : Type*) [PseudoEMetricSpace X]

/-- A self-map together with a Lipschitz constant for it. -/
structure LipMap where
  /-- The Lipschitz constant carried by the arrow. -/
  K : ℝ≥0
  /-- The underlying map. -/
  toFun : X → X
  /-- The Lipschitz property. -/
  lipschitz : LipschitzWith K toFun

/-- Lipschitz self-maps of `X` as a one-object composition system. -/
@[reducible] def lipSystem : CompSystem.{0, _} where
  Obj := PUnit
  Hom _ _ := LipMap X
  id _ := ⟨1, id, LipschitzWith.id⟩
  comp f g := ⟨g.K * f.K, g.toFun ∘ f.toFun, g.lipschitz.comp f.lipschitz⟩

/-- The Lipschitz constant as a lax cost, combined by multiplication. -/
def lipCost : LaxCost (lipSystem X) ℝ≥0 where
  op a b := a * b
  unit := 1
  op_mono h₁ h₂ := mul_le_mul' h₁ h₂
  cost f := f.K
  cost_id _ := le_rfl
  cost_comp f g := le_of_eq (mul_comm g.K f.K)

variable {X}

/-- Iterating one arrow of `lipSystem X` iterates the underlying map. -/
theorem lipChain_toFun (f : LipMap X) (n : ℕ) :
    ((lipSystem X).chain (fun _ => PUnit.unit) (fun _ => f) n).toFun = f.toFun^[n] := by
  induction n with
  | zero => rfl
  | succ n ih =>
      simp only [CompSystem.chain_succ, lipSystem, Function.iterate_succ']
      rw [ih]

/-- **The contraction estimate, obtained from the generic pattern**: the `n`-th
iterate of a `K`-Lipschitz map is `Kⁿ`-Lipschitz. -/
theorem lipschitzWith_pow_iterate (f : LipMap X) (n : ℕ) :
    LipschitzWith (f.K ^ n) f.toFun^[n] := by
  have hcost := (lipCost X).cost_chain (fun _ => PUnit.unit) (fun _ => f) n
  simp only [lipCost, opChain_mul_const] at hcost
  have hlip := ((lipSystem X).chain (fun _ => PUnit.unit) (fun _ => f) n).lipschitz
  rw [lipChain_toFun] at hlip
  exact hlip.weaken hcost

end CurriculumPatterns
