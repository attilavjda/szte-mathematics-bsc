/-
# Functoriality: a map of spaces is a functor, and Lipschitz-ness is a comparison of costs

The indiscrete composition system of `MetricPearl.lean` depends functorially on
the underlying set: *any* map `g : X → Y` induces a functor
`metricSystem X ⥤ metricSystem Y`.  Pulling the distance cost back along it
gives the cost `(a, b) ↦ dist (g a) (g b)`, and the statement "`g` is
`K`-Lipschitz" is precisely the comparison

`pulled-back cost ≤ K • original cost`.

So the Lipschitz condition of the analysis course is not an extra notion: it is
a 2-cell between two costs on the same composition system.
-/
import CurriculumPatterns.MetricPearl

namespace CurriculumPatterns

open scoped NNReal

variable {X Y : Type*} [PseudoMetricSpace X] [PseudoMetricSpace Y]

/-- Every map of sets is a functor between the indiscrete composition systems. -/
def indiscreteFunctor (g : X → Y) : CompFunctor (metricSystem X) (metricSystem Y) where
  obj := g
  map _ := PUnit.unit
  map_id _ := rfl
  map_comp _ _ := rfl

omit [PseudoMetricSpace X] in
@[simp]
theorem comap_distCost_cost (g : X → Y) {a b : X} (u : (metricSystem X).Hom a b) :
    ((distCost Y).comap (indiscreteFunctor g)).cost u = nndist (g a) (g b) := rfl

/-- **Lipschitz = a comparison of costs.**  `g` is `K`-Lipschitz exactly when the
distance cost pulled back along `g` is dominated by `K` times the distance cost. -/
theorem lipschitzWith_iff_comap_cost_le (g : X → Y) (K : ℝ≥0) :
    LipschitzWith K g ↔
      ∀ (a b : X) (u : (metricSystem X).Hom a b),
        ((distCost Y).comap (indiscreteFunctor g)).cost u ≤ K * (distCost X).cost u := by
  constructor
  · intro h a b _
    simpa [distCost] using LipschitzWith.nndist_le h a b
  · intro h
    refine LipschitzWith.of_dist_le_mul fun a b => ?_
    have := h a b PUnit.unit
    simp only [distCost] at this
    exact_mod_cast this

end CurriculumPatterns
