import Mathlib
import Atlas.Relation.Slope

/-!
# Tematika 08 — "Folytonosság fogalma, formális tulajdonságai.  Folytonos
függvények tulajdonsága: középérték-tétel, kompakt intervallumon folytonos
függvények."

**Syllabus item.**  *Folytonosság fogalma, formális tulajdonságai.  Folytonos
függvények tulajdonsága: középérték-tétel, kompakt intervallumon folytonos
függvények.*

**Categorical reading.**  Continuity is **preservation of limits**: a
continuous map is a morphism in `Top`, and the formal properties (composites
and combinations of continuous maps are continuous) are the statement that
`Top` is a category with finite products.  The library's ground object carries
the *discrete* topology, so every map out of it is continuous
(`Tematika.Continuity.continuous_of_discrete`): continuity carries no
information there, and the working notion of "morphism" moves one level down,
to the algebraic structure — which is why the library's transport lemmas are
about additive/ring maps rather than about continuity.

The two theorems of the chapter do transport, and they transport *literally*:

* **Kompakt intervallumon folytonos függvény felveszi a szélsőértékét
  (Weierstrass).**  A finite discrete space is compact, so Mathlib's compactness
  theorem applies verbatim and gives the finite maximum principle
  (`Tematika.Continuity.exists_max_of_finite_discrete` is proved *by* the
  general `IsCompact.exists_isMaxOn`).  In the library this is what makes the
  phrase "the largest slope count" meaningful: the admissible slope set
  `Atlas.slopeSet K` is a nonempty finite "compact interval" and the count
  attains its maximum on it (`Tematika.Continuity.exists_max_slopeCount`).
* **Középérték-tétel (Bolzano/intermediate value).**  Over `ℝ` it rests on
  connectedness of an interval.  Over a discrete object connectedness fails, and
  the surviving form is the *unit-step* version: a function whose increments are
  at most one hits every intermediate value
  (`Tematika.Continuity.discrete_intermediate_value`).  This is the shape in
  which the property is used in a counting proof: a quantity that changes by at
  most one and passes a level must equal that level somewhere.
-/

namespace Tematika.Continuity

/-- **Folytonosság a diszkrét kontextusban.**  Every map out of a discrete
space is continuous: continuity is vacuous over the library's ground object. -/
theorem continuous_of_discrete {α β : Type*} [TopologicalSpace α] [DiscreteTopology α]
    [TopologicalSpace β] (f : α → β) : Continuous f :=
  continuous_of_discreteTopology

/-- **Weierstrass in the finite context.**  A finite discrete space is compact,
so the extremum theorem for continuous functions on a compact set applies as it
stands.  The proof is the general compactness argument, not a finite
recomputation. -/
theorem exists_max_of_finite_discrete {α : Type*} [Finite α] [Nonempty α]
    [TopologicalSpace α] [DiscreteTopology α] (f : α → ℝ) : ∃ x₀, ∀ x, f x ≤ f x₀ := by
  have hc : IsCompact (Set.univ : Set α) := isCompact_univ
  obtain ⟨x₀, -, hx₀⟩ := hc.exists_isMaxOn Set.univ_nonempty
    (continuous_of_discreteTopology (f := f)).continuousOn
  exact ⟨x₀, fun x => hx₀ (Set.mem_univ x)⟩

/-- The same statement for a nonempty finite index set, in the form the library
uses it: the maximum over the admissible slopes is attained. -/
theorem exists_max_on_finset {ι : Type*} (s : Finset ι) (hs : s.Nonempty) (g : ι → ℝ) :
    ∃ i ∈ s, ∀ j ∈ s, g j ≤ g i :=
  s.exists_max_image g hs

/-- **The library's compact interval.**  The admissible slope set is a nonempty
finite set, so the slope count attains a maximum on it. -/
theorem exists_max_slopeCount {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (hK : 2 < Fintype.card K) (g : K → ℝ) :
    ∃ ρ ∈ Atlas.slopeSet K, ∀ σ ∈ Atlas.slopeSet K, g σ ≤ g ρ :=
  exists_max_on_finset _ (Atlas.slopeSet_nonempty hK) g

/-- **Középérték-tétel, unit-step form.**  If the increments of an integer
sequence are at most one and it starts below the level `c` and reaches or passes
it, then it *equals* `c` somewhere.  This is the combinatorial residue of the
intermediate value theorem: connectedness is replaced by "no jump larger than
one". -/
theorem discrete_intermediate_value (f : ℕ → ℤ) (hstep : ∀ n, f (n + 1) ≤ f n + 1)
    (c : ℤ) (h0 : f 0 ≤ c) : ∀ N, c ≤ f N → ∃ n ≤ N, f n = c := by
  intro N
  induction N with
  | zero => intro hN; exact ⟨0, le_refl _, le_antisymm h0 hN⟩
  | succ N ih =>
    intro hN
    by_cases hc : c ≤ f N
    · obtain ⟨n, hn, hfn⟩ := ih hc
      exact ⟨n, hn.trans (Nat.le_succ N), hfn⟩
    · push_neg at hc
      have h1 := hstep N
      exact ⟨N + 1, le_refl _, by omega⟩

/-- Calculus I's intermediate value theorem, recorded for comparison: over `ℝ`
the hypothesis is continuity on a compact interval, and the conclusion is that
the whole interval `[f a, f b]` is in the image. -/
theorem intermediate_value_real {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc a b)) : Set.Icc (f a) (f b) ⊆ f '' Set.Icc a b :=
  intermediate_value_Icc hab hf

end Tematika.Continuity
