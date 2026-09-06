import RequestProject.Darboux.Shapes

/-!
# Conséquences pour les dérivées

Spécialisations des formes de `Shapes.lean` au nœud `deriv`, plus les formes qui
utilisent une structure dont les fonctions de Darboux générales sont dépourvues :
l'ensemble des dérivées est un espace vectoriel.

* `deriv_eq_of_countable_image`, `deriv_eq_of_int_valued` : dérivée à valeurs
  dénombrables ⇒ constante.
* `deriv_strictMonoOn_or_strictAntiOn_of_injOn` : dérivée injective ⇒ strictement monotone.
* `ConvexOn.continuousOn_deriv` : convexe + dérivable ⇒ de classe `C¹`.
* `not_isDeriv_sign` : la fonction signe n'est la dérivée de personne.
* `deriv_lt_id_or_id_lt_deriv` : forme « point fixe » (utilise la linéarité).
-/

open Set Filter Topology

namespace Darboux

variable {f : ℝ → ℝ} {s : Set ℝ} {x y : ℝ}

/-! ### Dérivée à valeurs dénombrables -/

/-- Une dérivée dont l'image est dénombrable est constante. -/
theorem deriv_eq_of_countable_image (hs : s.OrdConnected)
    (hf : ∀ z ∈ s, DifferentiableAt ℝ f z) (hc : (deriv f '' s).Countable)
    (hx : x ∈ s) (hy : y ∈ s) : deriv f x = deriv f y :=
  (darbouxOn_deriv hf).eq_of_countable_image hs hc hx hy

/-- Une dérivée à valeurs entières est constante. -/
theorem deriv_eq_of_int_valued (hs : s.OrdConnected) (hf : ∀ z ∈ s, DifferentiableAt ℝ f z)
    (hint : ∀ z ∈ s, ∃ n : ℤ, deriv f z = n) (hx : x ∈ s) (hy : y ∈ s) :
    deriv f x = deriv f y := by
  refine (darbouxOn_deriv hf).eq_of_range_subset_countable hs
    (u := Set.range (fun n : ℤ => (n : ℝ))) (Set.countable_range _) ?_ hx hy
  intro z hz
  obtain ⟨n, hn⟩ := hint z hz
  exact ⟨n, hn.symm⟩

/-! ### Dérivée injective -/

/-- Une dérivée injective sur un intervalle y est strictement monotone. -/
theorem deriv_strictMonoOn_or_strictAntiOn_of_injOn (hs : s.OrdConnected)
    (hf : ∀ z ∈ s, DifferentiableAt ℝ f z) (hinj : InjOn (deriv f) s) :
    StrictMonoOn (deriv f) s ∨ StrictAntiOn (deriv f) s :=
  (darbouxOn_deriv hf).strictMonoOn_or_strictAntiOn hs hinj

/-! ### Convexe + dérivable ⇒ `C¹` -/

/-- **Forme non répertoriée** : une fonction convexe et dérivable sur un ouvert convexe est
de classe `C¹` : sa dérivée, monotone (convexité) et de Darboux, est continue. -/
theorem ConvexOn.continuousOn_deriv (hconv : ConvexOn ℝ s f) (hopen : IsOpen s)
    (hf : ∀ z ∈ s, DifferentiableAt ℝ f z) : ContinuousOn (deriv f) s :=
  (darbouxOn_deriv hf).continuousOn_of_monotoneOn_of_isOpen hconv.1.ordConnected hopen
    (hconv.monotoneOn_deriv hf)

/-! ### Obstructions concrètes -/

/-- La fonction signe n'est la dérivée d'aucune fonction : son image `{-1, 1}` n'est pas un
intervalle. -/
theorem not_isDeriv_sign :
    ¬ ∃ f : ℝ → ℝ, ∀ z : ℝ, HasDerivAt f (if z < 0 then (-1 : ℝ) else 1) z := by
  rintro ⟨f, hf⟩
  have hdiff : ∀ z ∈ (univ : Set ℝ), DifferentiableAt ℝ f z := fun z _ => (hf z).differentiableAt
  have hval : ∀ z : ℝ, deriv f z = if z < 0 then (-1 : ℝ) else 1 := fun z => (hf z).deriv
  have hD := darbouxOn_deriv hdiff
  obtain ⟨c, -, hc⟩ := hD.exists_eq ordConnected_univ (a := -1) (b := 1) (y := 0)
    (mem_univ _) (mem_univ _) (by
      rw [mem_uIcc, hval, hval]
      norm_num)
  rw [hval] at hc
  split_ifs at hc <;> norm_num at hc

/-! ### Forme « point fixe » : la linéarité en plus -/

/-- **Forme non répertoriée** : si une dérivée ne rencontre jamais l'identité, alors elle est
partout strictement en dessous, ou partout strictement au-dessus. La preuve utilise le fait
que les dérivées forment un espace vectoriel (`deriv f - id` est encore une dérivée), une
structure que les fonctions de Darboux générales n'ont pas. -/
theorem deriv_lt_id_or_id_lt_deriv (hs : s.OrdConnected)
    (hf : ∀ z ∈ s, DifferentiableAt ℝ f z) (hne : ∀ z ∈ s, deriv f z ≠ z) :
    (∀ z ∈ s, deriv f z < z) ∨ (∀ z ∈ s, z < deriv f z) := by
  set g : ℝ → ℝ := fun z => f z - z ^ 2 / 2 with hg
  have hgdiff : ∀ z ∈ s, DifferentiableAt ℝ g z := by
    intro z hz
    exact (hf z hz).sub (((differentiableAt_id.pow 2).div_const 2))
  have hgderiv : ∀ z ∈ s, deriv g z = deriv f z - z := by
    intro z hz
    have : deriv g z = deriv f z - deriv (fun w : ℝ => w ^ 2 / 2) z :=
      deriv_sub (hf z hz) ((differentiableAt_id.pow 2).div_const 2)
    rw [this]
    have h2 : deriv (fun w : ℝ => w ^ 2 / 2) z = z := by
      simp [deriv_div_const]
    rw [h2]
  have hgne : ∀ z ∈ s, deriv g z ≠ 0 := by
    intro z hz
    rw [hgderiv z hz]
    exact sub_ne_zero_of_ne (hne z hz)
  rcases (darbouxOn_deriv hgdiff).forall_lt_or_forall_gt hs hgne with h | h
  · refine Or.inl fun z hz => ?_
    have := h z hz
    rw [hgderiv z hz] at this
    linarith
  · refine Or.inr fun z hz => ?_
    have := h z hz
    rw [hgderiv z hz] at this
    linarith

/-- Dérivée ne s'annulant pas sur un intervalle convexe ⇒ `f` strictement monotone. -/
theorem strictMonoOn_or_strictAntiOn_of_deriv_ne_zero (hs : Convex ℝ s)
    (hf : ∀ z ∈ s, DifferentiableAt ℝ f z) (hne : ∀ z ∈ s, deriv f z ≠ 0) :
    StrictMonoOn f s ∨ StrictAntiOn f s := by
  have hcont : ContinuousOn f s := fun z hz => (hf z hz).continuousAt.continuousWithinAt
  rcases (darbouxOn_deriv hf).forall_lt_or_forall_gt hs.ordConnected hne with h | h
  · exact Or.inr (strictAntiOn_of_deriv_neg hs hcont fun z hz => h z (interior_subset hz))
  · exact Or.inl (strictMonoOn_of_deriv_pos hs hcont fun z hz => h z (interior_subset hz))

end Darboux
