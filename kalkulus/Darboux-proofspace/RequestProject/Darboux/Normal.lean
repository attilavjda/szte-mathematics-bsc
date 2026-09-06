import RequestProject.Darboux.Basic

/-!
# L'autre Darboux : forme normale d'une densité en dimension 1

Le théorème de Darboux symplectique dit : toute forme symplectique est localement
`∑ dpᵢ ∧ dqᵢ`. En dimension 1 (formes volume), l'énoncé se réduit à : toute densité
continue strictement positive `ρ` s'écrit `Φ^* (dx)` pour un difféomorphisme `Φ`, à savoir
la primitive de `ρ`. C'est le squelette du procédé de Moser : on résout `Φ' = ρ`.

Le lien avec le premier Darboux : la carte `Φ` est construite comme une primitive, donc sa
dérivée est de Darboux ; et son image est un intervalle, ce qui donne le domaine de la carte.
-/

open Set MeasureTheory intervalIntegral

namespace Darboux

variable {rho : ℝ → ℝ}

/-- La carte de Darboux en dimension 1 : la primitive de la densité. -/
noncomputable def chart (rho : ℝ → ℝ) : ℝ → ℝ := fun x => ∫ t in (0:ℝ)..x, rho t

/-- `Φ' = ρ` : la carte redresse la densité. -/
theorem hasDerivAt_chart (hc : Continuous rho) (x : ℝ) : HasDerivAt (chart rho) (rho x) x :=
  (hc.integral_hasStrictDerivAt 0 x).hasDerivAt

theorem deriv_chart (hc : Continuous rho) (x : ℝ) : deriv (chart rho) x = rho x :=
  (hasDerivAt_chart hc x).deriv

/-- Une densité continue strictement positive donne une carte strictement croissante. -/
theorem strictMono_chart (hc : Continuous rho) (hpos : ∀ x, 0 < rho x) :
    StrictMono (chart rho) :=
  strictMono_of_deriv_pos fun x => by rw [deriv_chart hc x]; exact hpos x

/-- L'image de la carte est un intervalle (ordre-connexe) : le domaine de la coordonnée
de Darboux. -/
theorem ordConnected_range_chart (hc : Continuous rho) :
    (Set.range (chart rho)).OrdConnected := by
  have hcont : ContinuousOn (chart rho) univ := fun x _ =>
    ((hasDerivAt_chart hc x).differentiableAt.continuousAt).continuousWithinAt
  have := (ContinuousOn.darbouxOn hcont).image_ordConnected ordConnected_univ
  rwa [image_univ] at this

/-- Changement de variable : la carte transporte la mesure `ρ dx` sur `dx`.
C'est la forme normale : `∫_a^b ρ = Φ(b) - Φ(a)`. -/
theorem integral_eq_sub_chart (hc : Continuous rho) (a b : ℝ) :
    ∫ t in a..b, rho t = chart rho b - chart rho a := by
  have h : ∀ x ∈ uIcc a b, HasDerivAt (chart rho) (rho x) x := fun x _ => hasDerivAt_chart hc x
  exact integral_eq_sub_of_hasDerivAt h (hc.intervalIntegrable a b)

/-- Forme normale : il existe un difféomorphisme local (ici global, strictement croissant et
dérivable) qui envoie la densité `ρ` sur la densité constante `1`. -/
theorem exists_chart_of_density (hc : Continuous rho) (hpos : ∀ x, 0 < rho x) :
    ∃ Phi : ℝ → ℝ, StrictMono Phi ∧ (∀ x, HasDerivAt Phi (rho x) x) ∧
      (Set.range Phi).OrdConnected ∧ ∀ a b, ∫ t in a..b, rho t = Phi b - Phi a :=
  ⟨chart rho, strictMono_chart hc hpos, hasDerivAt_chart hc, ordConnected_range_chart hc,
    integral_eq_sub_chart hc⟩

end Darboux
