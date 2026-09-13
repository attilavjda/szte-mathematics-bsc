import Mathlib

/-!
# Darboux : la propriété des valeurs intermédiaires, isolée

Module de base. On isole la *conclusion* du théorème de Darboux (« l'image d'un
intervalle est un intervalle ») en une propriété `DarbouxOn`, indépendante de la
dérivabilité. Les deux sources classiques (continuité, dérivée) deviennent alors deux
flèches entrant dans le même nœud du graphe de preuves.

* `DarbouxOn f s` : toute partie ordre-connexe de `s` a une image ordre-connexe.
* `darbouxOn_iff` : forme ponctuelle (valeurs intermédiaires).
* `ContinuousOn.darbouxOn`, `darbouxOn_deriv` : les deux sources.
* `DarbouxOn.comp_continuousOn` : stabilité par post-composition continue.
-/

open Set

namespace Darboux

variable {f g : ℝ → ℝ} {s t : Set ℝ} {a b y : ℝ}

/-- Propriété de Darboux (propriété des valeurs intermédiaires) sur `s` : l'image de
toute partie ordre-connexe de `s` est ordre-connexe. -/
def DarbouxOn (f : ℝ → ℝ) (s : Set ℝ) : Prop :=
  ∀ ⦃t : Set ℝ⦄, t ⊆ s → t.OrdConnected → (f '' t).OrdConnected

theorem DarbouxOn.mono (hf : DarbouxOn f s) (hts : t ⊆ s) : DarbouxOn f t :=
  fun _u hut hu => hf (hut.trans hts) hu

theorem DarbouxOn.image_ordConnected (hf : DarbouxOn f s) (hs : s.OrdConnected) :
    (f '' s).OrdConnected :=
  hf (subset_refl s) hs

/-- Forme ponctuelle : toute valeur intermédiaire est atteinte entre `a` et `b`. -/
theorem DarbouxOn.exists_eq (hf : DarbouxOn f s) (hs : s.OrdConnected) (ha : a ∈ s) (hb : b ∈ s)
    (hy : y ∈ uIcc (f a) (f b)) : ∃ c ∈ uIcc a b, f c = y := by
  have hsub : uIcc a b ⊆ s := hs.uIcc_subset ha hb
  have h := hf hsub ordConnected_uIcc
  have hya : f a ∈ f '' uIcc a b := mem_image_of_mem f left_mem_uIcc
  have hyb : f b ∈ f '' uIcc a b := mem_image_of_mem f right_mem_uIcc
  obtain ⟨c, hc, hcy⟩ : y ∈ f '' uIcc a b := h.uIcc_subset hya hyb hy
  exact ⟨c, hc, hcy⟩

theorem darbouxOn_of_forall_exists
    (H : ∀ a ∈ s, ∀ b ∈ s, ∀ y ∈ uIcc (f a) (f b), ∃ c ∈ uIcc a b, f c = y) :
    DarbouxOn f s := by
  intro t hts ht
  refine ⟨?_⟩
  rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩ y hy
  have hy' : y ∈ uIcc (f a) (f b) := Icc_subset_uIcc hy
  obtain ⟨c, hc, rfl⟩ := H a (hts ha) b (hts hb) y hy'
  exact mem_image_of_mem f (ht.uIcc_subset ha hb hc)

theorem darbouxOn_iff (hs : s.OrdConnected) :
    DarbouxOn f s ↔ ∀ a ∈ s, ∀ b ∈ s, ∀ y ∈ uIcc (f a) (f b), ∃ c ∈ uIcc a b, f c = y :=
  ⟨fun hf _ ha _ hb _ hy => hf.exists_eq hs ha hb hy, darbouxOn_of_forall_exists⟩

/-- Première source : la continuité (théorème des valeurs intermédiaires). -/
theorem _root_.ContinuousOn.darbouxOn (hf : ContinuousOn f s) : DarbouxOn f s := by
  intro t hts ht
  exact ((ht.isPreconnected).image f (hf.mono hts)).ordConnected

/-- Seconde source : la dérivation (**théorème de Darboux**). -/
theorem darbouxOn_deriv (hf : ∀ x ∈ s, DifferentiableAt ℝ f x) : DarbouxOn (deriv f) s :=
  fun _t hts ht => ht.image_deriv fun x hx => hf x (hts hx)

theorem darbouxOn_const (c : ℝ) : DarbouxOn (fun _ => c) s :=
  (continuousOn_const).darbouxOn

/-- Post-composition par une fonction continue : `g ∘ f` reste Darboux.
(La composition de deux fonctions de Darboux, elle, ne l'est pas en général.) -/
theorem DarbouxOn.comp_continuousOn (hf : DarbouxOn f s) (hg : ContinuousOn g (f '' s)) :
    DarbouxOn (g ∘ f) s := by
  intro t hts ht
  have himg : (f '' t).OrdConnected := hf hts ht
  have hsub : f '' t ⊆ f '' s := image_mono hts
  have hpre : IsPreconnected (g '' (f '' t)) :=
    (himg.isPreconnected).image g (hg.mono hsub)
  rw [image_comp]
  exact hpre.ordConnected

end Darboux
