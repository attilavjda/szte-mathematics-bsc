import RequestProject.Darboux.Deriv

/-!
# La carte : l'espace de preuves autour de Darboux, vérifié par la machine

Vocabulaire fixé (nœuds), arêtes (implications simples) et hyper-arêtes (deux hypothèses
agissant ensemble). Tout est relatif à un intervalle `s` fixé, supposé ordre-connexe (et
ouvert lorsque la topologie intervient).

Non-arêtes connues (elles ne sont *pas* démontrées ici, et ne peuvent pas l'être) :
* `Darb` n'implique pas `Cont` (dérivée de `x ↦ x² sin(1/x)`) ;
* `Darb` n'est pas stable par somme ni par composition, alors que `Der` est un espace
  vectoriel : voir `Darboux.deriv_lt_id_or_id_lt_deriv` ;
* `Der` n'implique pas `Cont` : toute fonction continue est une dérivée (théorème
  fondamental de l'analyse), mais la réciproque est fausse.
-/

open Set

namespace Darboux.Space

variable (f : ℝ → ℝ) (s : Set ℝ)

/-! ### Nœuds -/

/-- `f` est continue sur `s`. -/
def Cont : Prop := ContinuousOn f s

/-- `f` est une dérivée sur `s` : `f = F'` pour une `F`. -/
def Der : Prop := ∃ F : ℝ → ℝ, ∀ x ∈ s, HasDerivAt F (f x) x

/-- `f` a la propriété des valeurs intermédiaires sur `s`. -/
def Darb : Prop := DarbouxOn f s

/-- `f` est injective sur `s`. -/
def Inj : Prop := InjOn f s

/-- `f` est croissante sur `s`. -/
def Mono : Prop := MonotoneOn f s

/-- L'image de `s` est dénombrable. -/
def CountIm : Prop := (f '' s).Countable

/-- `f` est constante sur `s`. -/
def Const : Prop := ∀ x ∈ s, ∀ y ∈ s, f x = f y

/-- `f` est strictement monotone sur `s`. -/
def StrictMonoAnti : Prop := StrictMonoOn f s ∨ StrictAntiOn f s

/-- Le graphe de `f` est fermé. -/
def ClosedGraph : Prop := IsClosed {p : ℝ × ℝ | f p.1 = p.2}

variable {f s}

/-! ### Arêtes -/

theorem cont_to_darb (h : Cont f s) : Darb f s := ContinuousOn.darbouxOn h

theorem der_to_darb (h : Der f s) : Darb f s := by
  obtain ⟨F, hF⟩ := h
  intro t hts ht
  exact ht.image_hasDerivWithinAt fun x hx => (hF x (hts hx)).hasDerivWithinAt

theorem const_to_cont (h : Const f s) : Cont f s := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
  · simp [Cont]
  · have : EqOn f (fun _ => f a) s := fun x hx => h x hx a ha
    exact (continuousOn_const).congr this

theorem const_to_mono (h : Const f s) : Mono f s := fun x hx y hy _ => (h x hx y hy).le

theorem const_to_countIm (h : Const f s) : CountIm f s := by
  rcases s.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
  · simp [CountIm]
  · refine Set.Countable.mono ?_ (Set.countable_singleton (f a))
    rintro _ ⟨x, hx, rfl⟩
    exact h x hx a ha

theorem strictMonoAnti_to_inj (h : StrictMonoAnti f s) : Inj f s :=
  h.elim StrictMonoOn.injOn StrictAntiOn.injOn

/-! ### Hyper-arêtes : les formes récoltées -/

/-- `Darb & Inj ⇒ StrictMonoAnti`. -/
theorem darb_inj_to_strictMonoAnti (hs : s.OrdConnected) (hd : Darb f s) (hi : Inj f s) :
    StrictMonoAnti f s :=
  DarbouxOn.strictMonoOn_or_strictAntiOn hd hs hi

/-- `Darb & CountIm ⇒ Const`. -/
theorem darb_countIm_to_const (hs : s.OrdConnected) (hd : Darb f s) (hc : CountIm f s) :
    Const f s := fun _ hx _ hy => DarbouxOn.eq_of_countable_image hd hs hc hx hy

/-- `Darb & Mono ⇒ Cont` (sur un ouvert). -/
theorem darb_mono_to_cont (hs : s.OrdConnected) (hopen : IsOpen s) (hd : Darb f s)
    (hm : Mono f s) : Cont f s :=
  DarbouxOn.continuousOn_of_monotoneOn_of_isOpen hd hs hopen hm

/-- `Der & Mono ⇒ Cont` : forme dérivée du précédent (une dérivée monotone est continue). -/
theorem der_mono_to_cont (hs : s.OrdConnected) (hopen : IsOpen s) (hd : Der f s) (hm : Mono f s) :
    Cont f s := darb_mono_to_cont hs hopen (der_to_darb hd) hm

/-- `Der & Inj ⇒ StrictMonoAnti`. -/
theorem der_inj_to_strictMonoAnti (hs : s.OrdConnected) (hd : Der f s) (hi : Inj f s) :
    StrictMonoAnti f s := darb_inj_to_strictMonoAnti hs (der_to_darb hd) hi

/-- `Der & CountIm ⇒ Const`. -/
theorem der_countIm_to_const (hs : s.OrdConnected) (hd : Der f s) (hc : CountIm f s) :
    Const f s := darb_countIm_to_const hs (der_to_darb hd) hc

/-- `Darb & ClosedGraph ⇒ Cont` (sur `univ`). -/
theorem darb_closedGraph_to_cont (hd : Darb f univ) (hg : ClosedGraph f) : Cont f univ :=
  (DarbouxOn.continuous_of_isClosed_graph hd hg).continuousOn

/-- `Cont ⇒ ClosedGraph`. -/
theorem cont_to_closedGraph (h : Continuous f) : ClosedGraph f :=
  isClosed_eq (h.comp continuous_fst) continuous_snd

/-! ### Chemins fermés : la boucle `Const` -/

/-- Boucle du diagramme : `Const → Mono → (avec Darb) Cont → Darb`, et `Darb & CountIm → Const`.
Version condensée : sur un ouvert, une fonction de Darboux à image dénombrable est continue. -/
theorem darb_countIm_to_cont (hs : s.OrdConnected) (hd : Darb f s) (hc : CountIm f s) :
    Cont f s := const_to_cont (darb_countIm_to_const hs hd hc)

end Darboux.Space
