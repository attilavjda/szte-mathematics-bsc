import RequestProject.Darboux.Basic

/-!
# Formes de lemmes autour de Darboux

Hyper-arêtes du graphe de preuves : `Darboux & X ⇒ Y`. Chaque énoncé remplace la
continuité par la seule propriété des valeurs intermédiaires dans un résultat connu.

* `DarbouxOn.forall_lt_or_forall_gt` : valeur évitée ⇒ signe constant.
* `DarbouxOn.subsingleton_image_of_countable` : image dénombrable ⇒ fonction constante.
* `DarbouxOn.strictMonoOn_or_strictAntiOn` : injective ⇒ strictement monotone.
* `DarbouxOn.continuousAt_of_monotoneOn` : monotone ⇒ continue.
-/

open Set Filter Topology

namespace Darboux

variable {f : ℝ → ℝ} {s : Set ℝ} {a b c d m x y : ℝ}

/-! ### Valeur évitée ⇒ signe constant -/

/-- Si `f` est de Darboux et évite la valeur `m`, alors `f < m` partout ou `f > m` partout. -/
theorem DarbouxOn.forall_lt_or_forall_gt (hf : DarbouxOn f s) (hs : s.OrdConnected)
    (hm : ∀ x ∈ s, f x ≠ m) :
    (∀ x ∈ s, f x < m) ∨ (∀ x ∈ s, m < f x) := by
  by_contra h
  push_neg at h
  obtain ⟨⟨a, ha, hma⟩, ⟨b, hb, hmb⟩⟩ := h
  have hma' : m < f a := lt_of_le_of_ne hma (Ne.symm (hm a ha))
  have hmb' : f b < m := lt_of_le_of_ne hmb (hm b hb)
  obtain ⟨c, hc, hcm⟩ := hf.exists_eq hs ha hb (by
    rw [mem_uIcc]
    exact Or.inr ⟨hmb'.le, hma'.le⟩)
  exact hm c (hs.uIcc_subset ha hb hc) hcm

/-! ### Image dénombrable ⇒ constante -/

/-- Une partie ordre-connexe dénombrable de `ℝ` est un singleton (ou vide). -/
theorem subsingleton_of_ordConnected_of_countable {u : Set ℝ} (hu : u.OrdConnected)
    (hc : u.Countable) : u.Subsingleton := by
  intro x hx y hy
  by_contra hxy
  have hIcc : uIcc x y ⊆ u := hu.uIcc_subset hx hy
  have hlt : min x y < max x y := by
    rcases lt_or_gt_of_ne hxy with h | h
    · simpa [min_eq_left h.le, max_eq_right h.le] using h
    · simpa [min_eq_right h.le, max_eq_left h.le] using h
  have hcard : Cardinal.mk (Icc (min x y) (max x y)) = Cardinal.continuum :=
    Cardinal.mk_Icc_real hlt
  have hcount : (Icc (min x y) (max x y)).Countable := hc.mono (by simpa [uIcc] using hIcc)
  rw [← Cardinal.le_aleph0_iff_set_countable, hcard] at hcount
  exact absurd hcount (not_le.2 Cardinal.aleph0_lt_continuum)

/-- **Forme non répertoriée** : une fonction de Darboux dont l'image est dénombrable est
constante. (Cas particuliers : image dans `ℤ`, dans `ℚ`, image finie.) -/
theorem DarbouxOn.subsingleton_image_of_countable (hf : DarbouxOn f s) (hs : s.OrdConnected)
    (hc : (f '' s).Countable) : (f '' s).Subsingleton :=
  subsingleton_of_ordConnected_of_countable (hf.image_ordConnected hs) hc

theorem DarbouxOn.eq_of_countable_image (hf : DarbouxOn f s) (hs : s.OrdConnected)
    (hc : (f '' s).Countable) (hx : x ∈ s) (hy : y ∈ s) : f x = f y :=
  hf.subsingleton_image_of_countable hs hc (mem_image_of_mem f hx) (mem_image_of_mem f hy)

/-- Version « à valeurs dans un ensemble dénombrable ». -/
theorem DarbouxOn.eq_of_range_subset_countable {u : Set ℝ} (hf : DarbouxOn f s)
    (hs : s.OrdConnected) (hu : u.Countable) (hfu : ∀ x ∈ s, f x ∈ u)
    (hx : x ∈ s) (hy : y ∈ s) : f x = f y :=
  hf.eq_of_countable_image hs (hu.mono (by rintro _ ⟨z, hz, rfl⟩; exact hfu z hz)) hx hy

/-! ### Injective ⇒ strictement monotone -/

/-- Configuration à trois points : si `a < b < c` et si `f` est de Darboux et injective, alors
`f b` est strictement entre `f a` et `f c`. -/
theorem DarbouxOn.strict_between (hf : DarbouxOn f s) (hs : s.OrdConnected) (hinj : InjOn f s)
    (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s) (hab : a < b) (hbc : b < c) :
    (f a < f b ∧ f b < f c) ∨ (f c < f b ∧ f b < f a) := by
  have hne_ab : f a ≠ f b := fun h => absurd (hinj ha hb h) hab.ne
  have hne_cb : f c ≠ f b := fun h => absurd (hinj hc hb h) hbc.ne'
  rcases lt_or_gt_of_ne hne_ab with h1 | h1 <;> rcases lt_or_gt_of_ne hne_cb with h2 | h2
  · -- `f a < f b` et `f c < f b` : `f b` maximum strict, exclu
    exfalso
    obtain ⟨z, hz1, hz2⟩ := exists_between (max_lt h1 h2)
    have hz1' : max (f a) (f c) < z := hz1
    obtain ⟨p, hp, hpz⟩ := hf.exists_eq hs ha hb (by
      rw [mem_uIcc]
      exact Or.inl ⟨le_of_lt (lt_of_le_of_lt (le_max_left _ _) hz1'), hz2.le⟩)
    obtain ⟨q, hq, hqz⟩ := hf.exists_eq hs hb hc (by
      rw [mem_uIcc]
      exact Or.inr ⟨le_of_lt (lt_of_le_of_lt (le_max_right _ _) hz1'), hz2.le⟩)
    have hple : p ≤ b := by rw [uIcc_of_le hab.le] at hp; exact hp.2
    have hqge : b ≤ q := by rw [uIcc_of_le hbc.le] at hq; exact hq.1
    have hps : p ∈ s := hs.uIcc_subset ha hb hp
    have hqs : q ∈ s := hs.uIcc_subset hb hc hq
    have hpq : p = q := hinj hps hqs (by rw [hpz, hqz])
    have hpb : p = b := le_antisymm hple (hpq ▸ hqge)
    rw [hpb] at hpz
    exact absurd hpz (ne_of_gt hz2)
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨h2, h1⟩
  · -- `f b < f a` et `f b < f c` : `f b` minimum strict, exclu
    exfalso
    obtain ⟨z, hz1, hz2⟩ := exists_between (lt_min h1 h2)
    have hz2' : z < min (f a) (f c) := hz2
    obtain ⟨p, hp, hpz⟩ := hf.exists_eq hs ha hb (by
      rw [mem_uIcc]
      exact Or.inr ⟨hz1.le, le_of_lt (lt_of_lt_of_le hz2' (min_le_left _ _))⟩)
    obtain ⟨q, hq, hqz⟩ := hf.exists_eq hs hb hc (by
      rw [mem_uIcc]
      exact Or.inl ⟨hz1.le, le_of_lt (lt_of_lt_of_le hz2' (min_le_right _ _))⟩)
    have hple : p ≤ b := by rw [uIcc_of_le hab.le] at hp; exact hp.2
    have hqge : b ≤ q := by rw [uIcc_of_le hbc.le] at hq; exact hq.1
    have hps : p ∈ s := hs.uIcc_subset ha hb hp
    have hqs : q ∈ s := hs.uIcc_subset hb hc hq
    have hpq : p = q := hinj hps hqs (by rw [hpz, hqz])
    have hpb : p = b := le_antisymm hple (hpq ▸ hqge)
    rw [hpb] at hpz
    exact absurd hpz (ne_of_lt hz1)

/-- Orientation stable quand on partage l'extrémité gauche. -/
theorem DarbouxOn.lt_iff_left (hf : DarbouxOn f s) (hs : s.OrdConnected) (hinj : InjOn f s)
    (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s) (hab : a < b) (hac : a < c) :
    (f a < f b ↔ f a < f c) := by
  rcases eq_or_ne b c with rfl | hbc
  · rfl
  rcases lt_or_gt_of_ne hbc with h | h
  · rcases hf.strict_between hs hinj ha hb hc hab h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨fun _ => h1.trans h2, fun _ => h1⟩
    · exact ⟨fun hlt => absurd hlt (not_lt.2 h2.le),
        fun hlt => absurd hlt (not_lt.2 (h1.trans h2).le)⟩
  · rcases hf.strict_between hs hinj ha hc hb hac h with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨fun _ => h1, fun _ => h1.trans h2⟩
    · exact ⟨fun hlt => absurd hlt (not_lt.2 (h1.trans h2).le),
        fun hlt => absurd hlt (not_lt.2 h2.le)⟩

/-- Orientation stable quand on partage l'extrémité droite. -/
theorem DarbouxOn.lt_iff_right (hf : DarbouxOn f s) (hs : s.OrdConnected) (hinj : InjOn f s)
    (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s) (hac : a < c) (hbc : b < c) :
    (f a < f c ↔ f b < f c) := by
  rcases eq_or_ne a b with rfl | hab
  · rfl
  rcases lt_or_gt_of_ne hab with h | h
  · rcases hf.strict_between hs hinj ha hb hc h hbc with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨fun _ => h2, fun _ => h1.trans h2⟩
    · exact ⟨fun hlt => absurd hlt (not_lt.2 (h1.trans h2).le),
        fun hlt => absurd hlt (not_lt.2 h1.le)⟩
  · rcases hf.strict_between hs hinj hb ha hc h hac with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨fun _ => h1.trans h2, fun _ => h2⟩
    · exact ⟨fun hlt => absurd hlt (not_lt.2 h1.le),
        fun hlt => absurd hlt (not_lt.2 (h1.trans h2).le)⟩

/-- L'orientation ne dépend pas du couple de points choisi. -/
theorem DarbouxOn.lt_iff_lt (hf : DarbouxOn f s) (hs : s.OrdConnected) (hinj : InjOn f s)
    (ha : a ∈ s) (hb : b ∈ s) (hc : c ∈ s) (hd : d ∈ s) (hab : a < b) (hcd : c < d) :
    (f a < f b ↔ f c < f d) := by
  set p := min a c with hp
  set q := max b d with hq
  have hps : p ∈ s := by
    rcases min_cases a c with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [hp, h] <;> assumption
  have hqs : q ∈ s := by
    rcases max_cases b d with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [hq, h] <;> assumption
  have key : ∀ u v : ℝ, u ∈ s → v ∈ s → u < v → p ≤ u → v ≤ q → (f u < f v ↔ f p < f q) := by
    intro u v hu hv huv hpu hvq
    have hpv : p < v := lt_of_le_of_lt hpu huv
    have hpq : p < q := lt_of_lt_of_le hpv hvq
    have step1 : (f u < f v ↔ f p < f v) := by
      rcases eq_or_lt_of_le hpu with h | h
      · rw [h]
      · exact (hf.lt_iff_right hs hinj hps hu hv hpv huv).symm
    have step2 : (f p < f v ↔ f p < f q) := by
      rcases eq_or_lt_of_le hvq with h | h
      · rw [h]
      · exact hf.lt_iff_left hs hinj hps hv hqs hpv hpq
    exact step1.trans step2
  have h1 := key a b ha hb hab (min_le_left _ _) (le_max_left _ _)
  have h2 := key c d hc hd hcd (min_le_right _ _) (le_max_right _ _)
  exact h1.trans h2.symm

/-- **Forme non répertoriée** : Darboux + injective ⇒ strictement monotone (croissante ou
décroissante). C'est la généralisation, sans hypothèse de continuité, de
`ContinuousOn.strictMonoOn_of_injOn_Icc'`. -/
theorem DarbouxOn.strictMonoOn_or_strictAntiOn (hf : DarbouxOn f s) (hs : s.OrdConnected)
    (hinj : InjOn f s) : StrictMonoOn f s ∨ StrictAntiOn f s := by
  by_cases hex : ∃ a ∈ s, ∃ b ∈ s, a < b ∧ f a < f b
  · obtain ⟨a, ha, b, hb, hab, hfab⟩ := hex
    exact Or.inl fun x hx y hy hxy => (hf.lt_iff_lt hs hinj ha hb hx hy hab hxy).mp hfab
  · push_neg at hex
    refine Or.inr fun x hx y hy hxy => ?_
    have hne : f y ≠ f x := fun h => absurd (hinj hy hx h) hxy.ne'
    exact lt_of_le_of_ne (hex x hx y hy hxy) hne

/-! ### Monotone ⇒ continue -/

/-- Continuité à droite. -/
theorem DarbouxOn.continuousWithinAt_Ici_of_monotoneOn (hf : DarbouxOn f s) (hs : s.OrdConnected)
    (hmono : MonotoneOn f s) (hx : s ∈ 𝓝[≥] x) : ContinuousWithinAt f (Ici x) x := by
  have hxs : x ∈ s := mem_of_mem_nhdsWithin self_mem_Ici hx
  by_cases hup : ∃ c ∈ s, f x < f c
  · refine continuousWithinAt_right_of_monotoneOn_of_exists_between hmono hx ?_
    intro b hb
    obtain ⟨c, hcs, hfc⟩ := hup
    obtain ⟨z, hz1, hz2⟩ := exists_between (lt_min hb hfc)
    have hz2' : z < min b (f c) := hz2
    obtain ⟨d, hd, hdz⟩ := hf.exists_eq hs hxs hcs (by
      rw [mem_uIcc]
      exact Or.inl ⟨hz1.le, le_of_lt (lt_of_lt_of_le hz2' (min_le_right _ _))⟩)
    exact ⟨d, hs.uIcc_subset hxs hcs hd, hz1.trans_eq hdz.symm,
      hdz.trans_lt (lt_of_lt_of_le hz2' (min_le_left _ _))⟩
  · push_neg at hup
    have heq : f =ᶠ[𝓝[Ici x] x] (fun _ => f x) := by
      filter_upwards [hx, self_mem_nhdsWithin] with y hy hxy
      exact le_antisymm (hup y hy) (hmono hxs hy hxy)
    exact Tendsto.congr' heq.symm tendsto_const_nhds

/-- Continuité à gauche. -/
theorem DarbouxOn.continuousWithinAt_Iic_of_monotoneOn (hf : DarbouxOn f s) (hs : s.OrdConnected)
    (hmono : MonotoneOn f s) (hx : s ∈ 𝓝[≤] x) : ContinuousWithinAt f (Iic x) x := by
  have hxs : x ∈ s := mem_of_mem_nhdsWithin self_mem_Iic hx
  by_cases hdown : ∃ c ∈ s, f c < f x
  · refine continuousWithinAt_left_of_monotoneOn_of_exists_between hmono hx ?_
    intro b hb
    obtain ⟨c, hcs, hfc⟩ := hdown
    obtain ⟨z, hz1, hz2⟩ := exists_between (max_lt hb hfc)
    have hz1' : max b (f c) < z := hz1
    obtain ⟨d, hd, hdz⟩ := hf.exists_eq hs hxs hcs (by
      rw [mem_uIcc]
      exact Or.inr ⟨le_of_lt (lt_of_le_of_lt (le_max_right _ _) hz1'), hz2.le⟩)
    exact ⟨d, hs.uIcc_subset hxs hcs hd,
      (lt_of_le_of_lt (le_max_left _ _) hz1').trans_eq hdz.symm, hdz.trans_lt hz2⟩
  · push_neg at hdown
    have heq : f =ᶠ[𝓝[Iic x] x] (fun _ => f x) := by
      filter_upwards [hx, self_mem_nhdsWithin] with y hy hxy
      exact le_antisymm (hmono hy hxs hxy) (hdown y hy)
    exact Tendsto.congr' heq.symm tendsto_const_nhds

/-- **Forme non répertoriée** : Darboux + monotone ⇒ continue en tout point intérieur. -/
theorem DarbouxOn.continuousAt_of_monotoneOn (hf : DarbouxOn f s) (hs : s.OrdConnected)
    (hmono : MonotoneOn f s) (hx : s ∈ 𝓝 x) : ContinuousAt f x :=
  continuousAt_iff_continuous_left_right.2
    ⟨hf.continuousWithinAt_Iic_of_monotoneOn hs hmono (mem_nhdsWithin_of_mem_nhds hx),
      hf.continuousWithinAt_Ici_of_monotoneOn hs hmono (mem_nhdsWithin_of_mem_nhds hx)⟩

/-- Version « ouvert » : sur un ouvert, Darboux + monotone ⇒ continue. -/
theorem DarbouxOn.continuousOn_of_monotoneOn_of_isOpen (hf : DarbouxOn f s) (hs : s.OrdConnected)
    (hopen : IsOpen s) (hmono : MonotoneOn f s) : ContinuousOn f s := fun _z hz =>
  (hf.continuousAt_of_monotoneOn hs hmono (hopen.mem_nhds hz)).continuousWithinAt

/-! ### Graphe fermé ⇒ continue -/

/-- Le niveau `{y | f y = c}` d'une fonction à graphe fermé est fermé. -/
theorem isClosed_level_of_isClosed_graph (hgr : IsClosed {p : ℝ × ℝ | f p.1 = p.2}) (c : ℝ) :
    IsClosed {y : ℝ | f y = c} := by
  have hcont : Continuous fun y : ℝ => (y, c) := continuous_id.prodMk continuous_const
  exact hgr.preimage hcont

/-- **Forme non répertoriée** : une fonction de Darboux à graphe fermé est continue.
La valeur `f x ± ε` serait atteinte arbitrairement près de `x`, donc en `x`. -/
theorem DarbouxOn.continuous_of_isClosed_graph (hf : DarbouxOn f univ)
    (hgr : IsClosed {p : ℝ × ℝ | f p.1 = p.2}) : Continuous f := by
  rw [continuous_iff_continuousAt]
  intro x
  by_contra hcont
  rw [Metric.continuousAt_iff] at hcont
  push_neg at hcont
  obtain ⟨eps, heps, hbad⟩ := hcont
  set C : Set ℝ := {y | f y = f x + eps} ∪ {y | f y = f x - eps} with hC
  have hCclosed : IsClosed C :=
    (isClosed_level_of_isClosed_graph hgr _).union (isClosed_level_of_isClosed_graph hgr _)
  have hxC : x ∈ closure C := by
    rw [Metric.mem_closure_iff]
    intro delta hdelta
    obtain ⟨y, hy1, hy2⟩ := hbad delta hdelta
    have hballOC : (Metric.ball x delta).OrdConnected := (convex_ball x delta).ordConnected
    have hxb : x ∈ Metric.ball x delta := Metric.mem_ball_self hdelta
    have hyb : y ∈ Metric.ball x delta := Metric.mem_ball.2 hy1
    rw [Real.dist_eq, le_abs] at hy2
    rcases hy2 with h | h
    · obtain ⟨c, hc, hcv⟩ := hf.exists_eq (a := x) (b := y) (y := f x + eps) ordConnected_univ
        (mem_univ _) (mem_univ _) (by rw [mem_uIcc]; constructor; · constructor <;> linarith)
      refine ⟨c, Or.inl hcv, ?_⟩
      rw [dist_comm]
      exact Metric.mem_ball.1 (hballOC.uIcc_subset hxb hyb hc)
    · obtain ⟨c, hc, hcv⟩ := hf.exists_eq (a := x) (b := y) (y := f x - eps) ordConnected_univ
        (mem_univ _) (mem_univ _) (by
          rw [mem_uIcc]
          exact Or.inr ⟨by linarith, by linarith⟩)
      refine ⟨c, Or.inr hcv, ?_⟩
      rw [dist_comm]
      exact Metric.mem_ball.1 (hballOC.uIcc_subset hxb hyb hc)
  rw [hCclosed.closure_eq] at hxC
  rcases hxC with h | h
  · simp only [Set.mem_setOf_eq] at h; linarith
  · simp only [Set.mem_setOf_eq] at h; linarith

end Darboux
