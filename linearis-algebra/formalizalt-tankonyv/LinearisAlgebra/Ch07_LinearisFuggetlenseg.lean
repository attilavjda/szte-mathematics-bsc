import LinearisAlgebra.Ch06_Vektorterek

/-!
# Szabó László: Bevezetés a lineáris algebrába — 7. fejezet:
# Lineárisan független és függő vektorrendszerek

A jegyzet 7. fejezetének (38–41. oldal) formalizálása:

* **7.1. Definíció** — lineárisan független, illetve (össze)függő vektorrendszer,
* **7.2. Tétel** — a lineáris függőség három ekvivalens jellemzése,
* **7.3. Tétel** — részrendszerek, bővítés, `(7.3.3)` és az előállítás egyértelműsége,
* **7.4. Kicserélési tétel**,
* **7.5. Következmény** — lineárisan független rendszer nem lehet hosszabb egy őt
  generáló rendszernél.

A vektorrendszereket — a könyv `v₁,…,v_k` jelölésének megfelelően — `Fin k → V` alakú
függvényekkel írjuk le.  A `linFuggetlen_iff_linearIndependent` híd-lemma szerint a könyv
fogalma megegyezik a Mathlib `LinearIndependent` fogalmával.
-/

namespace SzaboLinAlg
namespace Ch07

open scoped BigOperators
open SzaboLinAlg.Ch06

variable {T : Type*} [Field T] {V : Type*} [AddCommGroup V] [Module T V] {k l : ℕ}

/-! ## 7.1. Definíció -/

/-- **7.1. Definíció.** A `v₁,…,v_k` vektorrendszer *lineárisan független*, ha valahányszor
`λ₁v₁ + … + λ_kv_k = 0`, mindannyiszor `λ₁ = … = λ_k = 0`. -/
def LinFuggetlen (T : Type*) [Field T] {V : Type*} [AddCommGroup V] [Module T V] {k : ℕ}
    (v : Fin k → V) : Prop :=
  ∀ g : Fin k → T, ∑ i, g i • v i = 0 → ∀ i, g i = 0

/-- **7.1. Definíció.** A vektorrendszer *lineárisan (össze)függő*, ha nem lineárisan
független. -/
def LinFuggo (T : Type*) [Field T] {V : Type*} [AddCommGroup V] [Module T V] {k : ℕ}
    (v : Fin k → V) : Prop :=
  ¬ LinFuggetlen T v

/-- A könyv lineáris függetlensége megegyezik a Mathlib `LinearIndependent` fogalmával. -/
theorem linFuggetlen_iff_linearIndependent (v : Fin k → V) :
    LinFuggetlen T v ↔ LinearIndependent T v :=
  Fintype.linearIndependent_iff.symm

/-- **7.1. Definíció.** Az üres vektorrendszer megállapodás szerint lineárisan független. -/
theorem linFuggetlen_ures (v : Fin 0 → V) : LinFuggetlen T v := by
  intro g _ i
  exact i.elim0

/-- Egyelemű vektorrendszer pontosan akkor lineárisan függő, ha vektora a nullvektor. -/
theorem linFuggo_egyelemu (x : V) : LinFuggo T (fun _ : Fin 1 => x) ↔ x = 0 := by
  constructor
  · intro h
    by_contra hx
    refine h ?_
    intro g hg i
    have hgx : g 0 • x = 0 := by simpa using hg
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    exact (smul_eq_zero.1 hgx).resolve_right hx
  · rintro rfl
    intro h
    have := h (fun _ => 1) (by simp) 0
    exact one_ne_zero this

/-! ## 7.2. Tétel -/

/-- A `v` rendszer `i`-től különböző indexű tagjainak halmaza. -/
def masok (v : Fin k → V) (i : Fin k) : Set V := v '' {j | j ≠ i}

/-- A `v` rendszer `i`-nél kisebb indexű tagjainak halmaza. -/
def elozok (v : Fin k → V) (i : Fin k) : Set V := v '' {j | j < i}

omit [AddCommGroup V] in
theorem masok_eq (v : Fin k → V) (i : Fin k) : masok v i = v '' (Set.univ \ {i}) := by
  unfold masok
  congr 1
  ext j
  simp

/-- **(7.2.2) ⟹ (7.2.1).** Ha valamelyik vektor a többi lineáris kombinációja, akkor a
rendszer lineárisan függő.

*Bizonyítás.* Ha `vᵢ = λ₁v₁ + … + λ_kv_k` (az `i`-edik tag nélkül), akkor a `(-1)`
együtthatóval az `i`-edik helyen nemtriviális lineáris kombináció adja a nullvektort. -/
theorem linFuggo_of_mem_masok {v : Fin k → V} {i : Fin k}
    (h : v i ∈ Generalt T (masok v i)) : LinFuggo T v := by
  intro hfug
  have hli : LinearIndependent T v := (linFuggetlen_iff_linearIndependent v).1 hfug
  have h' : (1 : T) • v i ∈ Submodule.span T (v '' (Set.univ \ {i})) := by
    rw [one_smul, ← masok_eq, ← SetLike.mem_coe, ← generalt_eq_span]
    exact h
  exact one_ne_zero (hli.eq_zero_of_smul_mem_span i 1 h')

/-- **(7.2.3) ⟹ (7.2.2).** Ha `vᵢ` az őt megelőző vektorok lineáris kombinációja, akkor a
többi vektoré is. -/
theorem mem_masok_of_mem_elozok {v : Fin k → V} {i : Fin k}
    (h : v i ∈ Generalt T (elozok v i)) : v i ∈ Generalt T (masok v i) :=
  generalt_mono (Set.image_mono (fun _ hj => ne_of_lt hj)) h

/-- **(7.2.1) ⟹ (7.2.3).** Ha a rendszer lineárisan függő, akkor van olyan tagja, amely az
őt megelőző tagok lineáris kombinációja.

*Bizonyítás (a könyv szerint).* Legyen `λ₁v₁ + … + λ_kv_k = 0` nemtriviális, és legyen
`λᵢ` a legnagyobb indexű nem nulla együttható.  Ekkor
`vᵢ = -(1/λᵢ)(λ₁v₁ + … + λ_{i-1}v_{i-1}) ∈ [v₁,…,v_{i-1}]`. -/
theorem exists_mem_elozok_of_linFuggo {v : Fin k → V} (h : LinFuggo T v) :
    ∃ i, v i ∈ Generalt T (elozok v i) := by
  classical
  rw [LinFuggo, LinFuggetlen] at h
  push_neg at h
  obtain ⟨g, hg, i₀, hi₀⟩ := h
  set S : Finset (Fin k) := Finset.univ.filter (fun j => g j ≠ 0) with hS
  have hSne : S.Nonempty := ⟨i₀, by simp [hS, hi₀]⟩
  set i : Fin k := S.max' hSne with hi
  have hgi : g i ≠ 0 := by
    have : i ∈ S := S.max'_mem hSne
    simpa [hS] using this
  have hzero : ∀ j, i < j → g j = 0 := by
    intro j hj
    by_contra hgj
    have hjS : j ∈ S := by simp [hS, hgj]
    exact absurd (S.le_max' j hjS) (not_le.2 hj)
  -- a nem nulla együtthatók mind `i`-nél kisebb (vagy egyenlő) indexűek
  have hsplit : ∑ j, g j • v j
      = (∑ j ∈ Finset.univ.filter (fun j => j < i), g j • v j) + g i • v i := by
    have h1 : ∑ j ∈ Finset.univ.filter (fun j => ¬ j ≤ i), g j • v j = 0 := by
      refine Finset.sum_eq_zero ?_
      intro j hj
      have : i < j := by
        have := (Finset.mem_filter.1 hj).2
        exact lt_of_not_ge this
      rw [hzero j this, zero_smul]
    have h2 : (Finset.univ.filter (fun j => j ≤ i))
        = insert i (Finset.univ.filter (fun j => j < i)) := by
      ext j
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_insert]
      constructor
      · intro hj
        rcases lt_or_eq_of_le hj with hlt | heq
        · exact Or.inr hlt
        · exact Or.inl heq
      · rintro (rfl | hlt)
        · exact le_rfl
        · exact le_of_lt hlt
    have h3 := Finset.sum_filter_add_sum_filter_not Finset.univ (fun j => j ≤ i)
      (fun j => g j • v j)
    rw [h1, add_zero] at h3
    rw [← h3, h2, Finset.sum_insert (by simp)]
    rw [add_comm]
  rw [hsplit] at hg
  refine ⟨i, ?_⟩
  rw [generalt_eq_span]
  have hvi : v i = (-(g i)⁻¹) • ∑ j ∈ Finset.univ.filter (fun j => j < i), g j • v j := by
    have hgv : g i • v i = -∑ j ∈ Finset.univ.filter (fun j => j < i), g j • v j := by
      linear_combination (norm := module) hg
    have := congrArg (fun x : V => (g i)⁻¹ • x) hgv
    simp only [smul_smul, inv_mul_cancel₀ hgi, one_smul] at this
    rw [this]
    module
  rw [hvi]
  refine Submodule.smul_mem _ _ (Submodule.sum_mem _ ?_)
  intro j hj
  refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  exact ⟨j, (Finset.mem_filter.1 hj).2, rfl⟩

/-- **7.2. Tétel.** A `v₁,…,v_k` vektorrendszerre az alábbi három állítás ekvivalens:
(7.2.1) a rendszer lineárisan függő; (7.2.2) valamelyik tagja a többi lineáris
kombinációja; (7.2.3) valamelyik tagja az őt megelőzők lineáris kombinációja. -/
theorem linFuggo_tfae (v : Fin k → V) :
    List.TFAE [LinFuggo T v, ∃ i, v i ∈ Generalt T (masok v i),
      ∃ i, v i ∈ Generalt T (elozok v i)] := by
  tfae_have 3 → 2 := by
    rintro ⟨i, hi⟩
    exact ⟨i, mem_masok_of_mem_elozok hi⟩
  tfae_have 2 → 1 := by
    rintro ⟨i, hi⟩
    exact linFuggo_of_mem_masok hi
  tfae_have 1 → 3 := exists_mem_elozok_of_linFuggo
  tfae_finish

/-! ## 7.3. Tétel -/

/-- **(7.3.1)** Lineárisan független vektorrendszer minden részrendszere lineárisan
független (a részrendszert egy injektív indexátírás adja meg). -/
theorem linFuggetlen_reszrendszer {v : Fin k → V} (hv : LinFuggetlen T v) {m : ℕ}
    (f : Fin m → Fin k) (hf : Function.Injective f) : LinFuggetlen T (v ∘ f) :=
  (linFuggetlen_iff_linearIndependent _).2
    (((linFuggetlen_iff_linearIndependent v).1 hv).comp f hf)

/-- **(7.3.2)** Lineárisan függő részrendszert tartalmazó vektorrendszer lineárisan
függő. -/
theorem linFuggo_of_reszrendszer {v : Fin k → V} {m : ℕ} (f : Fin m → Fin k)
    (hf : Function.Injective f) (h : LinFuggo T (v ∘ f)) : LinFuggo T v :=
  fun hv => h (linFuggetlen_reszrendszer hv f hf)

/-- **(7.3.3)** Ha `v₁,…,v_k` lineárisan független, de `v₁,…,v_k,x` lineárisan függő,
akkor `x ∈ [v₁,…,v_k]`. -/
theorem mem_generalt_of_snoc_linFuggo {v : Fin k → V} {x : V} (hv : LinFuggetlen T v)
    (h : LinFuggo T (Fin.snoc v x : Fin (k + 1) → V)) :
    x ∈ Generalt T (Set.range v) := by
  rw [generalt_eq_span]
  by_contra hx
  exact h ((linFuggetlen_iff_linearIndependent _).2
    (linearIndependent_fin_snoc.2 ⟨(linFuggetlen_iff_linearIndependent v).1 hv, hx⟩))

/-- **(7.3.4)** Lineárisan független rendszer esetén a lineáris kombinációként való
előállítás egyértelmű. -/
theorem egyertelmu_eloallitas {v : Fin k → V} (hv : LinFuggetlen T v) {a b : Fin k → T}
    (h : ∑ i, a i • v i = ∑ i, b i • v i) : a = b := by
  have h0 : ∑ i, (a i - b i) • v i = 0 := by
    simp only [sub_smul]
    rw [Finset.sum_sub_distrib, h, sub_self]
  funext i
  exact sub_eq_zero.1 (hv (fun i => a i - b i) h0 i)

/-! ## 7.4. Kicserélési tétel -/

/-- Segédlemma: az `i`-edik helyen kicserélt rendszer lineáris kombinációja. -/
theorem sum_update (w : Fin k → V) (i : Fin k) (x : V) (g : Fin k → T) :
    ∑ a, g a • (Function.update w i x) a
      = g i • x + ∑ a ∈ Finset.univ.erase i, g a • w a := by
  classical
  rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
  simp only [Function.update_self]
  congr 1
  refine Finset.sum_congr rfl fun a ha => ?_
  rw [Function.update_of_ne (Finset.ne_of_mem_erase ha)]

/-- Segédlemma a kicserélési tételhez: ha `u` lineárisan független, de az `i`-edik tagját
`x`-re cserélve lineárisan függő rendszert kapunk, akkor `x` benne van a többi `u`-tag
által generált altérben. -/
theorem mem_masok_of_update_linFuggo {u : Fin k → V} {i : Fin k} {x : V}
    (hu : LinFuggetlen T u) (h : LinFuggo T (Function.update u i x)) :
    x ∈ Generalt T (masok u i) := by
  classical
  rw [LinFuggo, LinFuggetlen] at h
  push_neg at h
  obtain ⟨g, hg, b, hb⟩ := h
  rw [sum_update] at hg
  by_cases hgi : g i = 0
  · -- ekkor `u` valamely nemtriviális lineáris kombinációja is nulla, ellentmondás
    exfalso
    have hg' : ∑ a, (Function.update g i 0) a • u a = 0 := by
      rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i)]
      simp only [Function.update_self, zero_smul, zero_add]
      have : ∑ a ∈ Finset.univ.erase i, (Function.update g i 0) a • u a
          = ∑ a ∈ Finset.univ.erase i, g a • u a :=
        Finset.sum_congr rfl fun a ha => by
          rw [Function.update_of_ne (Finset.ne_of_mem_erase ha)]
      rw [this]
      simpa [hgi] using hg
    have hall := hu _ hg'
    rcases eq_or_ne b i with rfl | hbi
    · exact hb hgi
    · have := hall b
      rw [Function.update_of_ne hbi] at this
      exact hb this
  · -- `x` kifejezhető a többi vektor lineáris kombinációjaként
    rw [generalt_eq_span]
    have hx : x = (-(g i)⁻¹) • ∑ a ∈ Finset.univ.erase i, g a • u a := by
      have hgv : g i • x = -∑ a ∈ Finset.univ.erase i, g a • u a := by
        linear_combination (norm := module) hg
      have := congrArg (fun y : V => (g i)⁻¹ • y) hgv
      simp only [smul_smul, inv_mul_cancel₀ hgi, one_smul] at this
      rw [this]
      module
    rw [hx]
    refine Submodule.smul_mem _ _ (Submodule.sum_mem _ fun a ha => ?_)
    refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    exact ⟨a, Finset.ne_of_mem_erase ha, rfl⟩

/-- **7.4. Kicserélési tétel.** Ha `u₁,…,u_k` lineárisan független és
`u₁,…,u_k ∈ [v₁,…,v_l]`, akkor bármely `uᵢ` vektorhoz van olyan `v_j` vektor, hogy
`u₁,…,u_{i-1},v_j,u_{i+1},…,u_k` is lineárisan független.

*Bizonyítás (a könyv szerint).* Ha nem így volna, akkor minden `j`-re `v_j` benne lenne a
többi `u`-tag által generált altérben, ezért `uᵢ ∈ [v₁,…,v_l]` is benne lenne, ami
ellentmond `u₁,…,u_k` lineáris függetlenségének. -/
theorem kicserelesi_tetel {u : Fin k → V} {v : Fin l → V} (hu : LinFuggetlen T u)
    (hspan : ∀ a, u a ∈ Generalt T (Set.range v)) (i : Fin k) :
    ∃ j, LinFuggetlen T (Function.update u i (v j)) := by
  classical
  by_contra hcon
  push_neg at hcon
  have hall : ∀ j, v j ∈ Submodule.span T (masok u i) := by
    intro j
    have := mem_masok_of_update_linFuggo hu (hcon j)
    rwa [generalt_eq_span] at this
  have hle : Submodule.span T (Set.range v) ≤ Submodule.span T (masok u i) := by
    rw [Submodule.span_le]
    rintro x ⟨j, rfl⟩
    exact hall j
  have hui : u i ∈ Submodule.span T (masok u i) := by
    have := hspan i
    rw [generalt_eq_span] at this
    exact hle this
  have hli : LinearIndependent T u := (linFuggetlen_iff_linearIndependent u).1 hu
  refine one_ne_zero (hli.eq_zero_of_smul_mem_span i 1 ?_)
  rw [one_smul, ← masok_eq]
  exact hui

/-- **7.5. Következmény.** Ha `u₁,…,u_k` lineárisan független és `u₁,…,u_k ∈ [v₁,…,v_l]`,
akkor `k ≤ l`. -/
theorem linFuggetlen_card_le {u : Fin k → V} {v : Fin l → V} (hu : LinFuggetlen T u)
    (hspan : ∀ a, u a ∈ Generalt T (Set.range v)) : k ≤ l := by
  classical
  have hli : LinearIndependent T u := (linFuggetlen_iff_linearIndependent u).1 hu
  have hsub : Set.range u ≤ (Submodule.span T (Set.range v) : Set V) := by
    rintro x ⟨a, rfl⟩
    have := hspan a
    rwa [generalt_eq_span] at this
  have hcard := linearIndependent_le_span' u hli (Set.range v) hsub
  have h1 : (Cardinal.mk (Fin k)) = (k : Cardinal) := by simp
  have h2 : Fintype.card (Set.range v) ≤ l := by
    simpa using Fintype.card_range_le v
  rw [h1] at hcard
  have hk : k ≤ Fintype.card (Set.range v) := by exact_mod_cast hcard
  exact hk.trans h2

end Ch07
end SzaboLinAlg
