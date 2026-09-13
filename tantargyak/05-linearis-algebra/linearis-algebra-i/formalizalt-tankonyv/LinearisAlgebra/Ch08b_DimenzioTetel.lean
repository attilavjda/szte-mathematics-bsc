import LinearisAlgebra.Ch08_VegesDimenzios

/-!
# Szabó László: Bevezetés a lineáris algebrába — 8. fejezet (folytatás)

A jegyzet 8. fejezetének (44–46. oldal) hátralévő anyaga:

* **8.5. Tétel** — `dim V` elemű generátorrendszer és `dim V` elemű lineárisan független
  vektorrendszer egyaránt bázis,
* **8.6. Tétel** — véges dimenziós vektortér altere is véges dimenziós, `dim U ≤ dim V`,
  továbbá `dim U = dim V ⟺ U = V` és `dim U = 0 ⟺ U = {0}`,
* **8.7. Alterek dimenziótétele** — `dim(U + W) = dim U + dim W − dim(U ∩ W)`,
* **8.8. Definíció** — vektorrendszer rangja, **8.9. Tétel** — `r(v₁,…,v_k) = dim [v₁,…,v_k]`,
* **8.10. Definíció** — ekvivalens vektorrendszerek, **8.11. Definíció** — a vektorrendszerek
  elemi átalakításai, **8.12. Következmény** — az elemi átalakítások ekvivalens
  vektorrendszerbe visznek át, és megőrzik a rangot.

Az alterek dimenzióját — a jegyzet szellemében — az *altér bázisának elemszámaként*
értelmezzük (`AlterBazisa`, `AlterDimenzioja`); a bizonyításokban ezt kötjük össze a
Mathlib `Module.finrank` fogalmával.
-/

namespace SzaboLinAlg
namespace Ch08b

open scoped BigOperators
open SzaboLinAlg.Ch06 SzaboLinAlg.Ch07 SzaboLinAlg.Ch08

variable {T : Type*} [Field T] {V : Type*} [AddCommGroup V] [Module T V]
variable {k l m n p q r s t : ℕ} {U W : Set V}

/-! ## Altér bázisa és dimenziója -/

/-- Az `u₁,…,u_n` vektorrendszer *bázisa* az `U` altérnek, ha lineárisan független és
éppen az `U` alteret generálja. -/
def AlterBazisa (T : Type*) [Field T] {V : Type*} [AddCommGroup V] [Module T V] {n : ℕ}
    (U : Set V) (u : Fin n → V) : Prop :=
  LinFuggetlen T u ∧ Generalt T (Set.range u) = U

/-- Az `U` altér *dimenziója* `n`, ha van `n` elemű bázisa. -/
def AlterDimenzioja (T : Type*) [Field T] {V : Type*} [AddCommGroup V] [Module T V]
    (U : Set V) (n : ℕ) : Prop :=
  ∃ u : Fin n → V, AlterBazisa T U u

/-- A teljes tér bázisai éppen a 8.1. Definíció szerinti bázisok. -/
theorem alterBazisa_univ_iff (u : Fin n → V) :
    AlterBazisa T (Set.univ : Set V) u ↔ Bazis T u := Iff.rfl

/-- A teljes tér dimenziója a 8.4. Definíció szerinti dimenzió. -/
theorem alterDimenzioja_univ_iff :
    AlterDimenzioja T (Set.univ : Set V) n ↔ Dimenzioja T V n := Iff.rfl

/-! ### Híd a Mathlib dimenziófogalmához -/

/-- Ha `U` altér, akkor az általa generált részmodulus alaphalmaza éppen `U`. -/
theorem coe_span_of_alter (hU : Alter T U) :
    ((Submodule.span T U : Submodule T V) : Set V) = U := by
  obtain ⟨X, hX⟩ := (alter_iff_submodule (T := T) U).1 hU
  subst hX
  rw [Submodule.span_eq]

/-- Egy vektorrendszer által generált altér a Mathlib `span` alaphalmaza. -/
theorem generalt_range_eq_coe_span (v : Fin k → V) :
    Generalt T (Set.range v) = ((Submodule.span T (Set.range v) : Submodule T V) : Set V) :=
  generalt_eq_span _

/-- Ha `u` bázisa az `U` altérnek, akkor `span U = span (range u)`. -/
theorem span_eq_span_range_of_alterBazisa {u : Fin n → V} (h : AlterBazisa T U u) :
    (Submodule.span T U : Submodule T V) = Submodule.span T (Set.range u) := by
  rw [← h.2, generalt_eq_span, Submodule.span_eq]

/-- Egy altér bázisának elemszáma a Mathlib szerinti dimenzió. -/
theorem finrank_span_of_alterBazisa {u : Fin n → V} (h : AlterBazisa T U u) :
    Module.finrank T (Submodule.span T U) = n := by
  rw [span_eq_span_range_of_alterBazisa h,
    finrank_span_eq_card ((linFuggetlen_iff_linearIndependent u).1 h.1), Fintype.card_fin]

/-- A `Bazis`-ból készített Mathlib-bázis. -/
noncomputable def toBasis {u : Fin n → V} (h : Bazis T u) : Module.Basis (Fin n) T V :=
  Module.Basis.mk ((linFuggetlen_iff_linearIndependent u).1 h.1)
    (by
      have : (Submodule.span T (Set.range u) : Set V) = Set.univ := by
        rw [← generalt_eq_span]; exact h.2
      intro x _
      have : x ∈ ((Submodule.span T (Set.range u) : Submodule T V) : Set V) := by
        rw [this]; trivial
      exact this)

/-- Ha a `V` vektortérnek van `n` elemű bázisa, akkor `dim V = n` a Mathlib értelmében is. -/
theorem finrank_eq_of_dimenzioja (h : Dimenzioja T V n) : Module.finrank T V = n := by
  obtain ⟨u, hu⟩ := h
  rw [Module.finrank_eq_card_basis (toBasis hu), Fintype.card_fin]

/-- Véges dimenziós vektortér a Mathlib értelmében is véges dimenziós. -/
theorem finiteDimensional_of_vegesDimenzios (h : VegesDimenzios T V) :
    FiniteDimensional T V := by
  obtain ⟨l, w, hw⟩ := h
  have hcoe : (Submodule.span T (Set.range w) : Set V) = Set.univ := by
    rw [← generalt_eq_span]; exact hw
  have htop : Submodule.span T (Set.range w) = ⊤ :=
    Submodule.eq_top_iff'.2 fun x => by
      have hx : x ∈ ((Submodule.span T (Set.range w) : Submodule T V) : Set V) := by
        rw [hcoe]; trivial
      exact hx
  refine Module.finite_def.2 ⟨(Set.finite_range w).toFinset, ?_⟩
  rw [Set.Finite.coe_toFinset]
  exact htop

/-- Ha a térnek van `n` elemű bázisa, akkor véges dimenziós. -/
theorem finiteDimensional_of_dimenzioja (h : Dimenzioja T V n) : FiniteDimensional T V :=
  finiteDimensional_of_vegesDimenzios ⟨n, h.choose, h.choose_spec.2⟩

/-- Az altér dimenziója egyértelmű. -/
theorem alterDimenzio_egyertelmu (h₁ : AlterDimenzioja T U m) (h₂ : AlterDimenzioja T U n) :
    m = n := by
  obtain ⟨u, hu⟩ := h₁
  obtain ⟨v, hv⟩ := h₂
  rw [← finrank_span_of_alterBazisa hu, ← finrank_span_of_alterBazisa hv]

/-! ## 8.5. Tétel -/

/-- **8.5. Tétel (első fele).** Véges dimenziós vektortérben minden `dim V` elemű
generátorrendszer bázis.

*Bizonyítás (a jegyzet szerint).* Ha egy generátorrendszer `dim V` elemű, akkor a
8.3. Tétel szerint tartalmaz bázist, mely ugyancsak `dim V` elemű, és ezért megegyezik a
generátorrendszerrel. -/
theorem bazis_of_generalja (hdim : Dimenzioja T V n) {v : Fin n → V} (hv : Generalja T v) :
    Bazis T v := by
  refine ⟨?_, hv⟩
  rw [linFuggetlen_iff_linearIndependent]
  refine linearIndependent_of_top_le_span_of_card_eq_finrank ?_ ?_
  · intro x _
    have : x ∈ ((Submodule.span T (Set.range v) : Submodule T V) : Set V) := by
      rw [← generalt_eq_span, hv]; trivial
    exact this
  · rw [Fintype.card_fin, finrank_eq_of_dimenzioja hdim]

/-- **8.5. Tétel (második fele).** Véges dimenziós vektortérben minden `dim V` elemű
lineárisan független vektorrendszer bázis.

*Bizonyítás (a jegyzet szerint).* Ha egy lineárisan független vektorrendszer `dim V` elemű,
akkor a 8.3. Tétel szerint bővíthető bázissá, mely ugyancsak `dim V` elemű, és ezért
megegyezik a lineárisan független vektorrendszerrel. -/
theorem bazis_of_linFuggetlen (hdim : Dimenzioja T V n) {v : Fin n → V}
    (hv : LinFuggetlen T v) : Bazis T v := by
  haveI := finiteDimensional_of_dimenzioja hdim
  refine ⟨hv, ?_⟩
  have hspan : Submodule.span T (Set.range v) = ⊤ :=
    ((linFuggetlen_iff_linearIndependent v).1 hv).span_eq_top_of_card_eq_finrank'
      (by rw [Fintype.card_fin, finrank_eq_of_dimenzioja hdim])
  rw [Generalja, generalt_eq_span, hspan]
  rfl

/-! ## 8.6. Tétel -/

/-- Bázis kiolvasása a Mathlib dimenziójából: minden altérnek van bázisa (véges dimenziós
térben), mégpedig `finrank`-nyi elemű. -/
theorem alterDimenzioja_span (hU : Alter T U)
    [FiniteDimensional T (Submodule.span T U : Submodule T V)] :
    AlterDimenzioja T U (Module.finrank T (Submodule.span T U)) := by
  set X : Submodule T V := Submodule.span T U with hX
  set N := Module.finrank T X with hN
  let b : Module.Basis (Fin N) T X := Module.finBasisOfFinrankEq T X hN.symm
  refine ⟨fun i => (b i : V), ?_, ?_⟩
  · rw [linFuggetlen_iff_linearIndependent]
    have : LinearIndependent T (fun i => (X.subtype) (b i)) :=
      b.linearIndependent.map' X.subtype (by simp [Submodule.ker_subtype])
    exact this
  · have hrange : Set.range (fun i => (b i : V)) = X.subtype '' (Set.range b) := by
      rw [← Set.range_comp]; rfl
    rw [generalt_eq_span, hrange, ← Submodule.map_span, b.span_eq, Submodule.map_top,
      Submodule.range_subtype]
    exact coe_span_of_alter hU

/-- **8.6. Tétel (első rész).** Véges dimenziós vektortér altere is véges dimenziós.

*Bizonyítás (a jegyzet szerint).* Minden `U`-beli lineárisan független vektorrendszer
`V`-ben is lineárisan független, így a 7.5. Következmény szerint legfeljebb `dim V` elemű;
ezért az üres rendszer bővíthető `U`-ban maximális lineárisan független
vektorrendszerré, ami bázis `U`-ban. -/
theorem alter_vegesDimenzios (hdim : VegesDimenzios T V) (hU : Alter T U) :
    ∃ r, AlterDimenzioja T U r := by
  haveI := finiteDimensional_of_vegesDimenzios hdim
  exact ⟨_, alterDimenzioja_span hU⟩

/-- **8.6. Tétel (második rész).** `dim U ≤ dim V`. -/
theorem alterDimenzio_le (hdim : Dimenzioja T V n) (hr : AlterDimenzioja T U r) : r ≤ n := by
  haveI := finiteDimensional_of_dimenzioja hdim
  obtain ⟨u, hu⟩ := hr
  rw [← finrank_span_of_alterBazisa hu, ← finrank_eq_of_dimenzioja hdim]
  exact Submodule.finrank_le _

/-- **8.6. Tétel (harmadik rész).** `dim U = dim V` akkor és csak akkor, ha `U = V`.

*Bizonyítás (a jegyzet szerint).* Ha `dim U = dim V`, akkor a 8.5. Tétel szerint `U`
minden bázisa `V`-ben is bázis, és ezért `U = V`. -/
theorem alterDimenzio_eq_iff (hdim : Dimenzioja T V n) (hU : Alter T U)
    (hr : AlterDimenzioja T U r) : r = n ↔ U = Set.univ := by
  haveI := finiteDimensional_of_dimenzioja hdim
  obtain ⟨u, hu⟩ := hr
  constructor
  · rintro rfl
    have hb : Bazis T u := bazis_of_linFuggetlen hdim hu.1
    rw [← hu.2]
    exact hb.2
  · rintro rfl
    exact alterDimenzio_egyertelmu ⟨u, hu⟩ hdim

/-- **8.6. Tétel (negyedik rész).** `dim U = 0` akkor és csak akkor, ha `U = {0}`.

*Bizonyítás (a jegyzet szerint).* Ha `dim U = 0`, akkor `U`-ban nincs egyelemű lineárisan
független vektorrendszer, azaz nincs `U`-ban `0`-tól különböző vektor. -/
theorem alterDimenzio_zero_iff (hU : Alter T U) :
    AlterDimenzioja T U 0 ↔ U = ({0} : Set V) := by
  constructor
  · rintro ⟨u, hu⟩
    rw [← hu.2]
    have : Set.range u = (∅ : Set V) := by
      ext x; simp [Set.range_eq_empty]
    rw [this]
    ext x
    constructor
    · rintro ⟨j, w, c, hw, rfl⟩
      have : ∀ i, w i ∈ (∅ : Set V) := hw
      cases j with
      | zero => simp
      | succ j => exact absurd (this 0) (by simp)
    · rintro rfl
      exact (generalt_alter (T := T) (∅ : Set V)).zero_mem
  · rintro rfl
    refine ⟨Fin.elim0, linFuggetlen_ures _, ?_⟩
    ext x
    constructor
    · intro hx
      have : Generalt T (Set.range (Fin.elim0 : Fin 0 → V)) ⊆ ({0} : Set V) :=
        generalt_minimal alter_zero (by simp [Set.range_eq_empty])
      exact this hx
    · rintro rfl
      exact (generalt_alter (T := T) _).zero_mem

/-! ## 8.7. Alterek dimenziótétele -/

/-- A generált részmodulus véges dimenziós, ha az altérnek van (véges) bázisa. -/
theorem finiteDimensional_span_of_alterDimenzioja (h : AlterDimenzioja T U n) :
    FiniteDimensional T (Submodule.span T U) := by
  obtain ⟨u, hu⟩ := h
  rw [span_eq_span_range_of_alterBazisa hu]
  exact FiniteDimensional.span_of_finite T (Set.finite_range u)

/-- Alterek metszetének generált részmodulusa a részmodulusok metszete. -/
theorem span_inter_of_alter (hU : Alter T U) (hW : Alter T W) :
    (Submodule.span T (U ∩ W) : Submodule T V)
      = Submodule.span T U ⊓ Submodule.span T W := by
  apply SetLike.coe_injective
  rw [coe_span_of_alter (alter_inter hU hW), Submodule.coe_inf,
    coe_span_of_alter hU, coe_span_of_alter hW]

/-- Alterek összegének generált részmodulusa a részmodulusok egyesítése (szuprémuma). -/
theorem span_alterOsszeg_of_alter (hU : Alter T U) (hW : Alter T W) :
    (Submodule.span T (AlterOsszeg U W) : Submodule T V)
      = Submodule.span T U ⊔ Submodule.span T W := by
  rw [alterOsszeg_eq_generalt hU hW, generalt_eq_span, Submodule.span_eq,
    Submodule.span_union]

/-- **8.7. Alterek dimenziótétele.** Ha `U` és `W` véges dimenziós altér valamely
vektortérben, akkor `U ∩ W` és `U + W` is véges dimenziós, és

`dim (U + W) = dim U + dim W − dim (U ∩ W)`,

itt (a természetes számok kivonását elkerülendő) az ekvivalens
`dim (U + W) + dim (U ∩ W) = dim U + dim W` alakban.

*Bizonyítás (a jegyzet szerint).* Legyen `u₁,…,u_k` az `U ∩ W` bázisa; a 8.3. Tétel szerint
ez kiegészíthető `U` és `W` bázisává is: `u₁,…,u_k,u_{k+1},…,u_m`, illetve
`u₁,…,u_k,w_{k+1},…,w_n`. Megmutatható, hogy az `u₁,…,u_m,w_{k+1},…,w_n` rendszer bázis
`U + W`-ben, amiből az állítás leolvasható. -/
theorem alterek_dimenziotetele (hU : Alter T U) (hW : Alter T W)
    (hp : AlterDimenzioja T U p) (hq : AlterDimenzioja T W q) :
    ∃ s t, AlterDimenzioja T (U ∩ W) s ∧ AlterDimenzioja T (AlterOsszeg U W) t ∧
      t + s = p + q := by
  haveI := finiteDimensional_span_of_alterDimenzioja hp
  haveI := finiteDimensional_span_of_alterDimenzioja hq
  obtain ⟨u, hu⟩ := hp
  obtain ⟨w, hw⟩ := hq
  -- a metszet és az összeg részmodulusa is véges dimenziós
  haveI : FiniteDimensional T (Submodule.span T U ⊓ Submodule.span T W :
      Submodule T V) :=
    Submodule.finiteDimensional_inf_left _ _
  haveI : FiniteDimensional T (Submodule.span T U ⊔ Submodule.span T W :
      Submodule T V) := Submodule.finite_sup _ _
  haveI : FiniteDimensional T (Submodule.span T (U ∩ W) : Submodule T V) := by
    rw [span_inter_of_alter hU hW]; infer_instance
  haveI : FiniteDimensional T (Submodule.span T (AlterOsszeg U W) : Submodule T V) := by
    rw [span_alterOsszeg_of_alter hU hW]; infer_instance
  have hi : AlterDimenzioja T (U ∩ W)
      (Module.finrank T (Submodule.span T (U ∩ W))) :=
    alterDimenzioja_span (alter_inter hU hW)
  have ho : AlterDimenzioja T (AlterOsszeg U W)
      (Module.finrank T (Submodule.span T (AlterOsszeg U W))) :=
    alterDimenzioja_span (alterOsszeg_alter hU hW)
  refine ⟨_, _, hi, ho, ?_⟩
  rw [span_inter_of_alter hU hW, span_alterOsszeg_of_alter hU hW,
    Submodule.finrank_sup_add_finrank_inf_eq, ← finrank_span_of_alterBazisa hu,
    ← finrank_span_of_alterBazisa hw]

/-! ## 8.8. Definíció, 8.9. Tétel: vektorrendszer rangja -/

/-- **8.8. Definíció.** Az `r` nemnegatív egész szám a `v₁,…,v_k` vektorrendszer *rangja*,
ha van a vektorrendszernek `r` elemű lineárisan független részrendszere, és minden `r`-nél
több elemű részrendszere lineárisan függő. Jele a jegyzetben: `r(v₁,…,v_k)`. -/
def RendszerRangja (T : Type*) [Field T] {V : Type*} [AddCommGroup V] [Module T V] {k : ℕ}
    (v : Fin k → V) (r : ℕ) : Prop :=
  (∃ f : Fin r → Fin k, Function.Injective f ∧ LinFuggetlen T (v ∘ f)) ∧
    ∀ m : ℕ, r < m → ∀ f : Fin m → Fin k, Function.Injective f → LinFuggo T (v ∘ f)

/-- A `[v₁,…,v_k]` generált altér mindig altér, és a hozzá tartozó részmodulus véges
dimenziós. -/
instance finiteDimensional_span_range (v : Fin k → V) :
    FiniteDimensional T (Submodule.span T (Set.range v) : Submodule T V) :=
  FiniteDimensional.span_of_finite T (Set.finite_range v)

/-- A generált altér által meghatározott részmodulus maga a `span`. -/
theorem span_generalt_range (v : Fin k → V) :
    (Submodule.span T (Generalt T (Set.range v)) : Submodule T V)
      = Submodule.span T (Set.range v) := by
  rw [generalt_eq_span, Submodule.span_eq]

/-- A `[v₁,…,v_k]` altér dimenziója pontosan a `span` Mathlib-beli dimenziója. -/
theorem alterDimenzioja_generalt_iff (v : Fin k → V) :
    AlterDimenzioja T (Generalt T (Set.range v)) n
      ↔ n = Module.finrank T (Submodule.span T (Set.range v)) := by
  constructor
  · rintro ⟨u, hu⟩
    have := finrank_span_of_alterBazisa hu
    rw [span_generalt_range] at this
    exact this.symm
  · rintro rfl
    have halter : Alter T (Generalt T (Set.range v)) := generalt_alter _
    haveI : FiniteDimensional T
        (Submodule.span T (Generalt T (Set.range v)) : Submodule T V) := by
      rw [span_generalt_range]; infer_instance
    have := alterDimenzioja_span (T := T) halter
    rwa [span_generalt_range] at this

/-- Bármely lineárisan független részrendszer elemszáma legfeljebb `dim [v₁,…,v_k]`. -/
theorem card_le_finrank_of_linFuggetlen (v : Fin k → V) {m : ℕ} (f : Fin m → Fin k)
    (hf : LinFuggetlen T (v ∘ f)) :
    m ≤ Module.finrank T (Submodule.span T (Set.range v)) := by
  set X : Submodule T V := Submodule.span T (Set.range v) with hX
  have hmem : ∀ i : Fin m, v (f i) ∈ X := fun i =>
    Submodule.subset_span ⟨f i, rfl⟩
  have hli : LinearIndependent T (fun i : Fin m => (⟨v (f i), hmem i⟩ : X)) := by
    have hcomp : LinearIndependent T
        (fun i : Fin m => X.subtype ⟨v (f i), hmem i⟩) :=
      (linFuggetlen_iff_linearIndependent _).1 hf
    exact hcomp.of_comp X.subtype
  simpa using hli.fintype_card_le_finrank

/-- Van `dim [v₁,…,v_k]` elemű lineárisan független részrendszer. -/
theorem exists_fuggetlen_reszrendszer (v : Fin k → V) :
    ∃ f : Fin (Module.finrank T (Submodule.span T (Set.range v))) → Fin k,
      Function.Injective f ∧ LinFuggetlen T (v ∘ f) := by
  obtain ⟨b, hbsub, hbspan, hbli⟩ := exists_linearIndependent T (Set.range v)
  have hbfin : b.Finite := (Set.finite_range v).subset hbsub
  haveI : Fintype b := hbfin.fintype
  have hcard : Fintype.card b = Module.finrank T (Submodule.span T (Set.range v)) := by
    have h := finrank_span_eq_card hbli
    rw [Subtype.range_coe_subtype, Set.setOf_mem_eq, hbspan] at h
    exact h.symm
  choose g hg using fun x : b => hbsub x.2
  have hginj : Function.Injective g := by
    intro x y hxy
    apply Subtype.ext
    rw [← hg x, ← hg y, hxy]
  let e : Fin (Module.finrank T (Submodule.span T (Set.range v))) ≃ b :=
    (Fintype.equivFinOfCardEq hcard).symm
  refine ⟨g ∘ e, hginj.comp e.injective, ?_⟩
  have hfun : v ∘ (g ∘ e) = fun i => ((e i : b) : V) := by
    funext i
    exact hg (e i)
  rw [linFuggetlen_iff_linearIndependent, hfun]
  exact hbli.comp e e.injective

/-- **8.9. Tétel.** Bármely `v₁,…,v_k` vektorrendszerre `r(v₁,…,v_k) = dim [v₁,…,v_k]`.

*Bizonyítás (a jegyzet szerint).* Legyen `r = r(v₁,…,v_k)`, és tegyük fel, hogy `v₁,…,v_r`
lineárisan független. Mivel a rendszerben nincs `r`-nél több elemű lineárisan független
részrendszer, `v₁,…,v_r,v_i` lineárisan függő minden `i > r` esetén, ezért (7.3.3 szerint)
`v_i ∈ [v₁,…,v_r]`. Így `v₁,…,v_r` generátorrendszer, tehát bázis a `[v₁,…,v_k]`
altérben. -/
theorem rendszerRangja_iff_alterDimenzioja (v : Fin k → V) :
    RendszerRangja T v r ↔ AlterDimenzioja T (Generalt T (Set.range v)) r := by
  set R := Module.finrank T (Submodule.span T (Set.range v)) with hR
  rw [alterDimenzioja_generalt_iff]
  constructor
  · rintro ⟨⟨f, _, hf⟩, hmax⟩
    have hle : r ≤ R := card_le_finrank_of_linFuggetlen v f hf
    rcases lt_or_eq_of_le hle with hlt | heq
    · exfalso
      obtain ⟨g, hginj, hg⟩ := exists_fuggetlen_reszrendszer (T := T) v
      exact hmax R hlt g hginj hg
    · exact heq
  · rintro rfl
    refine ⟨exists_fuggetlen_reszrendszer v, ?_⟩
    intro m hm f _ hf
    exact absurd (card_le_finrank_of_linFuggetlen v f hf) (by omega)

/-- A vektorrendszer rangja egyértelmű. -/
theorem rendszerRangja_egyertelmu {v : Fin k → V} (h₁ : RendszerRangja T v m)
    (h₂ : RendszerRangja T v n) : m = n := by
  rw [rendszerRangja_iff_alterDimenzioja] at h₁ h₂
  exact alterDimenzio_egyertelmu h₁ h₂

/-! ## 8.10–8.12: ekvivalens vektorrendszerek és elemi átalakítások -/

/-- **8.10. Definíció.** Két vektorrendszer *ekvivalens*, ha mindkét rendszer bármelyik
vektora megkapható a másik vektorrendszer lineáris kombinációjaként. -/
def Ekvivalens (T : Type*) [Field T] {V : Type*} [AddCommGroup V] [Module T V] {k l : ℕ}
    (v : Fin k → V) (w : Fin l → V) : Prop :=
  (∀ i, v i ∈ Generalt T (Set.range w)) ∧ (∀ j, w j ∈ Generalt T (Set.range v))

/-- Két generált altér egyenlőségének kényelmes kritériuma. -/
theorem generalt_eq_of_subset (v : Fin k → V) (w : Fin l → V)
    (h₁ : ∀ i, v i ∈ Generalt T (Set.range w)) (h₂ : ∀ j, w j ∈ Generalt T (Set.range v)) :
    Generalt T (Set.range v) = Generalt T (Set.range w) := by
  refine Set.Subset.antisymm ?_ ?_
  · exact generalt_minimal (generalt_alter _) (by rintro x ⟨i, rfl⟩; exact h₁ i)
  · exact generalt_minimal (generalt_alter _) (by rintro x ⟨j, rfl⟩; exact h₂ j)

/-- **8.10. Definíció (megjegyzés).** Két vektorrendszer pontosan akkor ekvivalens, ha
ugyanazt az alteret generálják. -/
theorem ekvivalens_iff_generalt_eq (v : Fin k → V) (w : Fin l → V) :
    Ekvivalens T v w ↔ Generalt T (Set.range v) = Generalt T (Set.range w) := by
  constructor
  · rintro ⟨h₁, h₂⟩
    exact generalt_eq_of_subset v w h₁ h₂
  · intro h
    constructor
    · intro i
      rw [← h]
      exact subset_generalt _ ⟨i, rfl⟩
    · intro j
      rw [h]
      exact subset_generalt _ ⟨j, rfl⟩

/-- **8.11. Definíció.** A vektorrendszerek *elemi átalakításai*:

* **(8.11.1)** a rendszer valamelyik tagját a `λ ≠ 0` skalárszorosával helyettesítjük;
* **(8.11.2)** a rendszer valamelyik tagját ezen vektor és a rendszer egy másik vektora
  (tetszőleges) skalárszorosának összegével helyettesítjük;
* **(8.11.3)** elhagyjuk a rendszerből a nullvektorokat. -/
inductive ElemiAtalakitas (T : Type*) [Field T] {V : Type*} [AddCommGroup V] [Module T V] :
    {k l : ℕ} → (Fin k → V) → (Fin l → V) → Prop
  | skalarszoros {k : ℕ} (v : Fin k → V) (i : Fin k) (c : T) (hc : c ≠ 0) :
      ElemiAtalakitas T v (Function.update v i (c • v i))
  | hozzaadas {k : ℕ} (v : Fin k → V) (i j : Fin k) (hij : i ≠ j) (c : T) :
      ElemiAtalakitas T v (Function.update v i (v i + c • v j))
  | nullvektorElhagyas {k : ℕ} (v : Fin (k + 1) → V) (i : Fin (k + 1)) (hi : v i = 0) :
      ElemiAtalakitas T v (fun j : Fin k => v (i.succAbove j))

/-- **8.12. Következmény (első fele).** Az elemi átalakítások a vektorrendszert vele
ekvivalens vektorrendszerbe viszik át — azaz nem változtatják meg a generált alteret. -/
theorem generalt_eq_of_elemiAtalakitas {v : Fin k → V} {w : Fin l → V}
    (h : ElemiAtalakitas T v w) :
    Generalt T (Set.range v) = Generalt T (Set.range w) := by
  induction h with
  | skalarszoros v i c hc =>
      refine generalt_eq_of_subset _ _ (fun m => ?_) (fun m => ?_)
      · rcases eq_or_ne m i with rfl | hm
        · have hmem : (c • v m) ∈ Generalt T (Set.range (Function.update v m (c • v m))) :=
            subset_generalt _ ⟨m, by simp⟩
          have := (generalt_alter (T := T)
            (Set.range (Function.update v m (c • v m)))).smul_mem c⁻¹ hmem
          rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at this
        · exact subset_generalt _ ⟨m, by rw [Function.update_of_ne hm]⟩
      · rcases eq_or_ne m i with rfl | hm
        · rw [Function.update_self]
          exact (generalt_alter (T := T) (Set.range v)).smul_mem c (subset_generalt _ ⟨m, rfl⟩)
        · rw [Function.update_of_ne hm]
          exact subset_generalt _ ⟨m, rfl⟩
  | hozzaadas v i j hij c =>
      have hwj : Function.update v i (v i + c • v j) j = v j :=
        Function.update_of_ne (Ne.symm hij) _ _
      refine generalt_eq_of_subset _ _ (fun m => ?_) (fun m => ?_)
      · rcases eq_or_ne m i with rfl | hm
        · have h₁ : (v m + c • v j) ∈
              Generalt T (Set.range (Function.update v m (v m + c • v j))) :=
            subset_generalt _ ⟨m, by simp⟩
          have h₂ : v j ∈ Generalt T (Set.range (Function.update v m (v m + c • v j))) :=
            subset_generalt _ ⟨j, hwj⟩
          have := (generalt_alter (T := T)
            (Set.range (Function.update v m (v m + c • v j)))).add_mem h₁
              ((generalt_alter (T := T) _).smul_mem (-c) h₂)
          simpa using this
        · exact subset_generalt _ ⟨m, by rw [Function.update_of_ne hm]⟩
      · rcases eq_or_ne m i with rfl | hm
        · rw [Function.update_self]
          exact (generalt_alter (T := T) (Set.range v)).add_mem (subset_generalt _ ⟨m, rfl⟩)
            ((generalt_alter (T := T) _).smul_mem c (subset_generalt _ ⟨j, rfl⟩))
        · rw [Function.update_of_ne hm]
          exact subset_generalt _ ⟨m, rfl⟩
  | nullvektorElhagyas v i hi =>
      refine generalt_eq_of_subset _ _ (fun m => ?_) (fun m => ?_)
      · rcases eq_or_ne m i with rfl | hm
        · rw [hi]
          exact (generalt_alter (T := T) _).zero_mem
        · obtain ⟨m', rfl⟩ := Fin.exists_succAbove_eq hm
          exact subset_generalt _ ⟨m', rfl⟩
      · exact subset_generalt _ ⟨i.succAbove m, rfl⟩

/-- **8.12. Következmény (első fele).** Az elemi átalakítások ekvivalens vektorrendszerbe
visznek át. -/
theorem ekvivalens_of_elemiAtalakitas {v : Fin k → V} {w : Fin l → V}
    (h : ElemiAtalakitas T v w) : Ekvivalens T v w :=
  (ekvivalens_iff_generalt_eq v w).2 (generalt_eq_of_elemiAtalakitas h)

/-- **8.12. Következmény (második fele).** Ekvivalens vektorrendszerek rangja megegyezik. -/
theorem rendszerRangja_of_ekvivalens {v : Fin k → V} {w : Fin l → V}
    (h : Ekvivalens T v w) (hr : RendszerRangja T v r) : RendszerRangja T w r := by
  rw [rendszerRangja_iff_alterDimenzioja] at hr ⊢
  rwa [← (ekvivalens_iff_generalt_eq v w).1 h]

/-- **8.12. Következmény.** Az elemi átalakítások megőrzik a vektorrendszer rangját. -/
theorem rendszerRangja_of_elemiAtalakitas {v : Fin k → V} {w : Fin l → V}
    (h : ElemiAtalakitas T v w) (hr : RendszerRangja T v r) : RendszerRangja T w r :=
  rendszerRangja_of_ekvivalens (ekvivalens_of_elemiAtalakitas h) hr

/-- **8.11. Definíció (megjegyzés).** Alkalmasan választott **négy** elemi átalakítással a
vektorrendszer bármelyik két vektora felcserélhető:

`u, v ↝ u − v, v ↝ u − v, u ↝ −v, u ↝ v, u`. -/
theorem csere_negy_elemi_lepessel (v : Fin k → V) {i j : Fin k} (hij : i ≠ j) :
    Relation.ReflTransGen (fun a b : Fin k → V => ElemiAtalakitas T a b) v
      (v ∘ Equiv.swap i j) := by
  classical
  set v₁ : Fin k → V := Function.update v i (v i + (-1 : T) • v j) with hv₁
  set v₂ : Fin k → V := Function.update v₁ j (v₁ j + (1 : T) • v₁ i) with hv₂
  set v₃ : Fin k → V := Function.update v₂ i (v₂ i + (-1 : T) • v₂ j) with hv₃
  set v₄ : Fin k → V := Function.update v₃ i ((-1 : T) • v₃ i) with hv₄
  have h₁ : ElemiAtalakitas T v v₁ := ElemiAtalakitas.hozzaadas v i j hij (-1)
  have h₂ : ElemiAtalakitas T v₁ v₂ := ElemiAtalakitas.hozzaadas v₁ j i (Ne.symm hij) 1
  have h₃ : ElemiAtalakitas T v₂ v₃ := ElemiAtalakitas.hozzaadas v₂ i j hij (-1)
  have h₄ : ElemiAtalakitas T v₃ v₄ :=
    ElemiAtalakitas.skalarszoros v₃ i (-1) (by simp)
  -- a négy lépés eredménye éppen az `i` és `j` indexű vektorok felcserélése
  have hv₁i : v₁ i = v i - v j := by rw [hv₁, Function.update_self]; module
  have hv₁j : v₁ j = v j := by rw [hv₁, Function.update_of_ne (Ne.symm hij)]
  have hv₂i : v₂ i = v i - v j := by rw [hv₂, Function.update_of_ne hij, hv₁i]
  have hv₂j : v₂ j = v i := by
    rw [hv₂, Function.update_self, hv₁i, hv₁j]; module
  have hv₃i : v₃ i = -v j := by
    rw [hv₃, Function.update_self, hv₂i, hv₂j]; module
  have hv₃j : v₃ j = v i := by rw [hv₃, Function.update_of_ne (Ne.symm hij), hv₂j]
  have hswap : v₄ = v ∘ Equiv.swap i j := by
    funext m
    rcases eq_or_ne m i with rfl | hmi
    · rw [hv₄, Function.update_self, hv₃i]
      simp
    rcases eq_or_ne m j with rfl | hmj
    · rw [hv₄, Function.update_of_ne hmi, hv₃j]
      simp
    · rw [hv₄, Function.update_of_ne hmi, hv₃, Function.update_of_ne hmi,
        hv₂, Function.update_of_ne hmj, hv₁, Function.update_of_ne hmi]
      simp [Equiv.swap_apply_of_ne_of_ne hmi hmj]
  rw [← hswap]
  exact (((Relation.ReflTransGen.refl.tail h₁).tail h₂).tail h₃).tail h₄

end Ch08b
end SzaboLinAlg
