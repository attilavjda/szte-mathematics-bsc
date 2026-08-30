import LinearisAlgebra.Ch07_LinearisFuggetlenseg

/-!
# Szabó László: Bevezetés a lineáris algebrába — 8. fejezet: Véges dimenziós vektorterek

A jegyzet 8. fejezetének (42–44. oldal) formalizálása:

* **8.1. Definíció** — véges dimenziós vektortér, minimális generátorrendszer, maximális
  lineárisan független vektorrendszer, bázis,
* **8.2. Tétel** — bázis ⟺ minimális generátorrendszer ⟺ maximális lineárisan független
  vektorrendszer,
* **8.3. Tétel** — minden lineárisan független vektorrendszer kiegészíthető bázissá,
  minden generátorrendszer tartalmaz bázist, és bármely két bázis ugyanannyi elemű,
* **8.4. Definíció** — a dimenzió és a koordináták (a koordináták egyértelműsége).

A vektorrendszereket itt is `Fin k → V` alakú függvények írják le.
-/

namespace SzaboLinAlg
namespace Ch08

open scoped BigOperators
open SzaboLinAlg.Ch06 SzaboLinAlg.Ch07

variable {T : Type*} [Field T] {V : Type*} [AddCommGroup V] [Module T V] {k l : ℕ}

/-! ## 8.1. Definíció -/

/-- A `v₁,…,v_k` vektorrendszer *generátorrendszer*, ha `[v₁,…,v_k] = V`. -/
def Generalja (T : Type*) [Field T] {V : Type*} [AddCommGroup V] [Module T V] {k : ℕ}
    (v : Fin k → V) : Prop :=
  Generalt T (Set.range v) = Set.univ

/-- **8.1. Definíció.** A vektortér *véges dimenziós*, ha van véges generátorrendszere. -/
def VegesDimenzios (T : Type*) [Field T] (V : Type*) [AddCommGroup V] [Module T V] : Prop :=
  ∃ (l : ℕ) (w : Fin l → V), Generalja T w

/-- **8.1. Definíció.** *Bázis*: lineárisan független generátorrendszer. -/
def Bazis (T : Type*) [Field T] {V : Type*} [AddCommGroup V] [Module T V] {k : ℕ}
    (v : Fin k → V) : Prop :=
  LinFuggetlen T v ∧ Generalja T v

/-- **8.1. Definíció.** *Minimális generátorrendszer*: generátorrendszer, melyből bármely
vektort elhagyva már nem generátorrendszert kapunk. -/
def MinimalisGenerator (T : Type*) [Field T] {V : Type*} [AddCommGroup V] [Module T V]
    {k : ℕ} (v : Fin k → V) : Prop :=
  Generalja T v ∧ ∀ i, Generalt T (masok v i) ≠ Set.univ

/-- **8.1. Definíció.** *Maximális lineárisan független vektorrendszer*: lineárisan
független, de bármely vektorral bővítve már lineárisan függő. -/
def MaximalisFuggetlen (T : Type*) [Field T] {V : Type*} [AddCommGroup V] [Module T V]
    {k : ℕ} (v : Fin k → V) : Prop :=
  LinFuggetlen T v ∧ ∀ x : V, LinFuggo T (Fin.snoc v x : Fin (k + 1) → V)

/-- Generátorrendszer esetén minden vektor benne van a generált altérben. -/
theorem mem_generalt_of_generalja {v : Fin k → V} (hv : Generalja T v) (x : V) :
    x ∈ Generalt T (Set.range v) := by
  rw [hv]
  trivial

/-- Ha `x` benne van a `v` által generált altérben, akkor `v₁,…,v_k,x` lineárisan függő. -/
theorem linFuggo_snoc_of_mem {v : Fin k → V} {x : V} (hx : x ∈ Generalt T (Set.range v)) :
    LinFuggo T (Fin.snoc v x : Fin (k + 1) → V) := by
  intro hfug
  have hli := (linFuggetlen_iff_linearIndependent _).1 hfug
  have hnot := (linearIndependent_fin_snoc.1 hli).2
  rw [generalt_eq_span] at hx
  exact hnot hx

/-! ## 8.2. Tétel -/

/-- **(8.2.1) ⟹ (8.2.2).** Bázis minimális generátorrendszer. -/
theorem minimalisGenerator_of_bazis {v : Fin k → V} (hv : Bazis T v) :
    MinimalisGenerator T v := by
  refine ⟨hv.2, fun i hi => ?_⟩
  have : v i ∈ Generalt T (masok v i) := by rw [hi]; trivial
  exact linFuggo_of_mem_masok this hv.1

/-- **(8.2.2) ⟹ (8.2.3).** Minimális generátorrendszer maximális lineárisan független
vektorrendszer. -/
theorem maximalisFuggetlen_of_minimalisGenerator {v : Fin k → V}
    (hv : MinimalisGenerator T v) : MaximalisFuggetlen T v := by
  obtain ⟨hgen, hmin⟩ := hv
  have hfug : LinFuggetlen T v := by
    by_contra hdep
    obtain ⟨i, hi⟩ := exists_mem_elozok_of_linFuggo (T := T) hdep
    have hi' : v i ∈ Generalt T (masok v i) := mem_masok_of_mem_elozok hi
    have hsub : Set.range v ⊆ Generalt T (masok v i) := by
      rintro x ⟨j, rfl⟩
      rcases eq_or_ne j i with rfl | hj
      · exact hi'
      · exact subset_generalt _ ⟨j, hj, rfl⟩
    have : Generalt T (Set.range v) ⊆ Generalt T (masok v i) :=
      generalt_minimal (generalt_alter _) hsub
    rw [hgen] at this
    exact hmin i (Set.eq_univ_of_univ_subset this)
  exact ⟨hfug, fun x => linFuggo_snoc_of_mem (mem_generalt_of_generalja hgen x)⟩

/-- **(8.2.3) ⟹ (8.2.1).** Maximális lineárisan független vektorrendszer bázis. -/
theorem bazis_of_maximalisFuggetlen {v : Fin k → V} (hv : MaximalisFuggetlen T v) :
    Bazis T v := by
  refine ⟨hv.1, ?_⟩
  refine Set.eq_univ_of_forall fun x => ?_
  exact mem_generalt_of_snoc_linFuggo hv.1 (hv.2 x)

/-- **8.2. Tétel.** A `v₁,…,v_k` vektorrendszerre ekvivalens: bázis; minimális
generátorrendszer; maximális lineárisan független vektorrendszer. -/
theorem bazis_tfae (v : Fin k → V) :
    List.TFAE [Bazis T v, MinimalisGenerator T v, MaximalisFuggetlen T v] := by
  tfae_have 1 → 2 := minimalisGenerator_of_bazis
  tfae_have 2 → 3 := maximalisFuggetlen_of_minimalisGenerator
  tfae_have 3 → 1 := bazis_of_maximalisFuggetlen
  tfae_finish

/-! ## 8.3. Tétel -/

/-- Segédlemma: ha `v` lineárisan független és `w` generátorrendszer, akkor `k ≤ l`. -/
theorem linFuggetlen_le_generator {v : Fin k → V} {w : Fin l → V} (hv : LinFuggetlen T v)
    (hw : Generalja T w) : k ≤ l :=
  linFuggetlen_card_le hv fun a => mem_generalt_of_generalja hw (v a)

/-- **8.3. Tétel (első rész), segédalak.** Véges dimenziós vektortérben minden lineárisan
független vektorrendszer kiegészíthető bázissá.

*Bizonyítás (a könyv szerint).* Ha a rendszer nem maximális lineárisan független, akkor
alkalmas vektorral bővítve újra lineárisan függetlent kapunk; a 7.5. Következmény szerint
minden lineárisan független rendszer legfeljebb `l` elemű, ezért az eljárás véges sok
lépésben maximális lineárisan független rendszerhez, azaz (8.2. Tétel) bázishoz vezet. -/
theorem bazissa_egeszitheto_aux {w : Fin l → V} (hw : Generalja T w) :
    ∀ (n k : ℕ) (v : Fin k → V), l ≤ k + n → LinFuggetlen T v →
      ∃ (m : ℕ) (u : Fin m → V), Bazis T u ∧ Set.range v ⊆ Set.range u := by
  intro n
  induction n with
  | zero =>
      intro k v hlk hv
      by_cases hmax : ∀ x : V, LinFuggo T (Fin.snoc v x : Fin (k + 1) → V)
      · exact ⟨k, v, bazis_of_maximalisFuggetlen ⟨hv, hmax⟩, subset_rfl⟩
      · exfalso
        push_neg at hmax
        obtain ⟨x, hx⟩ := hmax
        have hx' : LinFuggetlen T (Fin.snoc v x : Fin (k + 1) → V) := not_not.1 hx
        have := linFuggetlen_le_generator hx' hw
        omega
  | succ n ih =>
      intro k v hlk hv
      by_cases hmax : ∀ x : V, LinFuggo T (Fin.snoc v x : Fin (k + 1) → V)
      · exact ⟨k, v, bazis_of_maximalisFuggetlen ⟨hv, hmax⟩, subset_rfl⟩
      · push_neg at hmax
        obtain ⟨x, hx⟩ := hmax
        have hx' : LinFuggetlen T (Fin.snoc v x : Fin (k + 1) → V) := not_not.1 hx
        obtain ⟨m, u, hu, hsub⟩ := ih (k + 1) (Fin.snoc v x) (by omega) hx'
        refine ⟨m, u, hu, ?_⟩
        refine subset_trans ?_ hsub
        rintro y ⟨i, rfl⟩
        exact ⟨i.castSucc, by simp⟩

/-- **8.3. Tétel (első rész).** Véges dimenziós vektortérben minden lineárisan független
vektorrendszer kiegészíthető bázissá (a bázis tartalmazza az eredeti vektorokat). -/
theorem bazissa_egeszitheto (hdim : VegesDimenzios T V) {v : Fin k → V}
    (hv : LinFuggetlen T v) :
    ∃ (m : ℕ) (u : Fin m → V), Bazis T u ∧ Set.range v ⊆ Set.range u := by
  obtain ⟨l, w, hw⟩ := hdim
  exact bazissa_egeszitheto_aux hw l k v (by omega) hv

omit [AddCommGroup V] in
/-- Az `i`-edik tag elhagyásával kapott vektorrendszer értékkészlete éppen a többi tag
halmaza. -/
theorem range_succAbove (w : Fin (l + 1) → V) (i : Fin (l + 1)) :
    Set.range (fun j : Fin l => w (i.succAbove j)) = masok w i := by
  ext x
  constructor
  · rintro ⟨j, rfl⟩
    exact ⟨i.succAbove j, Fin.succAbove_ne i j, rfl⟩
  · rintro ⟨j, hj, rfl⟩
    obtain ⟨j', rfl⟩ := Fin.exists_succAbove_eq hj
    exact ⟨j', rfl⟩

/-- **8.3. Tétel (második rész).** Minden generátorrendszer tartalmaz bázist.

*Bizonyítás (a könyv szerint).* Ha a generátorrendszer nem minimális, akkor alkalmas
vektorának elhagyásával újra generátorrendszert kapunk; az eljárás legfeljebb `l`
lépésben minimális generátorrendszerhez, azaz (8.2. Tétel) bázishoz vezet. -/
theorem generator_tartalmaz_bazist :
    ∀ (l : ℕ) (w : Fin l → V), Generalja T w →
      ∃ (m : ℕ) (u : Fin m → V), Bazis T u ∧ Set.range u ⊆ Set.range w := by
  intro l
  induction l with
  | zero =>
      intro w hw
      refine ⟨0, w, ⟨linFuggetlen_ures w, hw⟩, subset_rfl⟩
  | succ l ih =>
      intro w hw
      by_cases hmin : ∀ i, Generalt T (masok w i) ≠ Set.univ
      · exact ⟨l + 1, w, bazis_of_maximalisFuggetlen
          (maximalisFuggetlen_of_minimalisGenerator ⟨hw, hmin⟩), subset_rfl⟩
      · push_neg at hmin
        obtain ⟨i, hi⟩ := hmin
        have hw' : Generalja T (fun j : Fin l => w (i.succAbove j)) := by
          rw [Generalja, range_succAbove, hi]
        obtain ⟨m, u, hu, hsub⟩ := ih _ hw'
        refine ⟨m, u, hu, subset_trans hsub ?_⟩
        rw [range_succAbove]
        rintro y ⟨j, _, rfl⟩
        exact ⟨j, rfl⟩

/-- **8.3. Tétel (harmadik rész).** Bármely két bázis ugyanannyi elemű.

*Bizonyítás.* A 7.5. Következményt mindkét irányban alkalmazva `k ≤ l` és `l ≤ k`. -/
theorem bazisok_egyenlo_elemszam {u : Fin k → V} {v : Fin l → V} (hu : Bazis T u)
    (hv : Bazis T v) : k = l :=
  le_antisymm (linFuggetlen_le_generator hu.1 hv.2) (linFuggetlen_le_generator hv.1 hu.2)

/-! ## 8.4. Definíció: dimenzió és koordináták -/

/-- **8.4. Definíció.** A véges dimenziós `V` vektortér *dimenziója* `n`, ha van `n` elemű
bázisa (a 8.3. Tétel szerint ez az érték egyértelmű). -/
def Dimenzioja (T : Type*) [Field T] (V : Type*) [AddCommGroup V] [Module T V] (n : ℕ) :
    Prop := ∃ u : Fin n → V, Bazis T u

/-- A dimenzió egyértelmű. -/
theorem dimenzio_egyertelmu {m n : ℕ} (hm : Dimenzioja T V m) (hn : Dimenzioja T V n) :
    m = n := by
  obtain ⟨u, hu⟩ := hm
  obtain ⟨v, hv⟩ := hn
  exact bazisok_egyenlo_elemszam hu hv

/-- **8.4. Definíció.** Bázis esetén minden vektor *egyértelműen* áll elő a bázisvektorok
lineáris kombinációjaként; az együtthatók a vektor koordinátái. -/
theorem koordinatak_egyertelmuek {u : Fin k → V} (hu : Bazis T u) (x : V) :
    ∃! g : Fin k → T, x = ∑ i, g i • u i := by
  have hx : x ∈ Generalt T (Set.range u) := mem_generalt_of_generalja hu.2 x
  obtain ⟨n, w, l, hw, hxsum⟩ := hx
  -- minden `w j` a `u` rendszer valamelyik tagja, ezért `x` felírható `u`-beli
  -- lineáris kombinációként
  have hspan : x ∈ Submodule.span T (Set.range u) := by
    rw [← SetLike.mem_coe, ← generalt_eq_span]
    exact ⟨n, w, l, hw, hxsum⟩
  obtain ⟨g, hg⟩ : ∃ g : Fin k → T, x = ∑ i, g i • u i := by
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun T).1 hspan
    exact ⟨c, hc.symm⟩
  refine ⟨g, hg, fun g' hg' => ?_⟩
  exact egyertelmu_eloallitas hu.1 (by rw [← hg', ← hg])

end Ch08
end SzaboLinAlg
