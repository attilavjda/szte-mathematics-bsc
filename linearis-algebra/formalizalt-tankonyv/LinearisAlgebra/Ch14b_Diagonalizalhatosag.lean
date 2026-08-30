import LinearisAlgebra.Ch14_Sajatertek
import LinearisAlgebra.Ch08b_DimenzioTetel

/-!
# Szabó László: Bevezetés a lineáris algebrába — 14. fejezet (kiegészítés)

**Sajátalterek és diagonalizálhatóság.**

A jegyzet 14. fejezete a sajátérték, a sajátvektor és a karakterisztikus polinom
fogalmánál (14.1–14.4.) megáll; a diagonalizálhatóságot csak a 18. fejezetben, a
szimmetrikus transzformációk ortogonális diagonalizálásaként tárgyalja. Ez a modul a
14. fejezet fogalmaira építve pótolja a hozzájuk szorosan tartozó, a *Lineáris algebra I.*
tematikájában is szereplő általános állításokat:

* a `λ`-hoz tartozó **sajátaltér** és annak altér volta,
* **különböző sajátértékekhez tartozó sajátvektorok lineárisan függetlenek**
  (a szokásos, a jegyzet stílusát követő teljes indukciós bizonyítással),
* egy bázis pontosan akkor áll csupa sajátvektorból (**sajátbázis**), ha a
  transzformáció ebben a bázisban felírt mátrixa **diagonális**,
* következésképpen: ha a transzformációnak `n = dim V` darab különböző sajátértéke van,
  akkor van sajátbázisa, azaz **diagonalizálható**; a mátrixos alakban ez azt jelenti,
  hogy a mátrix hasonló egy diagonális mátrixhoz (13.5. Következmény, 14.3. Tétel).
-/

namespace SzaboLinAlg
namespace Ch14

open scoped BigOperators
open SzaboLinAlg.Ch02 SzaboLinAlg.Ch04 SzaboLinAlg.Ch06 SzaboLinAlg.Ch07 SzaboLinAlg.Ch08
  SzaboLinAlg.Ch08b SzaboLinAlg.Ch10 SzaboLinAlg.Ch12

variable {T : Type*} [Field T] {V : Type*} [AddCommGroup V] [Module T V] {n : ℕ}

/-! ## Sajátaltér -/

/-- A `φ` lineáris transzformáció `λ`-hoz tartozó *sajátaltere*: azon `v` vektorok
halmaza, amelyekre `vφ = λv`. (A `λ` pontosan akkor sajátérték, ha ez a halmaz a
nullvektoron kívül mást is tartalmaz.) -/
def SajatAlter (T : Type*) [Field T] {V : Type*} [AddCommGroup V] [Module T V]
    (f : V → V) (l : T) : Set V := {v | f v = l • v}

/-- A sajátaltér valóban altér: nemüres (tartalmazza a nullvektort), és zárt az
összeadásra és a skalárral való szorzásra. -/
theorem sajatAlter_alter {f : V → V} (hf : LinearisLekepezes T f) (l : T) :
    Alter T (SajatAlter T f l) := by
  have hzero : f 0 = 0 := (toLin hf).map_zero
  refine ⟨⟨0, by simp [SajatAlter, hzero]⟩, ?_, ?_⟩
  · intro u hu v hv
    have : f (u + v) = l • (u + v) := by
      rw [hf.1 u v, hu, hv, smul_add]
    exact this
  · intro c u hu
    have : f (c • u) = l • (c • u) := by
      rw [hf.2 c u, hu, smul_comm]
    exact this

/-- A `λ` pontosan akkor sajátértéke `φ`-nek, ha a hozzá tartozó sajátaltér nem csak a
nullvektorból áll. -/
theorem sajatertek_iff_sajatAlter_ne {f : V → V} (hf : LinearisLekepezes T f) (l : T) :
    Sajatertek T f l ↔ SajatAlter T f l ≠ ({0} : Set V) := by
  constructor
  · rintro ⟨v, hv0, hv⟩ h
    have hmem : v ∈ ({0} : Set V) := h ▸ (hv : v ∈ SajatAlter T f l)
    exact hv0 hmem
  · intro h
    by_contra hcon
    refine h (Set.eq_singleton_iff_unique_mem.2 ⟨?_, ?_⟩)
    · show f (0 : V) = l • (0 : V)
      have h0 : f (0 : V) = 0 := (toLin hf).map_zero
      rw [h0, smul_zero]
    · intro v hv
      by_contra hv0
      exact hcon ⟨v, hv0, hv⟩

/-! ## Különböző sajátértékekhez tartozó sajátvektorok -/

/-- **Tétel.** Ha `v₁,…,v_k` a `φ` lineáris transzformáció sajátvektorai, és a hozzájuk
tartozó `λ₁,…,λ_k` sajátértékek páronként különbözők, akkor `v₁,…,v_k` lineárisan
független.

*Bizonyítás* (teljes indukció `k` szerint). `k = 0`-ra az állítás üres. Tegyük fel, hogy
`k` vektorra igaz, és legyen `∑_{i≤k} γᵢvᵢ = 0`. A `φ` alkalmazásával
`∑_{i≤k} γᵢλᵢvᵢ = 0`; ebből az első egyenlőség `λ_{k+1}`-szeresét kivonva
`∑_{i≤k} γᵢ(λᵢ − λ_{k+1})vᵢ = 0` adódik, ahol az utolsó tag eltűnt. Az indukciós feltevés
szerint `γᵢ(λᵢ − λ_{k+1}) = 0` minden `i ≤ k`-ra, és mivel `λᵢ ≠ λ_{k+1}`, ezért
`γᵢ = 0`. Így `γ_{k+1}v_{k+1} = 0`, és `v_{k+1} ≠ 0` miatt `γ_{k+1} = 0` is teljesül. -/
theorem kulonbozo_sajatertekek_fuggetlen {f : V → V} (hf : LinearisLekepezes T f) :
    ∀ {k : ℕ} (v : Fin k → V) (l : Fin k → T), Function.Injective l →
      (∀ i, v i ≠ 0) → (∀ i, f (v i) = l i • v i) → LinFuggetlen T v := by
  intro k
  induction k with
  | zero => intro v l _ _ _ g _ i; exact absurd i.2 (by omega)
  | succ k ih =>
    intro v l hinj hv0 hsajat g hg
    -- a `φ` alkalmazása az összefüggésre
    have hfg : ∑ i, g i • f (v i) = 0 := by
      have h1 : ∑ i, g i • f (v i) = (toLin hf) (∑ i, g i • v i) := by
        rw [map_sum]
        simp
      rw [h1, hg]
      exact (toLin hf).map_zero
    have hfg' : ∑ i, (g i * l i) • v i = 0 := by
      rw [← hfg]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [hsajat i, mul_smul]
    -- kivonjuk az eredeti összefüggés `λ_{k+1}`-szeresét
    have hsub : ∑ i, (g i * (l i - l (Fin.last k))) • v i = 0 := by
      have hbont : ∑ i, (g i * (l i - l (Fin.last k))) • v i
          = (∑ i, (g i * l i) • v i) - l (Fin.last k) • ∑ i, g i • v i := by
        rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl ?_
        intro i _
        rw [smul_smul, ← sub_smul]
        congr 1
        ring
      rw [hbont, hfg', hg, smul_zero, sub_zero]
    -- az utolsó tag eltűnik, marad egy `k` tagú összefüggés
    have hcast : ∑ i : Fin k, (g i.castSucc * (l i.castSucc - l (Fin.last k)))
        • v i.castSucc = 0 := by
      rw [Fin.sum_univ_castSucc] at hsub
      simpa using hsub
    have hzero : ∀ i : Fin k, g i.castSucc * (l i.castSucc - l (Fin.last k)) = 0 :=
      ih (fun i => v i.castSucc) (fun i => l i.castSucc)
        (fun i j hij => Fin.castSucc_injective k (hinj hij))
        (fun i => hv0 _) (fun i => hsajat _) _ hcast
    have hg0 : ∀ i : Fin k, g i.castSucc = 0 := by
      intro i
      rcases mul_eq_zero.1 (hzero i) with h | h
      · exact h
      · exact absurd (hinj (sub_eq_zero.1 h)) (Fin.castSucc_lt_last i).ne
    -- végül az utolsó együttható is nulla
    have hlast : g (Fin.last k) = 0 := by
      rw [Fin.sum_univ_castSucc] at hg
      have : g (Fin.last k) • v (Fin.last k) = 0 := by
        simpa [hg0] using hg
      rcases smul_eq_zero.1 this with h | h
      · exact h
      · exact absurd h (hv0 _)
    intro i
    rcases Fin.eq_castSucc_or_eq_last i with ⟨j, rfl⟩ | rfl
    · exact hg0 j
    · exact hlast

/-! ## Sajátbázis és diagonalizálhatóság -/

/-- A `v₁,…,v_k` rendszer *sajátbázis*, ha bázis, és minden tagja a `φ` sajátvektora. -/
def SajatBazis (T : Type*) [Field T] {V : Type*} [AddCommGroup V] [Module T V] {k : ℕ}
    (f : V → V) (e : Fin k → V) : Prop :=
  Bazis T e ∧ ∀ i, ∃ l : T, f (e i) = l • e i

/-- **Tétel.** Legyen `A` a `φ` transzformáció mátrixa az `ℰ` bázisban. Az `ℰ` bázis
pontosan akkor áll csupa sajátvektorból, ha `A` diagonális; ekkor `A` főátlójában éppen a
sajátértékek állnak.

*Bizonyítás.* A mátrix definíciója szerint `eᵢφ = ∑ⱼ aᵢⱼeⱼ`. Ha `A` diagonális, akkor a
jobb oldalon csak a `j = i` tag marad, tehát `eᵢφ = aᵢᵢeᵢ`, és `eᵢ ≠ 0` (bázis eleme),
tehát `eᵢ` sajátvektor. Megfordítva, ha `eᵢφ = λeᵢ`, akkor a koordináták egyértelműsége
miatt `aᵢⱼ = 0`, valahányszor `j ≠ i`. -/
theorem sajatBazis_iff_diagonalis {f : V → V} {e : Fin n → V} (he : Bazis T e)
    {A : Matrix' T n n} (hA : LekepezesMatrixa f e e A) :
    SajatBazis T f e ↔ Diagonalis A := by
  constructor
  · rintro ⟨-, hsajat⟩
    intro i j hij
    obtain ⟨l, hl⟩ := hsajat i
    have hkoord : koordinatai he (f (e i)) = A i := koordinatai_eq he (hA i)
    have hkoord' : koordinatai he (f (e i)) = fun j => if j = i then l else 0 := by
      refine koordinatai_eq he ?_
      rw [hl, Finset.sum_congr rfl (g := fun j => if j = i then l • e j else 0)]
      · simp
      · intro j _
        by_cases h : j = i <;> simp [h]
    have := hkoord.symm.trans hkoord'
    have hj := congrFun this j
    simpa [Ne.symm hij] using hj
  · intro hdiag
    refine ⟨he, fun i => ⟨A i i, ?_⟩⟩
    rw [hA i, Finset.sum_congr rfl (g := fun j => if j = i then A i i • e j else 0)]
    · simp
    · intro j _
      by_cases h : j = i
      · simp [h]
      · simp [h, hdiag i j (Ne.symm h)]

/-- **Következmény.** Ha `dim V = n`, és a `φ` lineáris transzformációnak van `n` darab
páronként különböző sajátértéke, akkor a hozzájuk tartozó sajátvektorok sajátbázist
alkotnak, azaz `φ` mátrixa alkalmas bázisban diagonális.

*Bizonyítás.* A különböző sajátértékekhez tartozó sajátvektorok lineárisan függetlenek,
és `n` darab lineárisan független vektor egy `n` dimenziós térben bázist alkot
(8. fejezet). -/
theorem sajatBazis_of_kulonbozo_sajatertekek {f : V → V} (hf : LinearisLekepezes T f)
    (hdim : Dimenzioja T V n) {v : Fin n → V} {l : Fin n → T} (hinj : Function.Injective l)
    (hv0 : ∀ i, v i ≠ 0) (hsajat : ∀ i, f (v i) = l i • v i) : SajatBazis T f v :=
  ⟨bazis_of_linFuggetlen hdim (kulonbozo_sajatertekek_fuggetlen hf v l hinj hv0 hsajat),
    fun i => ⟨l i, hsajat i⟩⟩

end Ch14
end SzaboLinAlg
