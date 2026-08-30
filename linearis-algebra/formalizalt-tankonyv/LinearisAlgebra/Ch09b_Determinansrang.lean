import LinearisAlgebra.Ch09_MatrixRang

/-!
# Szabó László: Bevezetés a lineáris algebrába — 9. fejezet (folytatás): determinánsrang

Ez a modul a 9. fejezet hiányzó részét, a **determinánsrangot** formalizálja, és
teljessé teszi a **9.2. Mátrixok rangszámtételét**: `r_o(A) = r_s(A) = r_d(A)`.

* **9.1. Definíció (folytatás).** Az `A` mátrix *`r`-edrendű aldeterminánsán* a
  következőképpen kapható determinánsokat értjük: kijelöljük a mátrix `r` sorát és
  `r` oszlopát, majd e sorok és oszlopok találkozásában lévő elemekből alkotott
  `r × r`-es mátrix determinánsát képezzük (`aldeterminans`). Az `A` mátrix
  *determinánsrangja* `r`, ha van `A`-ban `r`-edrendű nem nulla aldetermináns, és
  `A`-ban minden `r`-nél nagyobb rendű aldetermináns nulla (`DeterminansRangja`).
* **9.2. Mátrixok rangszámtétele (a determinánsrangra vonatkozó rész).**
  `DeterminansRangja A r ↔ r = rang A` (`determinansRangja_iff`), speciálisan a
  determinánsrang létezik és egyenlő az oszlop-, illetve a sorranggal
  (`determinansRangja_rang`, `rangszamtetel_teljes`).

A bizonyítás gondolatmenete (a jegyzetétől eltérően nem elemi átalakításokkal, hanem
közvetlenül a lineáris függetlenség fogalmával):

* ha egy `s`-edrendű aldetermináns nem nulla, akkor a hozzá tartozó `s` oszlop
  lineárisan független, tehát `s ≤ r(A)` — vagyis `r(A) < s` esetén minden
  `s`-edrendű aldetermináns nulla;
* megfordítva, az `A` oszlopvektorai közül kiválasztható `r(A)` lineárisan független,
  az így kapott `m × r(A)`-as mátrix sorai közül pedig `r(A)` lineárisan független,
  és az ezek metszetében álló `r(A) × r(A)`-as mátrix determinánsa a 9.4. Következmény
  szerint nem nulla.
-/

namespace SzaboLinAlg
namespace Ch09

open scoped BigOperators
open Matrix SzaboLinAlg.Ch02 SzaboLinAlg.Ch03

variable {T : Type*} [Field T] {m n : ℕ}

/-! ## 9.1. Definíció: aldetermináns és determinánsrang -/

/-- **9.1. Definíció.** Az `A` mátrix *`r`-edrendű aldeterminánsa*: kijelöljük a mátrix
`i 1, …, i r` sorát és `j 1, …, j r` oszlopát, és vesszük a metszetükben álló `r × r`-es
mátrix determinánsát. -/
noncomputable def aldeterminans (A : Matrix' T m n) {r : ℕ} (i : Fin r → Fin m)
    (j : Fin r → Fin n) : T := det' (A.submatrix i j)

theorem aldeterminans_eq_det (A : Matrix' T m n) {r : ℕ} (i : Fin r → Fin m)
    (j : Fin r → Fin n) : aldeterminans A i j = (A.submatrix i j).det :=
  det'_eq_det _

/-- **9.1. Definíció.** Az `A` mátrix *determinánsrangja* `r`, ha van `A`-ban
`r`-edrendű nem nulla (nemeltűnő) aldetermináns, és `A`-ban minden `r`-nél nagyobb
rendű aldetermináns nulla. (A sorok és oszlopok kijelölését — a jegyzethez híven —
szigorúan növekedő `i₁ < … < i_r`, illetve `j₁ < … < j_r` indexsorozat adja meg.) -/
def DeterminansRangja (A : Matrix' T m n) (r : ℕ) : Prop :=
  (∃ (i : Fin r → Fin m) (j : Fin r → Fin n),
      StrictMono i ∧ StrictMono j ∧ aldeterminans A i j ≠ 0) ∧
  (∀ s : ℕ, r < s → ∀ (i : Fin s → Fin m) (j : Fin s → Fin n),
      StrictMono i → StrictMono j → aldeterminans A i j = 0)

/-! ## Segédeszközök -/

theorem rang_transpose (A : Matrix' T m n) : rang Aᵀ = rang A := by
  rw [rang_eq_rank, rang_eq_rank, Matrix.rank_transpose]

/-- Ha egy `s`-edrendű aldetermináns nem nulla, akkor a benne szereplő `s` oszlop
lineárisan független (`A` oszlopvektorainak rendszerében). -/
theorem linearIndependent_oszlopok_of_det_ne_zero (A : Matrix' T m n) {s : ℕ}
    {i : Fin s → Fin m} {j : Fin s → Fin n} (h : (A.submatrix i j).det ≠ 0) :
    LinearIndependent T (fun k => oszlopRendszer A (j k)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hmul : (A.submatrix i j).mulVec c = 0 := by
    funext l
    have hl := congrFun hc (i l)
    simp only [Finset.sum_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul,
      oszlopRendszer] at hl
    simpa [Matrix.mulVec, dotProduct, mul_comm] using hl
  have := Matrix.eq_zero_of_mulVec_eq_zero h hmul
  intro k
  exact congrFun this k

/-- Ha `A` oszlopvektorai közül `s` lineárisan független, akkor `s ≤ r(A)`. -/
theorem le_rang_of_linearIndependent_oszlopok (A : Matrix' T m n) {s : ℕ} {j : Fin s → Fin n}
    (h : LinearIndependent T (fun k => oszlopRendszer A (j k))) : s ≤ rang A := by
  have hmem : ∀ k, oszlopRendszer A (j k) ∈
      Submodule.span T (Set.range (oszlopRendszer A)) := fun k =>
    Submodule.subset_span ⟨j k, rfl⟩
  have h' : LinearIndependent T
      (fun k => (⟨oszlopRendszer A (j k), hmem k⟩ :
        Submodule.span T (Set.range (oszlopRendszer A)))) :=
    LinearIndependent.of_comp (Submodule.span T (Set.range (oszlopRendszer A))).subtype h
  have hcard := h'.fintype_card_le_finrank
  simpa [rang, oszlopRang] using hcard

/-- **A 9.2. bizonyításának egyik fele.** Ha `r(A) < s`, akkor `A` minden `s`-edrendű
aldeterminánsa nulla. -/
theorem aldeterminans_eq_zero_of_rang_lt (A : Matrix' T m n) {s : ℕ} (hs : rang A < s)
    (i : Fin s → Fin m) (j : Fin s → Fin n) : aldeterminans A i j = 0 := by
  rw [aldeterminans_eq_det]
  by_contra h
  exact absurd (le_rang_of_linearIndependent_oszlopok A
    (linearIndependent_oszlopok_of_det_ne_zero A h)) (by omega)

/-- Az `A` mátrix oszlopvektorai közül kiválasztható `r(A)` darab lineárisan független.

*Bizonyítás.* Az oszlopvektorok halmazából kiválasztható olyan lineárisan független
részhalmaz, amely ugyanazt az alteret generálja; ennek elemszáma éppen az altér
dimenziója, azaz `r(A)`. -/
theorem exists_fuggetlen_oszlopok (A : Matrix' T m n) {r : ℕ} (hr : rang A = r) :
    ∃ j : Fin r → Fin n, Function.Injective j ∧
      LinearIndependent T (fun k => oszlopRendszer A (j k)) := by
  classical
  obtain ⟨b, hbsub, hbspan, hbli⟩ :=
    exists_linearIndependent T (Set.range (oszlopRendszer A))
  have hbfin : b.Finite := Set.Finite.subset (Set.finite_range _) hbsub
  haveI : Fintype b := hbfin.fintype
  have hcard : Fintype.card b = r := by
    have h1 : Module.finrank T (Submodule.span T b) = b.toFinset.card :=
      finrank_span_set_eq_card hbli
    rw [hbspan] at h1
    rw [← Set.toFinset_card]
    rw [← h1, ← hr, rang, oszlopRang]
  set e : Fin r ≃ b := (Fintype.equivFinOfCardEq hcard).symm with he
  have hex : ∀ k : Fin r, ∃ jj : Fin n, oszlopRendszer A jj = ((e k : Fin m → T)) := by
    intro k
    obtain ⟨jj, hjj⟩ := hbsub (e k).2
    exact ⟨jj, hjj⟩
  choose j hj using hex
  refine ⟨j, ?_, ?_⟩
  · intro k₁ k₂ hk
    have : ((e k₁ : Fin m → T)) = ((e k₂ : Fin m → T)) := by
      rw [← hj k₁, ← hj k₂, hk]
    exact e.injective (Subtype.ext this)
  · have : (fun k => oszlopRendszer A (j k)) = (fun k => ((e k : Fin m → T))) := by
      funext k; exact hj k
    rw [this]
    exact hbli.comp e e.injective

/-- **A 9.2. bizonyításának másik fele.** Van `A`-ban `r(A)`-adrendű nem nulla
aldetermináns.

*Bizonyítás.* Válasszunk ki `r = r(A)` lineárisan független oszlopot; az így kapott
`m × r`-es `B` mátrix rangja `r`, ezért `B` sorvektorai közül is kiválasztható `r`
lineárisan független. Az ezek metszetében álló `r × r`-es mátrix sorvektorai
lineárisan függetlenek, tehát a 9.4. Következmény szerint a determinánsa nem nulla. -/
theorem exists_det_ne_zero (A : Matrix' T m n) {r : ℕ} (hr : rang A = r) :
    ∃ (i : Fin r → Fin m) (j : Fin r → Fin n),
      Function.Injective i ∧ Function.Injective j ∧ (A.submatrix i j).det ≠ 0 := by
  classical
  obtain ⟨j, hjinj, hj⟩ := exists_fuggetlen_oszlopok A hr
  set B : Matrix' T m r := A.submatrix id j with hB
  have hBcol : oszlopRendszer B = fun k => oszlopRendszer A (j k) := rfl
  have hBrang : rang B = r := by
    rw [rang, oszlopRang, hBcol, finrank_span_eq_card hj, Fintype.card_fin]
  obtain ⟨i, hiinj, hi⟩ := exists_fuggetlen_oszlopok Bᵀ (by rw [rang_transpose, hBrang])
  refine ⟨i, j, hiinj, hjinj, ?_⟩
  have hrows : LinearIndependent T (A.submatrix i j).row := by
    have : (A.submatrix i j).row = fun k => oszlopRendszer Bᵀ (i k) := rfl
    rw [this]
    exact hi
  have hunit : IsUnit (A.submatrix i j) := Matrix.linearIndependent_rows_iff_isUnit.mp hrows
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero] at hunit
  exact hunit

/-- Injektív indexsorozat helyett mindig választható szigorúan növekedő is: van olyan
`i'` szigorúan növekedő indexsorozat és `σ` permutáció, hogy `i' = i ∘ σ`. -/
theorem exists_strictMono_comp_perm {r : ℕ} {i : Fin r → Fin m} (hi : Function.Injective i) :
    ∃ (i' : Fin r → Fin m) (σ : Equiv.Perm (Fin r)), StrictMono i' ∧ i' = i ∘ σ := by
  classical
  set S : Finset (Fin m) := Finset.image i Finset.univ with hS
  have hcard : S.card = r := by
    rw [hS, Finset.card_image_of_injective _ hi, Finset.card_univ, Fintype.card_fin]
  set i' : Fin r → Fin m := fun k => ((S.orderIsoOfFin hcard k : Fin m)) with hi'
  have hmono : StrictMono i' := by
    intro a b hab
    exact (S.orderIsoOfFin hcard).strictMono hab
  have hrange : Set.range i' = Set.range i := by
    have h1 : Set.range i' = (S : Set (Fin m)) := by
      rw [hi', show (fun k => ((S.orderIsoOfFin hcard k : Fin m))) =
        Subtype.val ∘ (S.orderIsoOfFin hcard) from rfl, Set.range_comp,
        (S.orderIsoOfFin hcard).surjective.range_eq, Set.image_univ, Subtype.range_coe]
    have h2 : (S : Set (Fin m)) = Set.range i := by
      rw [hS, Finset.coe_image, Finset.coe_univ, Set.image_univ]
    rw [h1, h2]
  refine ⟨i', Equiv.trans (Equiv.ofInjective i' hmono.injective)
    (Equiv.trans (Equiv.setCongr hrange) (Equiv.ofInjective i hi).symm), hmono, ?_⟩
  funext k
  simp only [Function.comp_apply, Equiv.trans_apply]
  rw [Equiv.apply_ofInjective_symm hi]
  rfl

/-- Sor- és oszloppermutáció nem változtatja meg az aldetermináns eltűnését. -/
theorem det_submatrix_comp_perm_ne_zero (A : Matrix' T m n) {r : ℕ} (i : Fin r → Fin m)
    (j : Fin r → Fin n) (σ τ : Equiv.Perm (Fin r)) :
    (A.submatrix (i ∘ σ) (j ∘ τ)).det ≠ 0 ↔ (A.submatrix i j).det ≠ 0 := by
  classical
  have h1 : A.submatrix (i ∘ σ) (j ∘ τ) =
      (((A.submatrix i j).submatrix id (τ ∘ σ.symm)).submatrix σ σ) := by
    funext a b
    simp [Matrix.submatrix, Function.comp]
  rw [h1, Matrix.det_submatrix_equiv_self σ]
  have h3 : (τ ∘ σ.symm : Fin r → Fin r) = ((σ.symm.trans τ : Equiv.Perm (Fin r)) : _ → _) := rfl
  rw [h3]
  rw [Matrix.det_permute' (σ.symm.trans τ) (A.submatrix i j)]
  have hs : ((Equiv.Perm.sign (σ.symm.trans τ) : ℤ) : T) ≠ 0 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign (σ.symm.trans τ)) with h | h <;>
      simp [h]
  constructor
  · intro h hz
    exact h (by rw [hz, mul_zero])
  · intro h hz
    exact h ((mul_eq_zero.mp hz).resolve_left hs)

/-! ## 9.2. Mátrixok rangszámtétele: a determinánsrangra vonatkozó rész -/

/-- **9.2. Tétel (determinánsrang).** Az `A` mátrix determinánsrangja `r(A)`, azaz
van `A`-ban `r(A)`-adrendű nemeltűnő aldetermináns, és minden nagyobb rendű
aldetermináns nulla. -/
theorem determinansRangja_rang (A : Matrix' T m n) : DeterminansRangja A (rang A) := by
  constructor
  · obtain ⟨i, j, hiinj, hjinj, hdet⟩ := exists_det_ne_zero A rfl
    obtain ⟨i', σ, hi'mono, hi'⟩ := exists_strictMono_comp_perm hiinj
    obtain ⟨j', τ, hj'mono, hj'⟩ := exists_strictMono_comp_perm hjinj
    refine ⟨i', j', hi'mono, hj'mono, ?_⟩
    rw [aldeterminans_eq_det, hi', hj']
    exact (det_submatrix_comp_perm_ne_zero A i j σ τ).2 hdet
  · intro s hs i j _ _
    exact aldeterminans_eq_zero_of_rang_lt A hs i j

/-- **9.2. Tétel (a determinánsrang egyértelműsége).** Ha `A` determinánsrangja `r`,
akkor `r = r(A)`. -/
theorem eq_rang_of_determinansRangja (A : Matrix' T m n) {r : ℕ}
    (h : DeterminansRangja A r) : r = rang A := by
  obtain ⟨⟨i, j, _, _, hne⟩, hzero⟩ := h
  have h1 : r ≤ rang A := by
    rw [aldeterminans_eq_det] at hne
    exact le_rang_of_linearIndependent_oszlopok A
      (linearIndependent_oszlopok_of_det_ne_zero A hne)
  have h2 : rang A ≤ r := by
    by_contra hlt
    push_neg at hlt
    obtain ⟨⟨i', j', hi', hj', hne'⟩, -⟩ := determinansRangja_rang A
    exact hne' (hzero (rang A) hlt i' j' hi' hj')
  omega

/-- **9.2. Mátrixok rangszámtétele (teljes alak).** `A` determinánsrangja pontosan a
mátrix rangja: `DeterminansRangja A r ↔ r = r(A)`. -/
theorem determinansRangja_iff (A : Matrix' T m n) (r : ℕ) :
    DeterminansRangja A r ↔ r = rang A :=
  ⟨eq_rang_of_determinansRangja A, fun h => h ▸ determinansRangja_rang A⟩

/-- **9.2. Mátrixok rangszámtétele.** Tetszőleges `A` mátrix esetén
`r_o(A) = r_s(A) = r_d(A)`: az oszlop- és a sorrang megegyezik, és ez a közös érték
egyben a mátrix determinánsrangja is. -/
theorem rangszamtetel_teljes (A : Matrix' T m n) :
    oszlopRang A = sorRang A ∧ DeterminansRangja A (oszlopRang A) :=
  ⟨(rangszamtetel A).symm, determinansRangja_rang A⟩

end Ch09
end SzaboLinAlg
