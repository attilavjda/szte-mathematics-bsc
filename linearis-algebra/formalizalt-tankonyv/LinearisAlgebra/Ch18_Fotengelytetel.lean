import LinearisAlgebra.Ch17_EuklidesziTerek

/-!
# Szabó László: Bevezetés a lineáris algebrába — 18. fejezet

**Szimmetrikus lineáris transzformációk, a kvadratikus alakok főtengelytétele**
(a jegyzet 85–88. oldala).

* **18.1. Definíció** — szimmetrikus (önadjungált) lineáris transzformáció,
* **18.2. Tétel** — a szimmetrikus transzformáció mátrixa ortonormált bázisban
  szimmetrikus, és megfordítva,
* **18.3. Segédtétel** — szimmetrikus lineáris transzformációnak van sajátérték-
  sajátvektor párja,
* **18.4. Tétel** — van a transzformáció sajátvektoraiból álló ortonormált bázis, s
  ebben a transzformáció mátrixa diagonális,
* **18.5. Következmény** — valós szimmetrikus mátrixhoz van olyan `P` ortogonális
  mátrix, melyre `P⁻¹AP` diagonális,
* **18.6. Kvadratikus alakok főtengelytétele** — euklideszi térben bármely kvadratikus
  alakhoz van olyan ortonormált bázis, melyben az alak kanonikus.

**Megjegyzés a bizonyításokról.** A 18.3. Segédtétel könyvbeli bizonyítása a komplex
számok fölötti karakterisztikus gyök valósságát igazolja. Az itteni felépítésben a valós
szimmetrikus mátrixok ortogonális diagonalizálhatóságát (a `szimmetrikus_matrix_sajatbazis`
tétel, mely a Mathlib spektráltételére épül) használjuk kiindulásként, és ebből
származtatjuk mind a 18.3., mind a 18.4., mind a 18.5. és 18.6. állítást — a könyvbeli
levezetés lépéseit (ortonormált bázisbeli mátrix, báziscsere, kanonikus alak) hűen
követve.
-/

namespace SzaboLinAlg
namespace Ch18

open scoped BigOperators
open SzaboLinAlg.Ch02 SzaboLinAlg.Ch03 SzaboLinAlg.Ch04 SzaboLinAlg.Ch06 SzaboLinAlg.Ch07
  SzaboLinAlg.Ch08 SzaboLinAlg.Ch10 SzaboLinAlg.Ch12 SzaboLinAlg.Ch13 SzaboLinAlg.Ch14
  SzaboLinAlg.Ch15 SzaboLinAlg.Ch17
open Matrix

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}

/-! ## 18.1. Definíció -/

/-- **18.1. Definíció.** A `V` euklideszi tér `φ` lineáris transzformációja
*szimmetrikus* (önadjungált), ha `⟨uφ, v⟩ = ⟨u, vφ⟩` minden `u, v ∈ V` esetén. -/
def SzimmetrikusTranszformacio (b : V → V → ℝ) (f : V → V) : Prop :=
  LinearisLekepezes ℝ f ∧ ∀ u v, b (f u) v = b u (f v)

/-! ## Segédállítások ortonormált bázisban -/

/-- Ortonormált bázisban a belső szorzat a koordinátasorok standard belső szorzata:
`⟨∑xᵢeᵢ, ∑yⱼeⱼ⟩ = ∑ xᵢyᵢ`. -/
theorem bilin_ortonormalt_koordinatas {b : V → V → ℝ} (hb : BelsoSzorzat b)
    {e : Fin n → V} (heon : OrtonormaltRendszer b e) (x y : Fin n → ℝ) :
    b (∑ i, x i • e i) (∑ j, y j • e j) = standardBSZ x y := by
  rw [bilinearis_koordinatas_alak hb.bilin]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · rw [bilinMatrixa_apply, ortonormalt_apply hb heon i i, if_pos rfl, mul_one]
  · intro j _ hj
    rw [bilinMatrixa_apply, ortonormalt_apply hb heon i j, if_neg (Ne.symm hj),
      mul_zero, zero_mul]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-- Ortonormált bázisban a transzformáció mátrixának elemei a `⟨eᵢφ, eⱼ⟩` belső
szorzatok. -/
theorem matrix_elem_eq_bilin {b : V → V → ℝ} (hb : BelsoSzorzat b) {f : V → V}
    {e : Fin n → V} (heon : OrtonormaltRendszer b e) {A : Matrix' ℝ n n}
    (hA : LekepezesMatrixa f e e A) (i j : Fin n) : b (f (e i)) (e j) = A i j := by
  rw [hA i, bilin_kombinacio_left hb.bilin, Finset.sum_eq_single j]
  · rw [ortonormalt_apply hb heon j j, if_pos rfl, mul_one]
  · intro k _ hk
    rw [ortonormalt_apply hb heon k j, if_neg hk, mul_zero]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

/-! ## 18.2. Tétel -/

/-- **18.2. Tétel.** Euklideszi tér lineáris transzformációja pontosan akkor
szimmetrikus, ha (valamely, s így minden) ortonormált bázisbeli mátrixa szimmetrikus.

*Bizonyítás (a könyv szerint).* Ortonormált bázisban `⟨eᵢφ, eⱼ⟩ = aᵢⱼ` és
`⟨eᵢ, eⱼφ⟩ = aⱼᵢ`. Ha `φ` szimmetrikus, akkor `aᵢⱼ = aⱼᵢ`. Megfordítva, ha `A`
szimmetrikus, akkor tetszőleges `u = ∑xᵢeᵢ`, `v = ∑yⱼeⱼ` esetén
`⟨uφ, v⟩ = ∑ᵢ∑ⱼ xᵢyⱼaᵢⱼ = ∑ᵢ∑ⱼ xᵢyⱼaⱼᵢ = ⟨u, vφ⟩`. -/
theorem szimmetrikus_iff_matrix_szimmetrikus {b : V → V → ℝ} (hb : BelsoSzorzat b)
    {f : V → V} (hf : LinearisLekepezes ℝ f) {e : Fin n → V} (he : Bazis ℝ e)
    (heon : OrtonormaltRendszer b e) {A : Matrix' ℝ n n} (hA : LekepezesMatrixa f e e A) :
    SzimmetrikusTranszformacio b f ↔ Szimmetrikus A := by
  constructor
  · rintro ⟨-, hsym⟩
    funext j i
    have h1 : b (f (e i)) (e j) = A i j := matrix_elem_eq_bilin hb heon hA i j
    have h2 : b (f (e j)) (e i) = A j i := matrix_elem_eq_bilin hb heon hA j i
    have h3 : b (f (e i)) (e j) = b (e i) (f (e j)) := hsym _ _
    rw [Matrix.transpose_apply, ← h1, ← h2, h3, hb.symm]
  · intro hAsym
    refine ⟨hf, fun u v => ?_⟩
    set x := koordinatai he u with hx
    set y := koordinatai he v with hy
    have hu : u = ∑ i, x i • e i := koordinatai_spec he u
    have hv : v = ∑ j, y j • e j := koordinatai_spec he v
    have hfu : f u = ∑ i, x i • f (e i) := by
      rw [hu, map_kombinacio hf]
    have hfv : f v = ∑ j, y j • f (e j) := by
      rw [hv, map_kombinacio hf]
    have hleft : b (f u) v = ∑ i, ∑ j, x i * A i j * y j := by
      rw [hfu, hv, bilin_kombinacio_left hb.bilin]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [bilin_kombinacio_right hb.bilin, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [matrix_elem_eq_bilin hb heon hA i j]
      ring
    have hright : b u (f v) = ∑ j, ∑ i, y j * A j i * x i := by
      rw [hu, hfv, bilin_kombinacio_right hb.bilin]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [bilin_kombinacio_left hb.bilin, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hb.symm (e i) (f (e j)), matrix_elem_eq_bilin hb heon hA j i]
      ring
    rw [hleft, hright, Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
    have : A i j = A j i := congrFun (congrFun hAsym j) i
    rw [this]
    ring

/-! ## A valós szimmetrikus mátrixok ortogonális diagonalizálása -/

/-- Valós szimmetrikus mátrixhoz van olyan `S` ortogonális mátrix, melynek sorai az `A`
mátrix sajátvektorai, és `SASᵀ` diagonális. (Ez a 18.3–18.5. állítások közös magja.) -/
theorem szimmetrikus_matrix_sajatbazis {A : Matrix' ℝ n n} (hA : Szimmetrikus A) :
    ∃ (S : Matrix' ℝ n n) (d : Fin n → ℝ), OrtogonalisMatrix S ∧
      (∀ i, Matrix.vecMul (S i) A = d i • S i) ∧ S * A * Sᵀ = Matrix.diagonal d := by
  have hAT : Aᵀ = A := hA
  have hH : A.IsHermitian := by
    unfold Matrix.IsHermitian
    ext i j
    rw [Matrix.conjTranspose_apply, RCLike.star_def, RCLike.conj_to_real]
    exact congrFun (congrFun hAT i) j
  set S : Matrix' ℝ n n :=
    fun i j => (hH.eigenvectorBasis i : EuclideanSpace ℝ (Fin n)) j with hS
  have hSS : S * Sᵀ = 1 := by
    ext i j
    have hon := orthonormal_iff_ite.1 hH.eigenvectorBasis.orthonormal i j
    rw [PiLp.inner_apply] at hon
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply]
    rw [← hon]
    exact Finset.sum_congr rfl fun k _ => by simp [hS, mul_comm]
  have heig : ∀ i, Matrix.vecMul (S i) A = hH.eigenvalues i • S i := by
    intro i
    have h := hH.mulVec_eigenvectorBasis i
    show Matrix.vecMul _ A = _
    rw [← Matrix.mulVec_transpose, hAT]
    exact h
  refine ⟨S, hH.eigenvalues, (ortogonalisMatrix_iff S).2 hSS, heig, ?_⟩
  ext i j
  have hrow : (S * A) i = Matrix.vecMul (S i) A := rfl
  have : (S * A * Sᵀ) i j = ∑ k, Matrix.vecMul (S i) A k * S j k := by
    simp only [Matrix.mul_apply, Matrix.transpose_apply]
    rw [← hrow]
    rfl
  rw [this, heig i]
  have hsum : ∑ k, (hH.eigenvalues i • S i) k * S j k
      = hH.eigenvalues i * ∑ k, S i k * S j k := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by simp [mul_assoc]
  rw [hsum]
  have hij : ∑ k, S i k * S j k = if i = j then 1 else 0 := by
    have := congrFun (congrFun hSS i) j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] at this
    exact this
  rw [hij]
  by_cases h : i = j
  · subst h
    simp
  · simp [h]

/-! ## 18.5. Következmény -/

/-- **18.5. Következmény.** Bármely `A` valós szimmetrikus mátrixhoz megadható olyan `P`
ortogonális mátrix, melyre `P⁻¹AP` diagonális (`P⁻¹ = Pᵀ`).

*Bizonyítás (a könyv szerint).* Az `ℝⁿ` euklideszi térben tekintsük azt a `φ`
transzformációt, melynek mátrixa a standard ortonormált bázisban `A`; a 18.2. Tétel
szerint `φ` szimmetrikus, így a 18.4. Tétel szerint van sajátvektoraiból álló ortonormált
bázis, és az áttérés mátrixa ortogonális. -/
theorem letezik_ortogonalis_diagonalizalo {A : Matrix' ℝ n n} (hA : Szimmetrikus A) :
    ∃ P : Matrix' ℝ n n, OrtogonalisMatrix P ∧ Inverze P Pᵀ ∧ Diagonalis (Pᵀ * A * P) := by
  obtain ⟨S, d, hSort, -, hdiag⟩ := szimmetrikus_matrix_sajatbazis hA
  have hSS : S * Sᵀ = 1 := (ortogonalisMatrix_iff S).1 hSort
  refine ⟨Sᵀ, (ortogonalisMatrix_iff Sᵀ).2 ?_, ?_, ?_⟩
  · rw [Matrix.transpose_transpose]
    exact mul_eq_one_comm.1 hSS
  · refine ⟨?_, ?_⟩
    · rw [Matrix.transpose_transpose]
      exact hSS
    · rw [Matrix.transpose_transpose]
      exact mul_eq_one_comm.1 hSS
  · intro i j hij
    rw [Matrix.transpose_transpose, hdiag]
    exact Matrix.diagonal_apply_ne _ hij

/-! ## 18.4. Tétel -/

/-- Ortogonális mátrixszal végrehajtott báziscsere ortonormált bázist ortonormált
bázisba visz. -/
theorem ortogonalis_baziscsere {b : V → V → ℝ} (hb : BelsoSzorzat b) {e : Fin n → V}
    (he : Bazis ℝ e) (heon : OrtonormaltRendszer b e) {S : Matrix' ℝ n n}
    (hS : OrtogonalisMatrix S) :
    Bazis ℝ (fun i => ∑ j, S i j • e j) ∧
      OrtonormaltRendszer b (fun i => ∑ j, S i j • e j) := by
  have hSS : S * Sᵀ = 1 := (ortogonalisMatrix_iff S).1 hS
  have hentry : ∀ i j, ∑ k, S i k * S j k = if i = j then 1 else 0 := by
    intro i j
    have := congrFun (congrFun hSS i) j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] at this
    exact this
  have hbval : ∀ i j, b (∑ k, S i k • e k) (∑ p, S j p • e p) = if i = j then 1 else 0 := by
    intro i j
    rw [bilin_ortonormalt_koordinatas hb heon]
    rw [standardBSZ]
    exact hentry i j
  have hdet : det' S ≠ 0 := by
    rw [det'_eq_det]
    intro h0
    have : (S * Sᵀ).det = 0 := by
      rw [Matrix.det_mul, Matrix.det_transpose, h0, mul_zero]
    rw [hSS, Matrix.det_one] at this
    exact one_ne_zero this
  refine ⟨bazis_kombinacio he hdet, fun i j hij => ?_, fun i => ?_⟩
  · rw [hbval i j, if_neg hij]
  · rw [hossz, hbval i i, if_pos rfl, Real.sqrt_one]

/-- **18.4. Tétel.** Euklideszi tér tetszőleges `φ` szimmetrikus lineáris
transzformációja esetén a térnek van `φ` sajátvektoraiból álló ortonormált bázisa; ebben
a bázisban `φ` mátrixa diagonális, főátlójában a sajátértékekkel.

*Bizonyítás.* Vegyünk egy `ℰ` ortonormált bázist (17.8.); a 18.2. Tétel szerint `φ`
mátrixa, `A`, szimmetrikus. Az `A`-hoz tartozó ortogonális `S` mátrix soraiból képzett
`e'ᵢ = ∑ⱼ sᵢⱼeⱼ` vektorrendszer ortonormált bázis, és `e'ᵢφ = λᵢe'ᵢ`. -/
theorem letezik_sajatvektor_ortonormalt_bazis {b : V → V → ℝ} (hb : BelsoSzorzat b)
    {f : V → V} (hf : SzimmetrikusTranszformacio b f) {e : Fin n → V} (he : Bazis ℝ e)
    (heon : OrtonormaltRendszer b e) :
    ∃ (e' : Fin n → V) (lam : Fin n → ℝ), Bazis ℝ e' ∧ OrtonormaltRendszer b e' ∧
      ∀ i, f (e' i) = lam i • e' i := by
  set A : Matrix' ℝ n n := matrixa e he f with hAdef
  have hA : LekepezesMatrixa f e e A := lekepezesMatrixa_matrixa e he f
  have hAsym : Szimmetrikus A :=
    (szimmetrikus_iff_matrix_szimmetrikus hb hf.1 he heon hA).1 hf
  obtain ⟨S, d, hSort, heig, -⟩ := szimmetrikus_matrix_sajatbazis hAsym
  obtain ⟨hbaz, hon⟩ := ortogonalis_baziscsere hb he heon hSort
  refine ⟨fun i => ∑ j, S i j • e j, d, hbaz, hon, fun i => ?_⟩
  have hfi : f (∑ j, S i j • e j) = ∑ j, S i j • f (e j) := map_kombinacio hf.1 _ _
  have hexp : ∑ j, S i j • f (e j) = ∑ m, Matrix.vecMul (S i) A m • e m := by
    have h1 : ∀ j, S i j • f (e j) = ∑ m, (S i j * A j m) • e m := by
      intro j
      rw [hA j, Finset.smul_sum]
      exact Finset.sum_congr rfl fun m _ => by rw [smul_smul]
    rw [Finset.sum_congr rfl fun j (_ : j ∈ Finset.univ) => h1 j, Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [← Finset.sum_smul]
    rfl
  rw [hfi, hexp, heig i, Finset.smul_sum]
  exact Finset.sum_congr rfl fun m _ => by simp [smul_smul]

/-! ## 18.3. Segédtétel -/

/-- **18.3. Segédtétel.** Euklideszi tér bármely szimmetrikus lineáris
transzformációjának van sajátérték-sajátvektor párja.

*Bizonyítás (a könyv szerint).* A transzformáció ortonormált bázisbeli `A` mátrixa
szimmetrikus, és az algebra alaptétele szerint `A` karakterisztikus polinomjának van
komplex gyöke, mely a szimmetria miatt valós. (Itt ehelyett a 18.4. Tételre
hivatkozunk: a sajátvektorokból álló ortonormált bázis első eleme megfelelő.) -/
theorem letezik_sajatvektor {b : V → V → ℝ} (hb : BelsoSzorzat b) {f : V → V}
    (hf : SzimmetrikusTranszformacio b f) {m : ℕ} {e : Fin (m + 1) → V}
    (he : Bazis ℝ e) (heon : OrtonormaltRendszer b e) :
    ∃ v : V, Sajatvektor (T := ℝ) f v := by
  obtain ⟨e', lam, -, hon, heig⟩ := letezik_sajatvektor_ortonormalt_bazis hb hf he heon
  refine ⟨e' 0, ?_, lam 0, heig 0⟩
  intro h0
  have := hon.2 0
  rw [h0, (hossz_eq_zero_iff hb 0).2 rfl] at this
  exact zero_ne_one this

/-! ## 18.6. Kvadratikus alakok főtengelytétele -/

/-- **18.6. Kvadratikus alakok főtengelytétele.** Euklideszi térben bármely kvadratikus
alakhoz megadható a tér olyan ortonormált bázisa, melyben a kvadratikus alak kanonikus
alakú.

*Bizonyítás (a könyv szerint).* Legyen `A` a kvadratikus alakhoz tartozó `l`
szimmetrikus bilineáris leképezés mátrixa az `ℰ` ortonormált bázisban. Legyen `φ` az a
lineáris transzformáció, melynek mátrixa ugyanebben a bázisban `A`; a 18.2. Tétel szerint
`φ` szimmetrikus, így a 18.4. Tétel szerint van olyan `ℰ'` ortonormált bázis, melyben
`φ` mátrixa `D` diagonális. Az `ℰ'`-ről `ℰ`-re való áttérés `S` mátrixa ortogonális,
ezért `l` mátrixa az `ℰ'` bázisban `SASᵀ = SAS⁻¹ = D`, azaz diagonális. -/
theorem fotengelytetel {b : V → V → ℝ} (hb : BelsoSzorzat b) {l : V → V → ℝ}
    (hl : SzimmetrikusBilinearis ℝ l) {e : Fin n → V} (he : Bazis ℝ e)
    (heon : OrtonormaltRendszer b e) :
    ∃ e' : Fin n → V, Bazis ℝ e' ∧ OrtonormaltRendszer b e' ∧ KanonikusAlaku l e' := by
  have hAsym : Szimmetrikus (bilinMatrixa e e l) :=
    (Ch15.szimmetrikus_iff_matrix_szimmetrikus hl.1 he).1 hl.2
  obtain ⟨S, d, hSort, -, hdiag⟩ := szimmetrikus_matrix_sajatbazis hAsym
  obtain ⟨hbaz, hon⟩ := ortogonalis_baziscsere hb he heon hSort
  refine ⟨fun i => ∑ j, S i j • e j, hbaz, hon, ?_⟩
  have hatt : AtteresMatrixa (fun i => ∑ j, S i j • e j) e S := fun _ => rfl
  rw [KanonikusAlaku, bilinMatrixa_baziscsere hl.1 hatt, hdiag]
  intro i j hij
  exact Matrix.diagonal_apply_ne _ hij

end Ch18
end SzaboLinAlg
