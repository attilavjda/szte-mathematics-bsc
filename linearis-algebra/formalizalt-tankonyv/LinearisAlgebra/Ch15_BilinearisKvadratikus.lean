import LinearisAlgebra.Ch14_Sajatertek
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.QuadraticForm.Basic

/-!
# Szabó László: Bevezetés a lineáris algebrába — 15. fejezet

**Bilineáris leképezések és kvadratikus alakok** (a jegyzet 72–77. oldala).

* **15.1. Definíció** — bilineáris leképezés, szimmetrikus bilineáris leképezés,
  a bilineáris leképezés mátrixa és koordinátás alakja `l(u,v) = xAyᵀ`,
* **15.2. Tétel** — `l` pontosan akkor szimmetrikus, ha (valamely, illetve bármely)
  bázisbeli mátrixa szimmetrikus,
* **15.3. Definíció** — kvadratikus alak,
* **15.4. Tétel** — a kvadratikus alak egyértelműen meghatározza a hozzá tartozó
  szimmetrikus bilineáris leképezést (polarizációs formula),
* **15.5. Definíció** — a kvadratikus alak mátrixa és koordinátás alakja, továbbá a
  báziscsere hatása: `B = SASᵀ`, valamint a nemelfajuló lineáris helyettesítés,
* **15.6. Definíció** — a kvadratikus alak rangja, kanonikus alak,
* **15.7. Kvadratikus alakok alaptétele** — minden kvadratikus alak alkalmas bázisban
  kanonikus alakú,
* **15.8. Következmény** — bármely `A` szimmetrikus mátrixhoz van olyan `S` nemelfajuló
  mátrix, amelyre `SASᵀ` diagonális.

A könyv számteste (`T`) mindig `0` karakterisztikájú; ahol a bizonyítás `2`-vel oszt,
ott ezt a `(2 : T) ≠ 0` feltétellel tesszük explicitté.
-/

namespace SzaboLinAlg
namespace Ch15

open scoped BigOperators
open SzaboLinAlg.Ch02 SzaboLinAlg.Ch03 SzaboLinAlg.Ch04 SzaboLinAlg.Ch06 SzaboLinAlg.Ch07
  SzaboLinAlg.Ch08 SzaboLinAlg.Ch09 SzaboLinAlg.Ch10 SzaboLinAlg.Ch12 SzaboLinAlg.Ch13
open Matrix

variable {T : Type*} [Field T] {U V : Type*} [AddCommGroup U] [Module T U]
  [AddCommGroup V] [Module T V] {m n : ℕ}

/-! ## 15.1. Definíció -/

/-- **15.1. Definíció.** Az `l : U × V → T` leképezés *bilineáris*, ha mindkét
változójában additív, és a skalárszorzó mindkét változóból kiemelhető:
`l(u₁+u₂,v) = l(u₁,v)+l(u₂,v)`, `l(u,v₁+v₂) = l(u,v₁)+l(u,v₂)`,
`l(λu,v) = l(u,λv) = λl(u,v)`. -/
def BilinearisLekepezes (T : Type*) [Field T] {U V : Type*} [AddCommGroup U] [Module T U]
    [AddCommGroup V] [Module T V] (l : U → V → T) : Prop :=
  (∀ u₁ u₂ v, l (u₁ + u₂) v = l u₁ v + l u₂ v) ∧
    (∀ u v₁ v₂, l u (v₁ + v₂) = l u v₁ + l u v₂) ∧
      (∀ (c : T) u v, l (c • u) v = c * l u v) ∧
        (∀ (c : T) u v, l u (c • v) = c * l u v)

/-- **15.1. Definíció.** Az `l : V × V → T` bilineáris leképezés *szimmetrikus*, ha
`l(u,v) = l(v,u)` minden `u, v ∈ V` esetén. -/
def SzimmetrikusBilinearis (T : Type*) [Field T] {V : Type*} [AddCommGroup V] [Module T V]
    (l : V → V → T) : Prop :=
  BilinearisLekepezes T l ∧ ∀ u v, l u v = l v u

/-! ### Alapvető tulajdonságok -/

/-- Bilineáris leképezés első változójában a nullvektoron `0`-t vesz fel. -/
theorem bilin_zero_left {l : U → V → T} (hl : BilinearisLekepezes T l) (v : V) :
    l 0 v = 0 := by
  simpa using hl.2.2.1 0 0 v

/-- Bilineáris leképezés második változójában a nullvektoron `0`-t vesz fel. -/
theorem bilin_zero_right {l : U → V → T} (hl : BilinearisLekepezes T l) (u : U) :
    l u 0 = 0 := by
  simpa using hl.2.2.2 0 u 0

/-- Bilineáris leképezés az első változójában additív véges összegre is. -/
theorem bilin_sum_left {ι : Type*} {l : U → V → T} (hl : BilinearisLekepezes T l)
    (s : Finset ι) (g : ι → U) (v : V) : l (∑ i ∈ s, g i) v = ∑ i ∈ s, l (g i) v := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using bilin_zero_left hl v
  | insert a s ha ih => rw [Finset.sum_insert ha, hl.1, ih, Finset.sum_insert ha]

/-- Bilineáris leképezés a második változójában additív véges összegre is. -/
theorem bilin_sum_right {ι : Type*} {l : U → V → T} (hl : BilinearisLekepezes T l)
    (s : Finset ι) (u : U) (g : ι → V) : l u (∑ i ∈ s, g i) = ∑ i ∈ s, l u (g i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using bilin_zero_right hl u
  | insert a s ha ih => rw [Finset.sum_insert ha, hl.2.1, ih, Finset.sum_insert ha]

/-- Lineáris kombináció az első változóban. -/
theorem bilin_kombinacio_left {ι : Type*} [Fintype ι] {l : U → V → T}
    (hl : BilinearisLekepezes T l) (x : ι → T) (u : ι → U) (v : V) :
    l (∑ i, x i • u i) v = ∑ i, x i * l (u i) v := by
  rw [bilin_sum_left hl]
  exact Finset.sum_congr rfl fun i _ => hl.2.2.1 (x i) (u i) v

/-- Lineáris kombináció a második változóban. -/
theorem bilin_kombinacio_right {ι : Type*} [Fintype ι] {l : U → V → T}
    (hl : BilinearisLekepezes T l) (u : U) (y : ι → T) (v : ι → V) :
    l u (∑ j, y j • v j) = ∑ j, y j * l u (v j) := by
  rw [bilin_sum_right hl]
  exact Finset.sum_congr rfl fun j _ => hl.2.2.2 (y j) u (v j)

/-- Átlós („ortogonális”) vektorrendszeren a kvadratikus érték négyzetösszeg alakú:
ha `l(uᵢ,uⱼ) = 0` valahányszor `i ≠ j`, akkor `l(∑cᵢuᵢ, ∑cᵢuᵢ) = ∑ l(uᵢ,uᵢ)cᵢ²`. -/
theorem bilin_diagonalis_ertek {ι : Type*} [Fintype ι] {l : V → V → T}
    (hl : BilinearisLekepezes T l) (u : ι → V) (hd : ∀ i j, i ≠ j → l (u i) (u j) = 0)
    (c : ι → T) : l (∑ i, c i • u i) (∑ i, c i • u i) = ∑ i, l (u i) (u i) * c i ^ 2 := by
  classical
  rw [bilin_kombinacio_left hl]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [bilin_kombinacio_right hl, Finset.sum_eq_single i]
  · ring
  · intro j _ hj
    rw [hd i j (Ne.symm hj), mul_zero]
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-! ### A bilineáris leképezés mátrixa -/

/-- **15.1. Definíció.** Az `l` bilineáris leképezés *mátrixa* az `ℰ : e₁,…,e_m` és
`ℱ : f₁,…,f_n` bázisokban az `A = (l(eᵢ,fⱼ))_{m×n}` mátrix. -/
def bilinMatrixa (e : Fin m → U) (f : Fin n → V) (l : U → V → T) : Matrix' T m n :=
  fun i j => l (e i) (f j)

omit [Field T] [AddCommGroup U] [Module T U] [AddCommGroup V] [Module T V] in
theorem bilinMatrixa_apply (e : Fin m → U) (f : Fin n → V) (l : U → V → T) (i j) :
    bilinMatrixa e f l i j = l (e i) (f j) := rfl

/-- **15.1.** A bilineáris leképezés *koordinátás alakja*: ha `u = ∑ xᵢeᵢ` és
`v = ∑ yⱼfⱼ`, akkor `l(u,v) = ∑ᵢ∑ⱼ aᵢⱼxᵢyⱼ`, azaz `l(u,v) = xAyᵀ`. -/
theorem bilinearis_koordinatas_alak {l : U → V → T} (hl : BilinearisLekepezes T l)
    (e : Fin m → U) (f : Fin n → V) (x : Fin m → T) (y : Fin n → T) :
    l (∑ i, x i • e i) (∑ j, y j • f j)
      = ∑ i, ∑ j, x i * bilinMatrixa e f l i j * y j := by
  rw [bilin_kombinacio_left hl]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [bilin_kombinacio_right hl, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [bilinMatrixa_apply]; ring

/-- A koordinátás alak mátrixszorzatos írásmódban: `l(u,v) = (xA)·y`. -/
theorem bilinearis_vecMul_alak {l : U → V → T} (hl : BilinearisLekepezes T l)
    (e : Fin m → U) (f : Fin n → V) (x : Fin m → T) (y : Fin n → T) :
    l (∑ i, x i • e i) (∑ j, y j • f j)
      = ∑ j, Matrix.vecMul x (bilinMatrixa e f l) j * y j := by
  rw [bilinearis_koordinatas_alak hl, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Matrix.vecMul, dotProduct, Finset.sum_mul]

/-! ## 15.2. Tétel -/

/-- **15.2. Tétel.** Legyen `V` véges dimenziós, `l : V² → T` bilineáris. `l` pontosan
akkor szimmetrikus, ha mátrixa (valamely, s így minden) bázisban szimmetrikus.

*Bizonyítás.* Ha `l` szimmetrikus, akkor `l(eᵢ,eⱼ) = l(eⱼ,eᵢ)`, azaz `A` szimmetrikus.
Megfordítva, ha `A` szimmetrikus, akkor `l(u,v) = xAyᵀ = (xAyᵀ)ᵀ = yAᵀxᵀ = yAxᵀ = l(v,u)`. -/
theorem szimmetrikus_iff_matrix_szimmetrikus {l : V → V → T} (hl : BilinearisLekepezes T l)
    {e : Fin n → V} (he : Bazis T e) :
    (∀ u v, l u v = l v u) ↔ Szimmetrikus (bilinMatrixa e e l) := by
  constructor
  · intro h
    funext i j
    exact h (e j) (e i)
  · intro hA u v
    have hAij : ∀ i j, bilinMatrixa e e l j i = bilinMatrixa e e l i j := fun i j =>
      congrFun (congrFun hA i) j
    have hu := koordinatai_spec he u
    have hv := koordinatai_spec he v
    rw [show l u v = l (∑ i, koordinatai he u i • e i) (∑ j, koordinatai he v j • e j) by
        rw [← hu, ← hv],
      show l v u = l (∑ i, koordinatai he v i • e i) (∑ j, koordinatai he u j • e j) by
        rw [← hu, ← hv],
      bilinearis_koordinatas_alak hl, bilinearis_koordinatas_alak hl, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [hAij i j]
    ring

/-! ## 15.3. Definíció, 15.4. Tétel -/

/-- **15.3. Definíció.** A `q : V → T` leképezés *kvadratikus alak*, ha van olyan
`l : V² → T` szimmetrikus bilineáris leképezés, melyre `q(v) = l(v,v)` minden `v`-re. -/
def KvadratikusAlak (T : Type*) [Field T] {V : Type*} [AddCommGroup V] [Module T V]
    (q : V → T) : Prop :=
  ∃ l : V → V → T, SzimmetrikusBilinearis T l ∧ ∀ v, q v = l v v

/-- **15.4. (polarizációs formula).** Szimmetrikus bilineáris `l` esetén
`2l(u,v) = l(u+v,u+v) − l(u,u) − l(v,v)`. -/
theorem polarizacio {l : V → V → T} (hl : SzimmetrikusBilinearis T l) (u v : V) :
    2 * l u v = l (u + v) (u + v) - l u u - l v v := by
  have h1 : l (u + v) (u + v) = l u (u + v) + l v (u + v) := hl.1.1 u v (u + v)
  have h2 : l u (u + v) = l u u + l u v := hl.1.2.1 u u v
  have h3 : l v (u + v) = l v u + l v v := hl.1.2.1 v u v
  have h4 : l v u = l u v := hl.2 v u
  rw [h1, h2, h3, h4]
  ring

/-- **15.4. Tétel.** Bármely kvadratikus alak egyértelműen meghatározza a hozzá tartozó
szimmetrikus bilineáris leképezést.

*Bizonyítás.* `q(u+v) = q(u) + 2l(u,v) + q(v)`, amiből
`l(u,v) = ½(q(u+v) − q(u) − q(v))`. -/
theorem kvadratikus_alak_egyertelmu (h2 : (2 : T) ≠ 0) {q : V → T} {l₁ l₂ : V → V → T}
    (hl₁ : SzimmetrikusBilinearis T l₁) (hl₂ : SzimmetrikusBilinearis T l₂)
    (hq₁ : ∀ v, q v = l₁ v v) (hq₂ : ∀ v, q v = l₂ v v) : l₁ = l₂ := by
  funext u v
  have e₁ := polarizacio hl₁ u v
  have e₂ := polarizacio hl₂ u v
  have hqq : ∀ w : V, l₁ w w = l₂ w w := fun w => by rw [← hq₁, hq₂]
  rw [hqq (u + v), hqq u, hqq v] at e₁
  exact mul_left_cancel₀ h2 (e₁.trans e₂.symm)

/-! ## 15.5. Definíció -/

/-- **15.5. Definíció.** A `q` kvadratikus alak mátrixa valamely bázisban az őt
meghatározó szimmetrikus bilineáris leképezés mátrixa. Ekkor `q(v) = xAxᵀ`, ahol `x`
a `v` koordinátasora; ez `q` *koordinátás alakja*. -/
theorem kvadratikus_koordinatas_alak {l : V → V → T} (hl : BilinearisLekepezes T l)
    {q : V → T} (hq : ∀ v, q v = l v v) (e : Fin n → V) (x : Fin n → T) :
    q (∑ i, x i • e i) = ∑ i, ∑ j, x i * bilinMatrixa e e l i j * x j := by
  rw [hq, bilinearis_koordinatas_alak hl]

/-- **15.5.** Báziscsere: ha `S` az `ℱ` bázisról az `ℰ` bázisra való áttérés mátrixa,
és `A`, illetve `B` a bilineáris leképezés mátrixa `ℰ`-ben, illetve `ℱ`-ben, akkor
`B = SASᵀ`.

*Bizonyítás.* `bᵢⱼ = l(fᵢ,fⱼ) = l(∑ₖ sᵢₖeₖ, ∑ₚ sⱼₚeₚ) = ∑ₖ∑ₚ sᵢₖ aₖₚ sⱼₚ = (SASᵀ)ᵢⱼ`. -/
theorem bilinMatrixa_baziscsere {l : V → V → T} (hl : BilinearisLekepezes T l)
    {e f : Fin n → V} {S : Matrix' T n n} (hS : AtteresMatrixa f e S) :
    bilinMatrixa f f l = S * bilinMatrixa e e l * Sᵀ := by
  funext i j
  have hi : f i = ∑ k, S i k • e k := hS i
  have hj : f j = ∑ p, S j p • e p := hS j
  have hval : bilinMatrixa f f l i j
      = ∑ k, ∑ p, S i k * bilinMatrixa e e l k p * S j p := by
    rw [bilinMatrixa_apply, hi, hj, bilinearis_koordinatas_alak hl]
  rw [hval, Matrix.mul_apply, Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]

/-- Nemelfajuló mátrixnak van inverze (tetszőleges méret esetén). -/
theorem inverze_letezik {S : Matrix' T n n} (hS : det' S ≠ 0) : ∃ X, Inverze S X := by
  have hdet : S.det ≠ 0 := by rwa [det'_eq_det] at hS
  exact ⟨S⁻¹, Matrix.nonsing_inv_mul S (Ne.isUnit hdet), Matrix.mul_nonsing_inv S (Ne.isUnit hdet)⟩

/-- **15.5.** Kvadratikus (bilineáris) alak különböző bázisbeli mátrixainak rangja
megegyezik (9.6. Tétel). -/
theorem bilinMatrixa_rang_egyenlo {l : V → V → T} (hl : BilinearisLekepezes T l)
    {e f : Fin n → V} (he : Bazis T e) (hf : Bazis T f) {S : Matrix' T n n}
    (hS : AtteresMatrixa f e S) : rang (bilinMatrixa f f l) = rang (bilinMatrixa e e l) := by
  obtain ⟨S', hS'⟩ := letezik_egyertelmu_atteres (T := T) (e := e) hf
  have hinv : Inverze S S' := atteres_inverze hf he hS hS'.1
  have hinvT : Inverze Sᵀ S'ᵀ := inverz_transzponalt hinv
  rw [bilinMatrixa_baziscsere hl hS, rang_mul_of_inverze_right hinvT,
    rang_mul_of_inverze_left hinv]

/-! ## 15.6. Definíció -/

/-- **15.6. Definíció.** A `q` kvadratikus alak *rangja* valamely bázisbeli mátrixának
rangja (a 15.5. szerint ez független a bázis választásától). -/
def KvadratikusRangja (l : V → V → T) (e : Fin n → V) (r : ℕ) : Prop :=
  rang (bilinMatrixa e e l) = r

/-- **15.6. Definíció.** A `q` kvadratikus alak *kanonikus alakú* az `ℰ` bázisban, ha
mátrixa diagonális, azaz koordinátás alakja `∑ᵢ aᵢxᵢ²`. -/
def KanonikusAlaku (l : V → V → T) (e : Fin n → V) : Prop :=
  Diagonalis (bilinMatrixa e e l)

/-- Kanonikus alak esetén a koordinátás alak valóban `∑ᵢ aᵢxᵢ²`. -/
theorem kanonikus_koordinatas_alak {l : V → V → T} (hl : BilinearisLekepezes T l)
    {e : Fin n → V} (hk : KanonikusAlaku l e) (x : Fin n → T) :
    l (∑ i, x i • e i) (∑ j, x j • e j)
      = ∑ i, bilinMatrixa e e l i i * x i * x i := by
  rw [bilinearis_koordinatas_alak hl]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · ring
  · intro j _ hj
    rw [hk i j (Ne.symm hj)]
    ring
  · intro hi
    exact absurd (Finset.mem_univ i) hi

/-! ## 15.7. Kvadratikus alakok alaptétele, 15.8. Következmény -/

/-- **15.8. Következmény.** Bármely `A` szimmetrikus mátrixhoz megadható olyan `S`
nemelfajuló mátrix, melyre `SASᵀ` diagonális.

A formalizált bizonyítás a szimmetrikus bilineáris leképezéshez tartozó *ortogonális
bázis* létezését használja, ami a könyvbeli indukciós („teljes négyzetté alakítós”)
gondolatmenettel egyenértékű. -/
theorem letezik_diagonalizalo_kongruencia (h2 : (2 : T) ≠ 0) {A : Matrix' T n n}
    (hA : Szimmetrikus A) : ∃ S : Matrix' T n n, det' S ≠ 0 ∧ Diagonalis (S * A * Sᵀ) := by
  classical
  haveI : Invertible (2 : T) := invertibleOfNonzero h2
  have hsymm : LinearMap.IsSymm (Matrix.toBilin' A) := by
    rw [← LinearMap.BilinForm.isSymm_iff, LinearMap.BilinForm.isSymm_def]
    intro x y
    rw [Matrix.toBilin'_apply, Matrix.toBilin'_apply, Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [show A j i = A i j from congrFun (congrFun hA i) j]
    ring
  obtain ⟨v, hv⟩ := LinearMap.BilinForm.exists_orthogonal_basis hsymm
  set w : Module.Basis (Fin n) T (Fin n → T) :=
    v.reindex (finCongr (Module.finrank_fin_fun T)) with hw
  have hworth : ∀ i j : Fin n, i ≠ j → Matrix.toBilin' A (w i) (w j) = 0 := by
    intro i j hij
    simp only [hw, Module.Basis.coe_reindex, Function.comp_apply]
    exact hv (fun hc => hij (by simpa using congrArg (finCongr (Module.finrank_fin_fun T)) hc))
  refine ⟨Matrix.of fun i j => w i j, ?_, ?_⟩
  · rw [det'_eq_det]
    intro hdet
    obtain ⟨x, hx0, hx⟩ := Matrix.exists_vecMul_eq_zero_iff.2 hdet
    have hsum : ∑ i, x i • w i = 0 := by
      funext j
      simpa [Matrix.vecMul, dotProduct] using congrFun hx j
    exact hx0 (funext ((Fintype.linearIndependent_iff.1 w.linearIndependent) x hsum))
  · intro i j hij
    have key : (Matrix.of (fun i j => w i j) * A * (Matrix.of (fun i j => w i j))ᵀ) i j
        = Matrix.toBilin' A (w i) (w j) := by
      rw [Matrix.toBilin'_apply]
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, Finset.sum_mul]
      rw [Finset.sum_comm]
    rw [key]
    exact hworth i j hij

/-- Ha `S` nemelfajuló és `ℰ` bázis, akkor az `fᵢ = ∑ⱼ sᵢⱼeⱼ` vektorrendszer is bázis
(a nemelfajuló lineáris helyettesítés új bázist ad). -/
theorem bazis_kombinacio {e : Fin n → V} (he : Bazis T e) {S : Matrix' T n n}
    (hS : det' S ≠ 0) : Bazis T (fun i => ∑ j, S i j • e j) := by
  obtain ⟨S', hS'⟩ := inverze_letezik hS
  have hef : ∀ i, e i = ∑ j, S' i j • (∑ k, S j k • e k) := by
    intro i
    have h := kombinacio_szorzat S' S e i
    rw [hS'.1, kombinacio_one e i] at h
    exact h.symm
  constructor
  · -- lineáris függetlenség
    intro g hg i
    have hg' : ∑ j, Matrix.vecMul g S j • e j = 0 := by
      calc ∑ j, Matrix.vecMul g S j • e j
          = ∑ j, ∑ i, (g i * S i j) • e j := by
            refine Finset.sum_congr rfl fun j _ => ?_
            simp only [Matrix.vecMul, dotProduct]
            rw [Finset.sum_smul]
        _ = ∑ i, ∑ j, (g i * S i j) • e j := Finset.sum_comm
        _ = ∑ i, g i • ∑ j, S i j • e j := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.smul_sum]
            exact Finset.sum_congr rfl fun j _ => (smul_smul _ _ _).symm
        _ = 0 := hg
    have hzero : Matrix.vecMul g S = 0 := funext fun j => he.1 _ hg' j
    by_contra hgi
    have hdet : S.det ≠ 0 := by rwa [det'_eq_det] at hS
    exact hdet (Matrix.exists_vecMul_eq_zero_iff.1 ⟨g, fun hc => hgi (congrFun hc i), hzero⟩)
  · -- generátorrendszer
    have hsub : Set.range e ⊆ Generalt T (Set.range fun i => ∑ j, S i j • e j) := by
      rintro _ ⟨i, rfl⟩
      rw [hef i]
      exact alter_sum_mem (generalt_alter _) n (S' i) (fun j => ∑ k, S j k • e k)
        fun j => subset_generalt _ ⟨j, rfl⟩
    have huniv : (Set.univ : Set V) ⊆ Generalt T (Set.range fun i => ∑ j, S i j • e j) := by
      rw [← he.2]
      exact generalt_minimal (generalt_alter _) hsub
    exact Set.eq_univ_of_univ_subset huniv

/-- Bázisvektorok nemnulla skalárszorosai is bázist alkotnak. -/
theorem bazis_scale {e : Fin n → V} (he : Bazis T e) {c : Fin n → T} (hc : ∀ i, c i ≠ 0) :
    Bazis T (fun i => c i • e i) := by
  classical
  have hdet : det' (Matrix.diagonal c) ≠ 0 := by
    rw [det'_eq_det, Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.2 fun i _ => hc i
  have h := bazis_kombinacio he hdet
  have heq : (fun i => ∑ j, (Matrix.diagonal c) i j • e j) = fun i => c i • e i := by
    funext i
    rw [Finset.sum_eq_single i]
    · rw [Matrix.diagonal_apply_eq]
    · intro j _ hj
      rw [Matrix.diagonal_apply_ne _ (Ne.symm hj), zero_smul]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  rwa [heq] at h

/-- **15.7. Kvadratikus alakok alaptétele.** Bármely véges dimenziós vektortéren
értelmezett kvadratikus alakhoz megadható a vektortér olyan bázisa, melyben a
kvadratikus alak kanonikus alakú.

*Bizonyítás.* A `q`-hoz tartozó `l` szimmetrikus bilineáris leképezés `ℰ` bázisbeli `A`
mátrixa szimmetrikus (15.2.), így a 15.8. szerint van olyan nemelfajuló `S`, melyre
`SASᵀ` diagonális. Az `fᵢ = ∑ⱼ sᵢⱼeⱼ` vektorrendszer bázis, és `q` mátrixa ebben a
bázisban éppen `SASᵀ`. -/
theorem kvadratikus_alaptetel (h2 : (2 : T) ≠ 0) {l : V → V → T}
    (hl : SzimmetrikusBilinearis T l) {e : Fin n → V} (he : Bazis T e) :
    ∃ f : Fin n → V, Bazis T f ∧ KanonikusAlaku l f := by
  have hAsymm : Szimmetrikus (bilinMatrixa e e l) :=
    (szimmetrikus_iff_matrix_szimmetrikus hl.1 he).1 hl.2
  obtain ⟨S, hSdet, hSdiag⟩ := letezik_diagonalizalo_kongruencia h2 hAsymm
  refine ⟨fun i => ∑ j, S i j • e j, bazis_kombinacio he hSdet, ?_⟩
  have hatt : AtteresMatrixa (fun i => ∑ j, S i j • e j) e S := fun _ => rfl
  rw [KanonikusAlaku, bilinMatrixa_baziscsere hl.1 hatt]
  exact hSdiag

/-- **15.7.** Koordinátás megfogalmazás: bármely `q` kvadratikus alak alkalmas bázisban
`q(∑ xᵢfᵢ) = ∑ aᵢxᵢ²` alakú. -/
theorem kvadratikus_alaptetel_koordinatas (h2 : (2 : T) ≠ 0) {q : V → T}
    (hq : KvadratikusAlak T q) {e : Fin n → V} (he : Bazis T e) :
    ∃ (f : Fin n → V) (a : Fin n → T), Bazis T f ∧
      ∀ x : Fin n → T, q (∑ i, x i • f i) = ∑ i, a i * x i * x i := by
  obtain ⟨l, hl, hql⟩ := hq
  obtain ⟨f, hf, hkan⟩ := kvadratikus_alaptetel h2 hl he
  refine ⟨f, fun i => bilinMatrixa f f l i i, hf, fun x => ?_⟩
  rw [hql]
  exact kanonikus_koordinatas_alak hl.1 hkan x

end Ch15
end SzaboLinAlg
