import Mathlib
import LinearisAlgebra.Ch01_Bevezetes
import LinearisAlgebra.Ch02_Matrixok
import LinearisAlgebra.Ch03_Determinans
import LinearisAlgebra.Ch04_Inverzmatrix
import LinearisAlgebra.Ch05_Egyenletrendszerek
import LinearisAlgebra.Ch06_Vektorterek
import LinearisAlgebra.Ch07_LinearisFuggetlenseg
import LinearisAlgebra.Ch08_VegesDimenzios
import LinearisAlgebra.Ch09_MatrixRang

/-!
# Lineáris algebra I. (MBLK15E) — a tematika követelményeinek formalizálása

Ez a modul a *Lineáris algebra I.* tantárgy tematikájának pontjait követi, és minden
ponthoz formális állítást rendel. Ahol az anyagot a Szabó László-féle *Bevezetés a
lineáris algebrába* jegyzet formalizálása már tartalmazza, ott az itteni tétel az ottani
eredményre épül; ahol a tematika a jegyzeten túlmutat (komplex számok trigonometrikus
alakja, `ℝⁿ` geometriája: belső szorzat, hossz, merőlegesség, egyenesek és síkok), ott új
definíciók és tételek készültek.

A tematika pontjai:

1. Komplex számok: kanonikus és trigonometrikus alak, Moivre-képlet, egységgyökök,
   primitív egységgyökök.
2. Az `ℝⁿ` vektorai, lineáris kombináció.
3. Belső szorzat, hossz, Cauchy–Schwarz- és háromszög-egyenlőtlenség, merőlegesség,
   merőleges vetítés.
4. Egyenesek, síkok, hipersíkok.
5. Lineáris egyenletrendszerek, elemi átalakítások.
6. Mátrixműveletek, inverzmátrix.
7. Determinánsok, kifejtési tétel, szorzástétel, Cramer-szabály.
8. Homogén egyenletrendszerek, a megoldáshalmaz szerkezete.
9. Vektorterek, alterek, generálás.
10. Lineáris függetlenség, bázis, dimenzió.
11. Mátrixok rangja, rangszámtétel, Kronecker–Capelli-tétel.
-/

namespace Tematika.LinearisAlgebraI

open scoped BigOperators
open Matrix SzaboLinAlg SzaboLinAlg.Ch02 SzaboLinAlg.Ch03 SzaboLinAlg.Ch04 SzaboLinAlg.Ch05

/-! ## 1. Komplex számok -/

/-- **1.** *Kanonikus alak.* Minden komplex szám egyértelműen írható `a + bi` alakban,
ahol `a, b` valós. -/
theorem kanonikus_alak (z : ℂ) : z = (z.re : ℂ) + (z.im : ℂ) * Complex.I ∧
    ∀ a b : ℝ, z = (a : ℂ) + (b : ℂ) * Complex.I → a = z.re ∧ b = z.im := by
  refine ⟨(Complex.re_add_im z).symm, fun a b hab => ?_⟩
  subst hab
  simp

/-- **1.** *Trigonometrikus alak.* Minden `z ≠ 0` komplex szám felírható
`z = r(cos φ + i sin φ)` alakban, ahol `r = |z| > 0`. -/
theorem trigonometrikus_alak {z : ℂ} (hz : z ≠ 0) :
    ∃ r : ℝ, ∃ phi : ℝ, 0 < r ∧
      z = (r : ℂ) * ((Real.cos phi : ℂ) + (Real.sin phi : ℂ) * Complex.I) := by
  refine ⟨‖z‖, Complex.arg z, norm_pos_iff.2 hz, ?_⟩
  rw [Complex.ofReal_cos, Complex.ofReal_sin, ← Complex.exp_mul_I,
    Complex.norm_mul_exp_arg_mul_I]

/-- **1.** *Moivre-képlet.* `(r(cos φ + i sin φ))ⁿ = rⁿ(cos nφ + i sin nφ)`. -/
theorem moivre (r phi : ℝ) (n : ℕ) :
    ((r : ℂ) * ((Real.cos phi : ℂ) + (Real.sin phi : ℂ) * Complex.I)) ^ n
      = (r ^ n : ℝ) * ((Real.cos (n * phi) : ℂ) + (Real.sin (n * phi) : ℂ) * Complex.I) := by
  rw [Complex.ofReal_cos, Complex.ofReal_sin, ← Complex.exp_mul_I, Complex.ofReal_cos,
    Complex.ofReal_sin, ← Complex.exp_mul_I, mul_pow, ← Complex.exp_nat_mul]
  push_cast
  ring_nf

/-- **1.** *`n`-edik egységgyökök.* Az `zⁿ = 1` egyenlet megoldásai pontosan a
`cos(2kπ/n) + i sin(2kπ/n)` `(k = 0,…,n-1)` számok. -/
theorem egyseggyokok {n : ℕ} (hn : 0 < n) (z : ℂ) :
    z ^ n = 1 ↔ ∃ k : ℕ, k < n ∧
      z = (Real.cos (2 * Real.pi * k / n) : ℂ)
        + (Real.sin (2 * Real.pi * k / n) : ℂ) * Complex.I := by
  have hp := Complex.isPrimitiveRoot_exp n hn.ne'
  constructor
  · intro hz
    haveI : NeZero n := ⟨hn.ne'⟩
    obtain ⟨k, hk, hzk⟩ := hp.eq_pow_of_pow_eq_one hz
    refine ⟨k, hk, ?_⟩
    rw [← hzk, ← Complex.exp_nat_mul, Complex.ofReal_cos, Complex.ofReal_sin,
      ← Complex.exp_mul_I]
    congr 1
    push_cast
    field_simp
  · rintro ⟨k, hk, rfl⟩
    rw [Complex.ofReal_cos, Complex.ofReal_sin, ← Complex.exp_mul_I, ← Complex.exp_nat_mul]
    have hnk : (n : ℂ) * ((2 * Real.pi * k / n : ℝ) * Complex.I)
        = (k : ℤ) * (2 * Real.pi * Complex.I) := by
      have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
      push_cast
      field_simp
    rw [hnk, Complex.exp_int_mul_two_pi_mul_I]

/-- **1.** Az `n`-edik egységgyökök száma pontosan `n`. -/
theorem egyseggyokok_szama {n : ℕ} (hn : 0 < n) :
    {z : ℂ | z ^ n = 1}.ncard = n := by
  have h : {z : ℂ | z ^ n = 1} = ↑(Polynomial.nthRootsFinset n (1 : ℂ)) := by
    ext z
    simp [Polynomial.mem_nthRootsFinset hn]
  rw [h, Set.ncard_coe_finset]
  exact (Complex.isPrimitiveRoot_exp n hn.ne').card_nthRootsFinset

/-- **1.** *Primitív egységgyök:* olyan `n`-edik egységgyök, amely semmilyen `n`-nél
kisebb pozitív kitevőre nem ad `1`-et. -/
def PrimitivEgyseggyok (n : ℕ) (z : ℂ) : Prop :=
  z ^ n = 1 ∧ ∀ m : ℕ, 0 < m → m < n → z ^ m ≠ 1

/-- **1.** A primitív egységgyök fogalma megegyezik a Mathlib `IsPrimitiveRoot`
fogalmával. -/
theorem primitivEgyseggyok_iff {n : ℕ} (hn : 0 < n) (z : ℂ) :
    PrimitivEgyseggyok n z ↔ IsPrimitiveRoot z n :=
  (IsPrimitiveRoot.iff hn).symm

/-- **1.** Ha `k` és `n` relatív prímek, akkor a `cos(2kπ/n) + i sin(2kπ/n)` egységgyök
primitív `n`-edik egységgyök. -/
theorem primitivEgyseggyok_exp {k n : ℕ} (hn : 0 < n) (hkn : Nat.Coprime k n) :
    PrimitivEgyseggyok n (Complex.exp (2 * Real.pi * Complex.I * (k / n))) :=
  (primitivEgyseggyok_iff hn _).2 (Complex.isPrimitiveRoot_exp_of_coprime k n hn.ne' hkn)

/-- **1.** A primitív `n`-edik egységgyökök száma `φ(n)` (Euler-féle `φ`-függvény). -/
theorem primitivEgyseggyokok_szama {n : ℕ} (hn : 0 < n) :
    {z : ℂ | PrimitivEgyseggyok n z}.ncard = Nat.totient n := by
  have h : {z : ℂ | PrimitivEgyseggyok n z} = ↑(primitiveRoots n ℂ) := by
    ext z
    simp [mem_primitiveRoots hn, primitivEgyseggyok_iff hn]
  rw [h, Set.ncard_coe_finset, Complex.card_primitiveRoots]

/-! ## 2. Az `ℝⁿ` vektorai, lineáris kombináció -/

/-- **2.** Az `x` vektor a `v₁,…,v_k` vektorok *lineáris kombinációja*, ha alkalmas
`c₁,…,c_k` skalárokkal `x = c₁v₁ + … + c_kv_k`. -/
def LinKombinacioja {n k : ℕ} (v : Fin k → (Fin n → ℝ)) (x : Fin n → ℝ) : Prop :=
  ∃ c : Fin k → ℝ, x = ∑ i, c i • v i

/-- **2.** Minden vektor előáll a standard egységvektorok lineáris kombinációjaként. -/
theorem standard_bazis_linkombinacio {n : ℕ} (x : Fin n → ℝ) :
    LinKombinacioja (fun i : Fin n => (Pi.single i (1 : ℝ))) x := by
  refine ⟨x, ?_⟩
  funext j
  simp [Finset.sum_apply, Pi.single_apply]

/-! ## 3. Belső szorzat, hossz, merőlegesség -/

/-- **3.** Az `ℝⁿ`-beli *belső (skaláris) szorzat*: `⟨x,y⟩ = x₁y₁ + … + xₙyₙ`. -/
def belsoSzorzat {n : ℕ} (x y : Fin n → ℝ) : ℝ := ∑ i, x i * y i

/-- **3.** Az `x` vektor *hossza*: `‖x‖ = √⟨x,x⟩`. -/
noncomputable def hossz {n : ℕ} (x : Fin n → ℝ) : ℝ := Real.sqrt (belsoSzorzat x x)

/-- **3.** A belső szorzat szimmetrikus. -/
theorem belsoSzorzat_szimmetrikus {n : ℕ} (x y : Fin n → ℝ) :
    belsoSzorzat x y = belsoSzorzat y x := by
  simp [belsoSzorzat, mul_comm]

/-- **3.** A belső szorzat az első változójában lineáris. -/
theorem belsoSzorzat_linearis {n : ℕ} (x y z : Fin n → ℝ) (lam : ℝ) :
    belsoSzorzat (x + y) z = belsoSzorzat x z + belsoSzorzat y z ∧
      belsoSzorzat (lam • x) z = lam * belsoSzorzat x z := by
  constructor
  · simp only [belsoSzorzat, Pi.add_apply, add_mul]
    exact Finset.sum_add_distrib
  · simp only [belsoSzorzat, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring

/-- **3.** A belső szorzat pozitív definit. -/
theorem belsoSzorzat_pozitiv_definit {n : ℕ} (x : Fin n → ℝ) :
    0 ≤ belsoSzorzat x x ∧ (belsoSzorzat x x = 0 ↔ x = 0) := by
  refine ⟨Finset.sum_nonneg fun i _ => mul_self_nonneg _, ?_, ?_⟩
  · intro h
    funext i
    have hi := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => mul_self_nonneg (x i))).1 h i (Finset.mem_univ i)
    simpa using mul_self_eq_zero.1 hi
  · rintro rfl
    simp [belsoSzorzat]

/-- **3.** *Cauchy–Schwarz-egyenlőtlenség:* `|⟨x,y⟩| ≤ ‖x‖·‖y‖`. -/
theorem cauchy_schwarz {n : ℕ} (x y : Fin n → ℝ) :
    |belsoSzorzat x y| ≤ hossz x * hossz y := by
  have h : (belsoSzorzat x y) ^ 2 ≤ belsoSzorzat x x * belsoSzorzat y y := by
    have := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ x y
    simpa [belsoSzorzat, sq] using this
  have hx : 0 ≤ belsoSzorzat x x := (belsoSzorzat_pozitiv_definit x).1
  calc |belsoSzorzat x y| = Real.sqrt ((belsoSzorzat x y) ^ 2) :=
        (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (belsoSzorzat x x * belsoSzorzat y y) := Real.sqrt_le_sqrt h
    _ = hossz x * hossz y := Real.sqrt_mul hx _

/-- **3.** *Háromszög-egyenlőtlenség:* `‖x + y‖ ≤ ‖x‖ + ‖y‖`. -/
theorem haromszog_egyenlotlenseg {n : ℕ} (x y : Fin n → ℝ) :
    hossz (x + y) ≤ hossz x + hossz y := by
  have hexp : belsoSzorzat (x + y) (x + y)
      = belsoSzorzat x x + 2 * belsoSzorzat x y + belsoSzorzat y y := by
    have hi : ∀ i : Fin n, (x + y) i * (x + y) i
        = x i * x i + 2 * (x i * y i) + y i * y i := fun i => by
      simp only [Pi.add_apply]; ring
    simp only [belsoSzorzat, hi]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hx : 0 ≤ belsoSzorzat x x := (belsoSzorzat_pozitiv_definit x).1
  have hy : 0 ≤ belsoSzorzat y y := (belsoSzorzat_pozitiv_definit y).1
  have hxx : hossz x ^ 2 = belsoSzorzat x x := Real.sq_sqrt hx
  have hyy : hossz y ^ 2 = belsoSzorzat y y := Real.sq_sqrt hy
  have hcs := cauchy_schwarz x y
  have habs := le_abs_self (belsoSzorzat x y)
  have hnn : 0 ≤ hossz x + hossz y := by
    have := Real.sqrt_nonneg (belsoSzorzat x x)
    have := Real.sqrt_nonneg (belsoSzorzat y y)
    simp only [hossz]
    linarith
  have key : belsoSzorzat (x + y) (x + y) ≤ (hossz x + hossz y) ^ 2 := by
    rw [hexp]
    nlinarith
  calc hossz (x + y) = Real.sqrt (belsoSzorzat (x + y) (x + y)) := rfl
    _ ≤ Real.sqrt ((hossz x + hossz y) ^ 2) := Real.sqrt_le_sqrt key
    _ = hossz x + hossz y := Real.sqrt_sq hnn

/-- **3.** Két vektor *merőleges*, ha belső szorzatuk nulla. -/
def Meroleges {n : ℕ} (x y : Fin n → ℝ) : Prop := belsoSzorzat x y = 0

/-- **3.** *Pitagorasz-tétel:* merőleges vektorokra `‖x + y‖² = ‖x‖² + ‖y‖²`. -/
theorem pitagorasz {n : ℕ} {x y : Fin n → ℝ} (h : Meroleges x y) :
    hossz (x + y) ^ 2 = hossz x ^ 2 + hossz y ^ 2 := by
  have hexp : belsoSzorzat (x + y) (x + y)
      = belsoSzorzat x x + 2 * belsoSzorzat x y + belsoSzorzat y y := by
    have hi : ∀ i : Fin n, (x + y) i * (x + y) i
        = x i * x i + 2 * (x i * y i) + y i * y i := fun i => by
      simp only [Pi.add_apply]; ring
    simp only [belsoSzorzat, hi]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  have hx : 0 ≤ belsoSzorzat x x := (belsoSzorzat_pozitiv_definit x).1
  have hy : 0 ≤ belsoSzorzat y y := (belsoSzorzat_pozitiv_definit y).1
  have hxy : 0 ≤ belsoSzorzat (x + y) (x + y) := (belsoSzorzat_pozitiv_definit _).1
  rw [hossz, hossz, hossz, Real.sq_sqrt hx, Real.sq_sqrt hy, Real.sq_sqrt hxy, hexp,
    show belsoSzorzat x y = 0 from h]
  ring

/-- **3.** Az `x` vektor *merőleges vetülete* az `a ≠ 0` vektor egyenesére:
`(⟨x,a⟩/⟨a,a⟩)·a`. -/
noncomputable def merolegesVetulet {n : ℕ} (a x : Fin n → ℝ) : Fin n → ℝ :=
  (belsoSzorzat x a / belsoSzorzat a a) • a

/-- **3.** A merőleges vetület jellemzése: `x - proj_a x` merőleges `a`-ra. -/
theorem merolegesVetulet_meroleges {n : ℕ} {a : Fin n → ℝ} (ha : a ≠ 0) (x : Fin n → ℝ) :
    Meroleges (x - merolegesVetulet a x) a := by
  have haa : belsoSzorzat a a ≠ 0 := fun h => ha ((belsoSzorzat_pozitiv_definit a).2.1 h)
  have h2 : ∑ i, (merolegesVetulet a x) i * a i
      = belsoSzorzat x a / belsoSzorzat a a * belsoSzorzat a a := by
    simp only [merolegesVetulet, Pi.smul_apply, smul_eq_mul, belsoSzorzat, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  have h3 : belsoSzorzat (x - merolegesVetulet a x) a
      = belsoSzorzat x a - ∑ i, (merolegesVetulet a x) i * a i := by
    simp only [belsoSzorzat, Pi.sub_apply, sub_mul]
    exact Finset.sum_sub_distrib _ _
  rw [Meroleges, h3, h2, div_mul_cancel₀ _ haa, sub_self]

/-! ## 4. Egyenesek, síkok, hipersíkok -/

/-- **4.** A `p` ponton átmenő, `v ≠ 0` irányvektorú *egyenes* `ℝⁿ`-ben. -/
def Egyenes {n : ℕ} (p v : Fin n → ℝ) : Set (Fin n → ℝ) := {x | ∃ t : ℝ, x = p + t • v}

/-- **4.** A `p` ponton átmenő, `u`, `v` irányvektorok kifeszítette *sík*. -/
def Sik {n : ℕ} (p u v : Fin n → ℝ) : Set (Fin n → ℝ) :=
  {x | ∃ s t : ℝ, x = p + s • u + t • v}

/-- **4.** Az `a ≠ 0` normálvektorú, `c` konstansú *hipersík*: `{x : ⟨a,x⟩ = c}`. -/
def Hipersik {n : ℕ} (a : Fin n → ℝ) (c : ℝ) : Set (Fin n → ℝ) :=
  {x | belsoSzorzat a x = c}

/-- **4.** Egy hipersík pontosan az `⟨a,x⟩ = c` egyenletű lineáris egyenlet
megoldáshalmaza; a `p` ponton átmenő, `a` normálvektorú hipersík
`{x : ⟨a, x - p⟩ = 0}`. -/
theorem hipersik_pont_normalvektor {n : ℕ} (a p : Fin n → ℝ) :
    Hipersik a (belsoSzorzat a p) = {x | Meroleges a (x - p)} := by
  ext x
  have hsub : belsoSzorzat a (x - p) = belsoSzorzat a x - belsoSzorzat a p := by
    simp only [belsoSzorzat, Pi.sub_apply, mul_sub]
    exact Finset.sum_sub_distrib _ _
  simp only [Hipersik, Meroleges, Set.mem_setOf_eq, hsub, sub_eq_zero]

/-- **4.** Az egyenes minden pontja kielégíti a rá illeszkedő hipersík egyenletét, ha az
irányvektor merőleges a normálvektorra. -/
theorem egyenes_hipersikban {n : ℕ} {a p v : Fin n → ℝ} (hv : Meroleges a v) :
    Egyenes p v ⊆ Hipersik a (belsoSzorzat a p) := by
  rintro x ⟨t, rfl⟩
  have hadd : belsoSzorzat a (p + t • v) = belsoSzorzat a p + t * belsoSzorzat a v := by
    simp only [belsoSzorzat, Pi.add_apply, Pi.smul_apply, smul_eq_mul, mul_add,
      Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  have hv0 : belsoSzorzat a v = 0 := hv
  simp [Hipersik, hadd, hv0]

/-! ## 5–8. A jegyzet fejezeteire épülő pontok -/

/-- **5.** Az elemi átalakítások ekvivalens egyenletrendszert adnak (5.2. Definíció). -/
theorem elemi_atalakitas_ekvivalens {T : Type*} [Field T] {m n : ℕ} (A : Matrix' T m n)
    (b : Fin m → T) {i₀ j₀ : Fin m} (hij : i₀ ≠ j₀) (lam : T) :
    Ekvivalens A b (A.updateRow i₀ (A i₀ + lam • A j₀))
      (Function.update b i₀ (b i₀ + lam * b j₀)) :=
  ekvivalens_sor_hozzaadas A b hij lam

/-- **6.** A mátrixszorzás asszociatív (2.5. Tétel). -/
theorem matrixszorzas_asszociativ {T : Type*} [CommRing T] {m n s t : ℕ}
    (A : Matrix' T m n) (B : Matrix' T n s) (C : Matrix' T s t) :
    A * (B * C) = (A * B) * C :=
  szorzas_asszociativ A B C

/-- **6.** Egy négyzetes mátrixnak akkor és csak akkor van inverze, ha determinánsa nem
nulla (4.2. Tétel). -/
theorem inverz_letezese {T : Type*} [Field T] {n : ℕ} (A : Matrix' T (n + 1) (n + 1)) :
    (∃ X, Inverze A X) ↔ det' A ≠ 0 :=
  inverze_letezik_iff A

/-- **7.** Kifejtési tétel: a determináns bármely sora szerint kifejthető (3.4. Tétel). -/
theorem kifejtesi_tetel {T : Type*} [CommRing T] {n : ℕ}
    (A : Matrix (Fin (n + 1)) (Fin (n + 1)) T) (i : Fin (n + 1)) :
    det' A = ∑ k, A i k * adjungaltAldeterminans A i k :=
  det_kifejtes_sor A i

/-- **7.** *Szorzástétel:* `|AB| = |A|·|B|`. -/
theorem determinans_szorzastetel {T : Type*} [CommRing T] {n : ℕ}
    (A B : Matrix' T n n) : det' (A * B) = det' A * det' B := by
  rw [det'_eq_det, det'_eq_det, det'_eq_det, Matrix.det_mul]

/-- **7.** *Cramer-szabály* (5.8.). -/
theorem cramer {T : Type*} [Field T] {n : ℕ} (A : Matrix' T (n + 1) (n + 1))
    (b : Fin (n + 1) → T) (h : det' A ≠ 0) :
    Megoldasa A b (fun k => cramerDet A b k / det' A) :=
  cramer_megoldas A b h

/-- **8.** Ha egy négyzetes mátrixú homogén egyenletrendszernek van triviálistól különböző
megoldása, akkor a mátrix determinánsa nulla (5.9.). -/
theorem homogen_nemtrivialis {T : Type*} [Field T] {n : ℕ}
    (A : Matrix' T (n + 1) (n + 1)) {c : Fin (n + 1) → T} (hc : Megoldasa A 0 c)
    (hc0 : c ≠ 0) : det' A = 0 :=
  det_nulla_nemtrivialis_megoldas A hc hc0

/-- **8.** A megoldáshalmaz szerkezete: partikuláris megoldás + a homogén rendszer
megoldásai (5.11.3). -/
theorem megoldashalmaz {T : Type*} [Field T] {m n : ℕ} {A : Matrix' T m n} {b : Fin m → T}
    {c₀ : Fin n → T} (hc₀ : Megoldasa A b c₀) :
    (∀ d, Megoldasa A 0 d → Megoldasa A b (c₀ + d)) ∧
      (∀ c, Megoldasa A b c → ∃ d, Megoldasa A 0 d ∧ c = c₀ + d) :=
  megoldashalmaz_szerkezete hc₀

/-! ## 9–11. Vektorterek, bázis, rang -/

/-- **9.** Az altérkritérium: nemüres, összeadásra és skalárral való szorzásra zárt
részhalmaz altér (6.7.2). -/
theorem alterkriterium {T : Type*} [Field T] {V : Type*} [AddCommGroup V] [Module T V]
    (U : Set V) : SzaboLinAlg.Ch06.Alter T U ↔ ∃ W : Submodule T V, (W : Set V) = U :=
  SzaboLinAlg.Ch06.alter_iff_submodule U

/-- **9.** A generált altér a legszűkebb, az adott halmazt tartalmazó altér (6.10). -/
theorem generalt_legszukebb {T : Type*} [Field T] {V : Type*} [AddCommGroup V]
    [Module T V] {X U : Set V} (hU : SzaboLinAlg.Ch06.Alter T U) (hXU : X ⊆ U) :
    SzaboLinAlg.Ch06.Generalt T X ⊆ U :=
  SzaboLinAlg.Ch06.generalt_minimal hU hXU

/-- **10.** Lineárisan független vektorrendszer nem lehet hosszabb egy generátorrendszernél
(7.5. Következmény). -/
theorem fuggetlen_legfeljebb_generator {T : Type*} [Field T] {V : Type*} [AddCommGroup V]
    [Module T V] {k l : ℕ} {u : Fin k → V} {v : Fin l → V}
    (hu : SzaboLinAlg.Ch07.LinFuggetlen T u)
    (hspan : ∀ a, u a ∈ SzaboLinAlg.Ch06.Generalt T (Set.range v)) : k ≤ l :=
  SzaboLinAlg.Ch07.linFuggetlen_card_le hu hspan

/-- **10.** Bármely két bázis ugyanannyi elemű, azaz a dimenzió jól definiált (8.3). -/
theorem dimenzio_joldefinialt {T : Type*} [Field T] {V : Type*} [AddCommGroup V]
    [Module T V] {k l : ℕ} {u : Fin k → V} {v : Fin l → V} (hu : SzaboLinAlg.Ch08.Bazis T u)
    (hv : SzaboLinAlg.Ch08.Bazis T v) : k = l :=
  SzaboLinAlg.Ch08.bazisok_egyenlo_elemszam hu hv

/-- **10.** Bázis esetén a koordináták egyértelműek (8.4). -/
theorem koordinatak_egyertelmuek {T : Type*} [Field T] {V : Type*} [AddCommGroup V]
    [Module T V] {k : ℕ} {u : Fin k → V} (hu : SzaboLinAlg.Ch08.Bazis T u) (x : V) :
    ∃! g : Fin k → T, x = ∑ i, g i • u i :=
  SzaboLinAlg.Ch08.koordinatak_egyertelmuek hu x

/-- **11.** Rangszámtétel: a sorrang és az oszloprang megegyezik (9.2). -/
theorem rangszamtetel {T : Type*} [Field T] {m n : ℕ} (A : Matrix' T m n) :
    SzaboLinAlg.Ch09.sorRang A = SzaboLinAlg.Ch09.oszlopRang A :=
  SzaboLinAlg.Ch09.rangszamtetel A

/-- **11.** Kronecker–Capelli-tétel: az `Ax = b` egyenletrendszer pontosan akkor oldható
meg, ha `r(A) = r(A|b)` (9.7). -/
theorem kronecker_capelli {T : Type*} [Field T] {m n : ℕ} (A : Matrix' T m n)
    (b : Fin m → T) :
    Megoldhato A b ↔ SzaboLinAlg.Ch09.rang A = SzaboLinAlg.Ch09.rang (SzaboLinAlg.Ch09.bovitett A b) :=
  SzaboLinAlg.Ch09.kronecker_capelli A b

end Tematika.LinearisAlgebraI
