import LinearisAlgebra.Ch04_Inverzmatrix

/-!
# Szabó László: Bevezetés a lineáris algebrába — 5. fejezet: Lineáris egyenletrendszerek

A jegyzet 5. fejezetének (24–31. oldal) formalizálása:

* **5.1. Definíció** — a lineáris egyenletrendszer és megoldása; az egyenletrendszer
  mátrixa, bővített mátrixa, mátrix- és vektoregyenlet alakja; homogén egyenletrendszer,
  triviális megoldás,
* **5.2. Definíció** — ekvivalens egyenletrendszerek és az elemi átalakítások: minden
  elemi átalakítás ekvivalens egyenletrendszerbe visz,
* **5.7. Definíció** — szabályos egyenletrendszer,
* **5.8. Cramer-szabály** — a szabályos egyenletrendszernek egyetlen megoldása van,
  mégpedig `xₖ = Dₖ/D`,
* **5.9. Következmény** — ha egy négyzetes mátrixú homogén egyenletrendszernek van
  triviálistól különböző megoldása, akkor `|A| = 0`,
* **5.10. Definíció, 5.11. Tétel** — a megoldáshalmaz szerkezete.
-/

namespace SzaboLinAlg
namespace Ch05

open scoped BigOperators
open Matrix SzaboLinAlg.Ch02 SzaboLinAlg.Ch03 SzaboLinAlg.Ch04

variable {T : Type*} [Field T] {m n : ℕ}

/-! ## 5.1. Definíció: lineáris egyenletrendszer és megoldása -/

/-- **5.1. Definíció.** A `c = (c₁,…,cₙ)` elem-`n`-es *megoldása* az `A` mátrixú, `b`
konstansvektorú lineáris egyenletrendszernek, ha minden `i`-re
`aᵢ₁c₁ + … + aᵢₙcₙ = bᵢ`. -/
def Megoldasa (A : Matrix' T m n) (b : Fin m → T) (c : Fin n → T) : Prop :=
  ∀ i, ∑ j, A i j * c j = b i

/-- Az egyenletrendszer *mátrixegyenlet* alakja: `Ax = b`. -/
theorem megoldasa_iff_mulVec (A : Matrix' T m n) (b : Fin m → T) (c : Fin n → T) :
    Megoldasa A b c ↔ A.mulVec c = b := by
  constructor
  · intro h; funext i; exact h i
  · intro h i; exact congrFun h i

/-- Az egyenletrendszer *vektoregyenlet* alakja: `x₁a₁ + … + xₙaₙ = b`, ahol `aⱼ` az `A`
mátrix `j`-edik oszlopvektora. -/
theorem megoldasa_iff_oszlopok (A : Matrix' T m n) (b : Fin m → T) (c : Fin n → T) :
    Megoldasa A b c ↔ ∀ i, ∑ j, c j * A i j = b i := by
  constructor <;> intro h i
  · rw [← h i]; exact Finset.sum_congr rfl fun j _ => mul_comm _ _
  · rw [← h i]; exact Finset.sum_congr rfl fun j _ => mul_comm _ _

/-- **5.1. Definíció.** Az egyenletrendszer *megoldható*, ha van megoldása. -/
def Megoldhato (A : Matrix' T m n) (b : Fin m → T) : Prop := ∃ c, Megoldasa A b c

/-- **5.1. Definíció.** Az egyenletrendszer *ellentmondó*, ha nincs megoldása. -/
def Ellentmondo (A : Matrix' T m n) (b : Fin m → T) : Prop := ¬ Megoldhato A b

/-- **5.1. Definíció.** A homogén lineáris egyenletrendszernek (`Ax = 0`) mindig megoldása
a csupa nulla oszlopvektor: a *triviális megoldás*. -/
theorem trivialis_megoldas (A : Matrix' T m n) : Megoldasa A 0 (fun _ => 0) := by
  intro i; simp

/-! ## 5.2. Definíció: ekvivalens egyenletrendszerek, elemi átalakítások -/

/-- **5.2. Definíció.** Két egyenletrendszer *ekvivalens*, ha pontosan ugyanazok a
megoldásaik. -/
def Ekvivalens (A : Matrix' T m n) (b : Fin m → T) (A' : Matrix' T m n) (b' : Fin m → T) :
    Prop := ∀ c, Megoldasa A b c ↔ Megoldasa A' b' c

/-- **(5.2.b)** Ha egy egyenletet (a bővített mátrix egy sorát) nullától különböző
skalárral szorzunk, ekvivalens egyenletrendszert kapunk. -/
theorem ekvivalens_sor_szorzas (A : Matrix' T m n) (b : Fin m → T) (i₀ : Fin m) {lam : T}
    (hlam : lam ≠ 0) :
    Ekvivalens A b (A.updateRow i₀ (lam • A i₀)) (Function.update b i₀ (lam * b i₀)) := by
  intro c
  have key : ∑ j, (lam • A i₀) j * c j = lam * ∑ j, A i₀ j * c j := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by simp [mul_assoc]
  constructor
  · intro h i
    rcases eq_or_ne i i₀ with rfl | hi
    · rw [Matrix.updateRow_self, Function.update_self, key, h i]
    · rw [Matrix.updateRow_ne hi, Function.update_of_ne hi]
      exact h i
  · intro h i
    rcases eq_or_ne i i₀ with rfl | hi
    · have hi₀ := h i
      rw [Matrix.updateRow_self, Function.update_self, key] at hi₀
      exact mul_left_cancel₀ hlam hi₀
    · have hi' := h i
      rwa [Matrix.updateRow_ne hi, Function.update_of_ne hi] at hi'

/-- **(5.2.c)** Ha egy egyenlethez egy másik egyenlet skalárszorosát adjuk, ekvivalens
egyenletrendszert kapunk. -/
theorem ekvivalens_sor_hozzaadas (A : Matrix' T m n) (b : Fin m → T) {i₀ j₀ : Fin m}
    (hij : i₀ ≠ j₀) (lam : T) :
    Ekvivalens A b (A.updateRow i₀ (A i₀ + lam • A j₀))
      (Function.update b i₀ (b i₀ + lam * b j₀)) := by
  intro c
  have key : ∑ j, (A i₀ + lam • A j₀) j * c j
      = (∑ j, A i₀ j * c j) + lam * ∑ j, A j₀ j * c j := by
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by simp [add_mul, mul_assoc]
  constructor
  · intro h i
    rcases eq_or_ne i i₀ with rfl | hi
    · rw [Matrix.updateRow_self, Function.update_self, key, h i, h j₀]
    · rw [Matrix.updateRow_ne hi, Function.update_of_ne hi]
      exact h i
  · intro h i
    have hj : ∑ j, A j₀ j * c j = b j₀ := by
      have hj' := h j₀
      rwa [Matrix.updateRow_ne (Ne.symm hij), Function.update_of_ne (Ne.symm hij)] at hj'
    rcases eq_or_ne i i₀ with rfl | hi
    · have hi₀ := h i
      rw [Matrix.updateRow_self, Function.update_self, key, hj] at hi₀
      exact add_right_cancel hi₀
    · have hi' := h i
      rwa [Matrix.updateRow_ne hi, Function.update_of_ne hi] at hi'

/-- **(5.2.d)** Két egyenlet felcserélése ekvivalens egyenletrendszert ad. -/
theorem ekvivalens_sorcsere (A : Matrix' T m n) (b : Fin m → T) (i₀ j₀ : Fin m) :
    Ekvivalens A b (A.submatrix (Equiv.swap i₀ j₀) id) (b ∘ Equiv.swap i₀ j₀) := by
  intro c
  constructor
  · intro h i
    exact h (Equiv.swap i₀ j₀ i)
  · intro h i
    have := h (Equiv.swap i₀ j₀ i)
    simpa using this

/-! ## 5.7. Definíció, 5.8. Cramer-szabály -/

/-- **5.7. Definíció.** Az egyenletrendszer *szabályos*, ha ugyanannyi egyenlete van, mint
ismeretlene, és `|A| ≠ 0`. -/
def Szabalyos (A : Matrix' T n n) : Prop := det' A ≠ 0

/-- A Cramer-szabályban szereplő `Dₖ` determináns: az `A` mátrix `k`-adik oszlopát a `b`
konstansvektorral helyettesítve kapott determináns. -/
def cramerDet (A : Matrix' T n n) (b : Fin n → T) (k : Fin n) : T :=
  det' (A.updateCol k b)

/-- **5.8. Cramer-szabály (a megoldás alakja).** A szabályos egyenletrendszer megoldása
`xₖ = Dₖ/D`. -/
theorem cramer_megoldas (A : Matrix' T (n + 1) (n + 1)) (b : Fin (n + 1) → T)
    (h : Szabalyos A) :
    Megoldasa A b (fun k => cramerDet A b k / det' A) := by
  have hdet : A.det ≠ 0 := by rw [← det'_eq_det]; exact h
  rw [megoldasa_iff_mulVec]
  have hvec : (fun k => cramerDet A b k / det' A) = (A.det)⁻¹ • A.cramer b := by
    funext k
    rw [cramerDet, det'_eq_det, det'_eq_det]
    simp [Matrix.cramer_apply, div_eq_inv_mul]
  rw [hvec, Matrix.mulVec_smul, Matrix.mulVec_cramer, smul_smul, inv_mul_cancel₀ hdet,
    one_smul]

/-- **5.8. Cramer-szabály.** Ha az egyenletrendszer szabályos, akkor egyetlen megoldása
van, mégpedig `xₖ = Dₖ/D`, ahol `D = |A|`.

*Bizonyítás (a jegyzet szerint).* Mivel `|A| ≠ 0`, létezik `A⁻¹`, és `Ac = b`-ből
`c = A⁻¹b`; megfordítva `A⁻¹b` valóban megoldás. Az `A⁻¹ = (1/|A|)·adj A` alakot
felhasználva a megoldásvektor `k`-adik eleme `(1/|A|)·∑ᵢ bᵢAᵢₖ`, ami épp `Dₖ/D`, hiszen
`∑ᵢ bᵢAᵢₖ` a `Dₖ` determináns `k`-adik oszlop szerinti kifejtése. -/
theorem cramer_szabaly (A : Matrix' T (n + 1) (n + 1)) (b : Fin (n + 1) → T)
    (h : Szabalyos A) :
    ∃! c : Fin (n + 1) → T, Megoldasa A b c := by
  have hdet : A.det ≠ 0 := by rw [← det'_eq_det]; exact h
  have hu : IsUnit A.det := isUnit_iff_ne_zero.2 hdet
  refine ⟨_, cramer_megoldas A b h, ?_⟩
  intro c hc
  have h1 : A.mulVec c = b := (megoldasa_iff_mulVec A b c).1 hc
  have h2 : A.mulVec (fun k => cramerDet A b k / det' A) = b :=
    (megoldasa_iff_mulVec A b _).1 (cramer_megoldas A b h)
  have h3 := congrArg (fun v => A⁻¹.mulVec v) (h1.trans h2.symm)
  simpa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu] using h3

/-- **5.9. Következmény.** Ha az `Ax = 0` négyzetes mátrixú homogén egyenletrendszernek
van triviálistól különböző megoldása, akkor `|A| = 0`.

*Bizonyítás (a jegyzet szerint).* Ha `|A| ≠ 0` volna, akkor a Cramer-szabály szerint
egyetlen megoldás lenne, a triviális; ez ellentmondás. -/
theorem det_nulla_nemtrivialis_megoldas (A : Matrix' T (n + 1) (n + 1))
    {c : Fin (n + 1) → T} (hc : Megoldasa A 0 c) (hc0 : c ≠ 0) : det' A = 0 := by
  by_contra hdet
  obtain ⟨d, _, huniq⟩ := cramer_szabaly A 0 hdet
  exact hc0 ((huniq c hc).trans (huniq 0 (trivialis_megoldas A)).symm)

/-! ## 5.10. Definíció, 5.11. Tétel: a megoldáshalmaz szerkezete -/

/-- **(5.11.1)** Ha `c` és `d` megoldása `Ax = b`-nek, akkor `c - d` megoldása a hozzá
tartozó `Ax = 0` homogén egyenletrendszernek. -/
theorem kulonbseg_homogen_megoldas {A : Matrix' T m n} {b : Fin m → T} {c d : Fin n → T}
    (hc : Megoldasa A b c) (hd : Megoldasa A b d) : Megoldasa A 0 (c - d) := by
  intro i
  have : ∑ j, A i j * (c j - d j) = (∑ j, A i j * c j) - ∑ j, A i j * d j := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  simp [this, hc i, hd i]

/-- **(5.11.2)** A homogén egyenletrendszer megoldásainak halmaza zárt az összeadásra és a
skalárral való szorzásra. -/
theorem homogen_megoldasok_zart {A : Matrix' T m n} {c d : Fin n → T} (lam : T)
    (hc : Megoldasa A 0 c) (hd : Megoldasa A 0 d) :
    Megoldasa A 0 (c + d) ∧ Megoldasa A 0 (lam • c) := by
  constructor
  · intro i
    have : ∑ j, A i j * (c j + d j) = (∑ j, A i j * c j) + ∑ j, A i j * d j := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    simp [this, hc i, hd i]
  · intro i
    have : ∑ j, A i j * (lam * c j) = lam * ∑ j, A i j * c j := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    simp [this, hc i]

/-- **(5.11.3)** Ha `c₀` megoldása `Ax = b`-nek és `d` megoldása `Ax = 0`-nak, akkor
`c₀ + d` megoldása `Ax = b`-nek; megfordítva, `Ax = b` minden `c` megoldásához van olyan
`d` megoldása `Ax = 0`-nak, hogy `c = c₀ + d`. -/
theorem megoldashalmaz_szerkezete {A : Matrix' T m n} {b : Fin m → T} {c₀ : Fin n → T}
    (hc₀ : Megoldasa A b c₀) :
    (∀ d, Megoldasa A 0 d → Megoldasa A b (c₀ + d)) ∧
      (∀ c, Megoldasa A b c → ∃ d, Megoldasa A 0 d ∧ c = c₀ + d) := by
  constructor
  · intro d hd i
    have : ∑ j, A i j * (c₀ j + d j) = (∑ j, A i j * c₀ j) + ∑ j, A i j * d j := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun j _ => by ring
    simp [this, hc₀ i, hd i]
  · intro c hc
    refine ⟨c - c₀, kulonbseg_homogen_megoldas hc hc₀, ?_⟩
    funext j; simp

end Ch05
end SzaboLinAlg
