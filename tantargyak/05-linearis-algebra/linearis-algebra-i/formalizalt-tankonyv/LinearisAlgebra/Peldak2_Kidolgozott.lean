import LinearisAlgebra.Ch05_Egyenletrendszerek
import LinearisAlgebra.Ch14_Sajatertek

/-!
# Szabó László: Bevezetés a lineáris algebrába — kidolgozott gyakorlófeladatok

Ez a modul a *Lineáris algebra I. (MBLK15E)* tematika tipikus számolási feladatait
dolgozza ki **konkrét** mátrixokon, végig a jegyzet saját fogalmaival és tételeire
hivatkozva:

* **1.** háromismeretlenes szabályos egyenletrendszer megoldása a **Cramer-szabállyal**
  (5.7. Definíció, 5.8. Tétel),
* **2.** konkrét mátrix **inverze** a 4.1. Definíció értelmében (`Inverze`),
* **3.** konkrét mátrix **sajátértékei és sajátvektorai**, a karakterisztikus polinom
  gyökeiként (14.1. Definíció, `karPol`).

A számítások a racionális számtest (`ℚ`) felett történnek, ahol minden művelet
kiszámítható, így a `det'` rekurzív determináns értéke fordítási időben ellenőrizhető.
-/

namespace SzaboLinAlg
namespace Peldak2

open scoped BigOperators
open Matrix SzaboLinAlg.Ch02 SzaboLinAlg.Ch03 SzaboLinAlg.Ch04 SzaboLinAlg.Ch05
open SzaboLinAlg.Ch14

/-! ## 1. Szabályos egyenletrendszer megoldása a Cramer-szabállyal

Tekintsük a

```
 2x₁ +  x₂ -  x₃ =   8
-3x₁ -  x₂ + 2x₃ = -11
-2x₁ +  x₂ + 2x₃ =  -3
```

egyenletrendszert. Az együtthatómátrix determinánsa `-1 ≠ 0`, tehát az egyenletrendszer
*szabályos* (5.7. Definíció), így a Cramer-szabály (5.8. Tétel) szerint pontosan egy
megoldása van; ez a megoldás `x = (2, 3, -1)`.
-/

/-- Az egyenletrendszer együtthatómátrixa. -/
def Acr : Matrix' ℚ 3 3 := !![2, 1, -1; -3, -1, 2; -2, 1, 2]

/-- Az egyenletrendszer konstansvektora. -/
def bcr : Fin 3 → ℚ := ![8, -11, -3]

/-- Az egyenletrendszer megoldásvektora. -/
def xcr : Fin 3 → ℚ := ![2, 3, -1]

/-- Az együtthatómátrix determinánsa a jegyzet rekurzív definíciója szerint `-1`. -/
theorem det_Acr : det' Acr = -1 := by
  rw [det'_eq_det, Acr]
  simp [Matrix.det_fin_three]
  norm_num

/-- Az egyenletrendszer *szabályos* (5.7. Definíció): `|A| ≠ 0`. -/
theorem szabalyos_Acr : Szabalyos Acr := by
  rw [Szabalyos, det_Acr]; norm_num

/-- Az `x = (2, 3, -1)` vektor megoldása az egyenletrendszernek (5.1. Definíció). -/
theorem megoldasa_Acr : Megoldasa Acr bcr xcr := by
  intro i
  fin_cases i <;> simp [Acr, bcr, xcr, Fin.sum_univ_succ] <;> norm_num

/-- **5.8. Cramer-szabály.** Mivel az egyenletrendszer szabályos, `x = (2, 3, -1)` az
*egyetlen* megoldása. -/
theorem egyertelmu_megoldas_Acr :
    ∀ c : Fin 3 → ℚ, Megoldasa Acr bcr c → c = xcr := by
  obtain ⟨d, -, huniq⟩ := cramer_szabaly (n := 2) Acr bcr szabalyos_Acr
  intro c hc
  rw [huniq c hc, huniq xcr megoldasa_Acr]

/-! ## 2. Konkrét mátrix inverze (4.1. Definíció)

A `4.6. Tétel` szerint egy négyzetes mátrixnak pontosan akkor van inverze, ha
determinánsa nem nulla. Az alábbi mátrix determinánsa `1`, inverzét az adjungált
mátrixszal számolva kapjuk.
-/

/-- Egy `3 × 3`-as, egész elemű mátrix, amelynek determinánsa `1`. -/
def Ainv : Matrix' ℚ 3 3 := !![1, 2, 3; 0, 1, 4; 5, 6, 0]

/-- Az `Ainv` mátrix determinánsa `1`. -/
theorem det_Ainv : det' Ainv = 1 := by
  rw [det'_eq_det, Ainv]
  simp [Matrix.det_fin_three]
  norm_num

/-- Az `Ainv` mátrix inverze. -/
def Ainv_inv : Matrix' ℚ 3 3 := !![-24, 18, 5; 20, -15, -4; -5, 4, 1]

/-- A `4.1. Definíció` szerinti inverzreláció: `Ainv · Ainv⁻¹ = E` és
`Ainv⁻¹ · Ainv = E`. -/
theorem Ainv_inverze : Inverze Ainv Ainv_inv := by
  constructor <;>
  · ext i j
    fin_cases i <;> fin_cases j <;>
      norm_num [Ainv, Ainv_inv, Matrix.mul_apply, Fin.sum_univ_succ, Matrix.one_apply]

/-! ## 3. Sajátértékek és sajátvektorok (14.1. Definíció)

Az `A = !![2, 1; 1, 2]` szimmetrikus mátrix karakterisztikus polinomja
`f_A(x) = (2 - x)² - 1`, amelynek gyökei `1` és `3`. A hozzájuk tartozó sajátvektorok
`(1, -1)`, illetve `(1, 1)`.
-/

/-- A vizsgált szimmetrikus mátrix. -/
def Asaj : Matrix' ℚ 2 2 := !![2, 1; 1, 2]

/-- A karakterisztikus polinom helyettesítési értéke: `f_A(λ) = (2 - λ)² - 1`. -/
theorem karPol_Asaj_eval (l : ℚ) : (karPol Asaj).eval l = (2 - l) ^ 2 - 1 := by
  rw [karPol_eval]
  rw [Matrix.det_fin_two]
  simp [Asaj, Matrix.diagonal]
  ring

/-- `1` karakterisztikus gyök (14.1. Definíció). -/
theorem karGyok_egy : KarakterisztikusGyok Asaj 1 := by
  rw [KarakterisztikusGyok, karPol_Asaj_eval]; norm_num

/-- `3` karakterisztikus gyök (14.1. Definíció). -/
theorem karGyok_harom : KarakterisztikusGyok Asaj 3 := by
  rw [KarakterisztikusGyok, karPol_Asaj_eval]; norm_num

/-- A karakterisztikus polinomnak `1`-en és `3`-on kívül nincs más gyöke. -/
theorem karGyokok_Asaj (l : ℚ) : KarakterisztikusGyok Asaj l ↔ l = 1 ∨ l = 3 := by
  rw [KarakterisztikusGyok, karPol_Asaj_eval]
  constructor
  · intro h
    have hfac : (l - 1) * (l - 3) = 0 := by linear_combination h
    rcases mul_eq_zero.1 hfac with h1 | h2
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  · rintro (rfl | rfl) <;> norm_num

/-- Az `1` sajátértékhez tartozó sajátvektor: `(1, -1)` (14.1. Definíció). -/
theorem sajatertek_egy : MatrixSajatertek Asaj 1 := by
  refine ⟨![1, -1], ?_, ?_⟩
  · intro h
    have := congrFun h 0
    norm_num at this
  · funext i
    fin_cases i <;> simp [Asaj, Matrix.vecMul, dotProduct, Fin.sum_univ_succ] <;>
      norm_num

/-- A `3` sajátértékhez tartozó sajátvektor: `(1, 1)` (14.1. Definíció). -/
theorem sajatertek_harom : MatrixSajatertek Asaj 3 := by
  refine ⟨![1, 1], ?_, ?_⟩
  · intro h
    have := congrFun h 0
    norm_num at this
  · funext i
    fin_cases i <;> simp [Asaj, Matrix.vecMul, dotProduct, Fin.sum_univ_succ] <;>
      norm_num

end Peldak2
end SzaboLinAlg
