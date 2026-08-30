import LinearisAlgebra.Ch13_Baziscsere

/-!
# Szabó László: Bevezetés a lineáris algebrába — 14. fejezet

**Lineáris transzformációk és mátrixok sajátértékei, sajátvektorai és
karakterisztikus polinomja** (a jegyzet 70–71. oldala).

* **14.1. Definíció** — sajátvektor és sajátérték (lineáris transzformációra és
  mátrixra), valamint a karakterisztikus polinom `f_A(x) = |A − xE|` és a
  karakterisztikus gyökök,
* **14.2. Tétel** — (14.2.1) `λ, v` pontosan akkor sajátérték–sajátvektor párja `φ`-nek,
  ha `λ, x` sajátérték–sajátvektor párja a `φ` mátrixának; (14.2.2) `λ` pontosan akkor
  sajátértéke `A`-nak, ha gyöke a karakterisztikus polinomnak,
* **14.3. Tétel** — hasonló mátrixok karakterisztikus polinomja megegyezik,
* **14.4. Definíció** — véges dimenziós vektortér lineáris transzformációjának
  karakterisztikus polinomja (a 13.5. Következmény és a 14.3. Tétel szerint ez
  független a bázis választásától).

A könyv a vektorokat sorvektorként írja, ezért a mátrix sajátérték-egyenlete
`xA = λx` alakú.
-/

namespace SzaboLinAlg
namespace Ch14

open scoped BigOperators
open Polynomial
open SzaboLinAlg.Ch02 SzaboLinAlg.Ch03 SzaboLinAlg.Ch04 SzaboLinAlg.Ch08
  SzaboLinAlg.Ch10 SzaboLinAlg.Ch12 SzaboLinAlg.Ch13

variable {T : Type*} [Field T] {V : Type*} [AddCommGroup V] [Module T V] {n : ℕ}

/-! ## 14.1. Definíció -/

/-- **14.1. Definíció.** A `v ∈ V` vektor a `φ` lineáris transzformáció *sajátvektora*,
ha `v ≠ 0`, és van olyan `λ ∈ T`, hogy `vφ = λv`. -/
def Sajatvektor (f : V → V) (v : V) : Prop := v ≠ 0 ∧ ∃ l : T, f v = l • v

/-- **14.1. Definíció.** A `λ ∈ T` szám a `φ` lineáris transzformáció *sajátértéke*, ha
van olyan `v ≠ 0`, hogy `vφ = λv`. -/
def Sajatertek (T : Type*) [Field T] {V : Type*} [AddCommGroup V] [Module T V]
    (f : V → V) (l : T) : Prop := ∃ v : V, v ≠ 0 ∧ f v = l • v

/-- **14.1. Definíció.** Az `x ∈ Tⁿ` vektor az `A` mátrix *sajátvektora*, ha `x ≠ 0`, és
van olyan `λ ∈ T`, hogy `xA = λx`. -/
def MatrixSajatvektor (A : Matrix' T n n) (x : Fin n → T) : Prop :=
  x ≠ 0 ∧ ∃ l : T, Matrix.vecMul x A = l • x

/-- **14.1. Definíció.** A `λ ∈ T` szám az `A` mátrix *sajátértéke*, ha van olyan
`x ≠ 0`, hogy `xA = λx`. -/
def MatrixSajatertek (A : Matrix' T n n) (l : T) : Prop :=
  ∃ x : Fin n → T, x ≠ 0 ∧ Matrix.vecMul x A = l • x

/-- **14.1. Definíció.** Az `A` mátrix *karakterisztikus polinomja*: `f_A(x) = |A − xE|`. -/
noncomputable def karPol (A : Matrix' T n n) : Polynomial T :=
  (A.map Polynomial.C - Matrix.diagonal fun _ => Polynomial.X).det

/-- A karakterisztikus polinom helyettesítési értéke: `f_A(λ) = |A − λE|`. -/
theorem karPol_eval (A : Matrix' T n n) (l : T) :
    (karPol A).eval l = (A - Matrix.diagonal fun _ => l).det := by
  rw [karPol, ← Polynomial.coe_evalRingHom, RingHom.map_det]
  congr 1
  ext i j
  by_cases h : i = j <;> simp [Matrix.map_apply, h]

/-- **14.1. Definíció.** A `λ` szám az `A` mátrix *karakterisztikus gyöke*, ha gyöke a
karakterisztikus polinomnak. -/
def KarakterisztikusGyok (A : Matrix' T n n) (l : T) : Prop := (karPol A).eval l = 0

/-! ## 14.2. Tétel -/

/-- **(14.2.1)** Ha `A` a `φ` lineáris transzformáció mátrixa az `ℰ` bázisban, és `x`
a `v` vektor koordinátasora, akkor `λ, v` pontosan akkor sajátérték–sajátvektor párja
`φ`-nek, ha `λ, x` sajátérték–sajátvektor párja `A`-nak.

*Bizonyítás.* A 12. fejezet szerint `vφ` koordinátasora `xA`, a `λv` vektoré pedig
`λx`; mivel a koordinátasor egyértelmű, `vφ = λv` ⟺ `xA = λx`. Végül `v ≠ 0` pontosan
akkor teljesül, ha `x ≠ 0`. -/
theorem sajat_iff_matrix {f : V → V} (hf : LinearisLekepezes T f) {e : Fin n → V}
    (he : Bazis T e) {A : Matrix' T n n} (hA : LekepezesMatrixa f e e A) (v : V) (l : T) :
    (v ≠ 0 ∧ f v = l • v) ↔
      (koordinatai he v ≠ 0 ∧ Matrix.vecMul (koordinatai he v) A = l • koordinatai he v) := by
  have hzero : koordinatai he v = 0 ↔ v = 0 := koordinatai_eq_zero_iff he v
  constructor
  · rintro ⟨hv, hfv⟩
    refine ⟨fun h => hv (hzero.1 h), ?_⟩
    rw [← koordinatai_map hf he he hA v, hfv, koordinatai_smul]
  · rintro ⟨hx, hxA⟩
    refine ⟨fun h => hx (hzero.2 h), ?_⟩
    refine koordinatai_injective he ?_
    rw [koordinatai_map hf he he hA v, hxA, koordinatai_smul]

/-- **(14.2.1)** Következmény: `λ` pontosan akkor sajátértéke `φ`-nek, ha sajátértéke a
`φ` (bármely bázisbeli) mátrixának. -/
theorem sajatertek_iff_matrixSajatertek {f : V → V} (hf : LinearisLekepezes T f)
    {e : Fin n → V} (he : Bazis T e) {A : Matrix' T n n} (hA : LekepezesMatrixa f e e A)
    (l : T) : Sajatertek T f l ↔ MatrixSajatertek A l := by
  constructor
  · rintro ⟨v, hv⟩
    exact ⟨koordinatai he v, (sajat_iff_matrix hf he hA v l).1 hv⟩
  · rintro ⟨x, hx0, hx⟩
    refine ⟨∑ i, x i • e i, ?_⟩
    have hcoord : koordinatai he (∑ i, x i • e i) = x := koordinatai_eq he rfl
    refine (sajat_iff_matrix hf he hA _ l).2 ?_
    rw [hcoord]
    exact ⟨hx0, hx⟩

/-- **(14.2.2)** A `λ ∈ T` szám pontosan akkor sajátértéke az `A` mátrixnak, ha gyöke `A`
karakterisztikus polinomjának.

*Bizonyítás.* `xA = λx` ⟺ `x(A − λE) = 0`; ilyen `x ≠ 0` pontosan akkor létezik, ha az
`A − λE` mátrix elfajuló, azaz ha `|A − λE| = f_A(λ) = 0`. -/
theorem matrixSajatertek_iff_karakterisztikusGyok (A : Matrix' T n n) (l : T) :
    MatrixSajatertek A l ↔ KarakterisztikusGyok A l := by
  have hkulcs : ∀ x : Fin n → T,
      Matrix.vecMul x (A - Matrix.diagonal fun _ => l) = 0 ↔ Matrix.vecMul x A = l • x := by
    intro x
    have hd : Matrix.vecMul x (Matrix.diagonal fun _ => l) = l • x := by
      funext i
      simp [Matrix.vecMul_diagonal, mul_comm]
    rw [Matrix.vecMul_sub, sub_eq_zero, hd]
  rw [KarakterisztikusGyok, karPol_eval, ← Matrix.exists_vecMul_eq_zero_iff]
  constructor
  · rintro ⟨x, hx0, hx⟩
    exact ⟨x, hx0, (hkulcs x).2 hx⟩
  · rintro ⟨x, hx0, hx⟩
    exact ⟨x, hx0, (hkulcs x).1 hx⟩

/-! ## 14.3. Tétel -/

/-- **14.3. Tétel.** Hasonló mátrixok karakterisztikus polinomja megegyezik.

*Bizonyítás.* Ha `B = X⁻¹AX`, akkor `B − xE = X⁻¹(A − xE)X`, ezért
`f_B(x) = |X⁻¹||A − xE||X| = |X⁻¹X||A − xE| = |A − xE| = f_A(x)`. -/
theorem karPol_hasonlo {A B : Matrix' T n n} (h : Hasonlo A B) : karPol B = karPol A := by
  obtain ⟨X, Y, ⟨hYX, hXY⟩, rfl⟩ := h
  have hmap : ∀ M N : Matrix' T n n,
      (M * N).map (Polynomial.C : T → Polynomial T)
        = M.map Polynomial.C * N.map Polynomial.C := by
    intro M N
    simp
  have hone : (1 : Matrix' T n n).map (Polynomial.C : T → Polynomial T) = 1 := by
    simp
  have hYXone : Y.map (Polynomial.C : T → Polynomial T) * X.map Polynomial.C = 1 := by
    rw [← hmap, hYX, hone]
  have hkozep : Y.map (Polynomial.C : T → Polynomial T)
      * (Matrix.diagonal fun _ : Fin n => (Polynomial.X : Polynomial T))
      * X.map Polynomial.C = Matrix.diagonal fun _ => Polynomial.X := by
    rw [← Matrix.smul_one_eq_diagonal, Matrix.mul_smul, Matrix.smul_mul, mul_one, hYXone]
  have hkulcs : Y.map (Polynomial.C : T → Polynomial T)
      * (A.map Polynomial.C - Matrix.diagonal fun _ : Fin n => (Polynomial.X : Polynomial T))
      * X.map Polynomial.C
      = (Y * A * X).map Polynomial.C - Matrix.diagonal fun _ => Polynomial.X := by
    rw [Matrix.mul_sub, Matrix.sub_mul, hkozep, hmap, hmap]
  rw [karPol, karPol, ← hkulcs, Matrix.det_mul, Matrix.det_mul]
  have hdet : (Y.map (Polynomial.C : T → Polynomial T)).det
      * (X.map Polynomial.C).det = 1 := by
    rw [← Matrix.det_mul, hYXone, Matrix.det_one]
  calc (Y.map (Polynomial.C : T → Polynomial T)).det
        * (A.map Polynomial.C - Matrix.diagonal fun _ => Polynomial.X).det
        * (X.map Polynomial.C).det
      = ((Y.map (Polynomial.C : T → Polynomial T)).det * (X.map Polynomial.C).det)
        * (A.map Polynomial.C - Matrix.diagonal fun _ => Polynomial.X).det := by ring
    _ = (A.map Polynomial.C
          - Matrix.diagonal fun _ => Polynomial.X).det := by rw [hdet, one_mul]

/-! ## 14.4. Definíció -/

/-- **14.4. Definíció.** A lineáris transzformáció karakterisztikus polinomja a
transzformáció valamely bázisbeli mátrixának karakterisztikus polinomja. Ez a 13.5.
Következmény és a 14.3. Tétel szerint független a bázis megválasztásától. -/
theorem karPol_fuggetlen_bazistol {f : V → V} (hf : LinearisLekepezes T f)
    {e e' : Fin n → V} (he : Bazis T e) (he' : Bazis T e') {A A' : Matrix' T n n}
    (hA : LekepezesMatrixa f e e A) (hA' : LekepezesMatrixa f e' e' A') :
    karPol A' = karPol A := by
  obtain ⟨P, hP, -⟩ := letezik_egyertelmu_atteres (T := T) (e := e) he'
  exact karPol_hasonlo (hasonlo_baziscsere hf he he' hP hA hA')

/-- **14.4. Definíció.** A `φ` lineáris transzformáció karakterisztikus polinomja az
`ℰ` bázisban felírt mátrixának karakterisztikus polinomja. -/
noncomputable def transzformacioKarPol {f : V → V} {e : Fin n → V} (he : Bazis T e)
    (_hf : LinearisLekepezes T f) : Polynomial T := karPol (matrixa e he f)

end Ch14
end SzaboLinAlg
