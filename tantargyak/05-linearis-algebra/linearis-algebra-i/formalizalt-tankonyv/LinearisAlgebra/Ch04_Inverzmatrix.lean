import LinearisAlgebra.Ch03_Determinans

/-!
# Szabó László: Bevezetés a lineáris algebrába — 4. fejezet: Inverzmátrix

A jegyzet 4. fejezetének (21–23. oldal) formalizálása:

* **4.1. Definíció** — az inverzmátrix fogalma,
* **4.2. Tétel** — az inverz egyértelmű; `A`-nak akkor és csak akkor van inverze, ha
  `|A| ≠ 0`; az inverz explicit alakja az adjungált aldeterminánsokkal; továbbá
  `(A⁻¹)⁻¹ = A`, `(AB)⁻¹ = B⁻¹A⁻¹` és `(Aᵀ)⁻¹ = (A⁻¹)ᵀ`,
* **4.3. Definíció** — elfajuló és nemelfajuló mátrix,
* **4.4. Definíció** — hasonló mátrixok,
* **4.5. Tétel** — a hasonlóság ekvivalenciareláció, és hasonló mátrixok determinánsa
  megegyezik.

A bizonyítás kulcslépése a *ferde kifejtési tétel*: ha egy sor elemeit egy másik sorhoz
tartozó adjungált aldeterminánsokkal szorozzuk össze, az összeg nulla.
-/

namespace SzaboLinAlg
namespace Ch04

open scoped BigOperators
open Matrix SzaboLinAlg.Ch02 SzaboLinAlg.Ch03

variable {T : Type*} [Field T] {n : ℕ}

/-! ## 4.1. Definíció: az inverzmátrix -/

/-- **4.1. Definíció.** Az `X ∈ Tⁿˣⁿ` mátrix az `A` mátrix *inverze*, ha `XA = AX = E`,
ahol `E` az `n × n`-es egységmátrix. -/
def Inverze (A X : Matrix' T n n) : Prop := X * A = 1 ∧ A * X = 1

/-! ## 4.2. Tétel -/

/-- **4.2. Tétel (első állítás).** Minden mátrixnak legfeljebb egy inverze van.

*Bizonyítás (a jegyzet szerint).* Ha `A`-nak `X` és `Y` is inverze, akkor
`X = XE = X(AY) = (XA)Y = EY = Y`. -/
theorem inverz_egyertelmu {A X Y : Matrix' T n n} (hX : Inverze A X) (hY : Inverze A Y) :
    X = Y := by
  calc X = X * 1 := (Matrix.mul_one X).symm
    _ = X * (A * Y) := by rw [hY.2]
    _ = (X * A) * Y := (Matrix.mul_assoc X A Y).symm
    _ = 1 * Y := by rw [hX.1]
    _ = Y := Matrix.one_mul Y

/-- **4.2. Tétel (második állítás, szükségesség).** Ha `A`-nak van inverze, akkor
`|A| ≠ 0`.

*Bizonyítás (a jegyzet szerint).* `1 = |E| = |AX| = |A|·|X|`, tehát `|A| ≠ 0`. -/
theorem det_ne_zero_of_inverze {A X : Matrix' T n n} (h : Inverze A X) : det' A ≠ 0 := by
  intro h0
  have h1 : det' A * det' X = 1 := by
    rw [det'_eq_det, det'_eq_det, ← Matrix.det_mul, h.2, Matrix.det_one]
  rw [h0, zero_mul] at h1
  exact zero_ne_one h1

/-- Egy sor kicserélése nem változtatja meg az *ahhoz a sorhoz* tartozó adjungált
aldeterminánsokat, hiszen azok kiszámításához épp ezt a sort hagyjuk el. -/
theorem adjungaltAldeterminans_updateRow (A : Matrix' T (n + 1) (n + 1)) (j : Fin (n + 1))
    (v : Fin (n + 1) → T) (k : Fin (n + 1)) :
    adjungaltAldeterminans (A.updateRow j v) j k = adjungaltAldeterminans A j k := by
  unfold adjungaltAldeterminans komplementerAldeterminans
  congr 2
  ext p q
  simp only [Matrix.submatrix_apply]
  exact congrFun (Matrix.updateRow_ne (j.succAbove_ne p)) _

/-- **Ferde kifejtési tétel (sorokra).** Ha `i ≠ j`, akkor az `i`-edik sor elemeinek és a
`j`-edik sorhoz tartozó adjungált aldeterminánsoknak a szorzatösszege nulla.

*Bizonyítás.* Az összeg annak a mátrixnak a `j`-edik sor szerinti kifejtése, amelyben a
`j`-edik sort az `i`-edikkel helyettesítettük; ennek két egyforma sora van, tehát a
determinánsa nulla. -/
theorem ferde_kifejtes_sor (A : Matrix' T (n + 1) (n + 1)) {i j : Fin (n + 1)} (hij : i ≠ j) :
    ∑ k, A i k * adjungaltAldeterminans A j k = 0 := by
  have hupd := adjungaltAldeterminans_updateRow A j (A i)
  have hdet : det' (A.updateRow j (A i)) = 0 :=
    det_egyforma_sor _ hij (by rw [Matrix.updateRow_ne hij, Matrix.updateRow_self])
  have := det_kifejtes_sor (A.updateRow j (A i)) j
  rw [hdet] at this
  rw [this]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [hupd k, Matrix.updateRow_self]

/-- Az `A` mátrix *adjungált mátrixa*: az adjungált aldeterminánsokból alkotott mátrix
transzponáltja (a jegyzetben a 4.2. Tétel bizonyításában szereplő mátrix). -/
def adjungaltMatrix (A : Matrix' T (n + 1) (n + 1)) : Matrix' T (n + 1) (n + 1) :=
  fun i j => adjungaltAldeterminans A j i

/-- A jegyzet adjungált mátrixa megegyezik a Mathlib `Matrix.adjugate` fogalmával.

*Bizonyítás.* A Mathlib szerint `adj A i j = |A(j-edik sorát eᵢ-re cserélve)|`; ezt a
`j`-edik sora szerint kifejtve épp az `Aⱼᵢ` adjungált aldeterminánst kapjuk. -/
theorem adjungaltMatrix_eq_adjugate (A : Matrix' T (n + 1) (n + 1)) :
    adjungaltMatrix A = A.adjugate := by
  ext i j
  show adjungaltAldeterminans A j i = A.adjugate i j
  rw [Matrix.adjugate_apply, ← det'_eq_det, det_kifejtes_sor _ j, Finset.sum_eq_single i]
  · rw [adjungaltAldeterminans_updateRow, Matrix.updateRow_self, Pi.single_eq_same, one_mul]
  · intro k _ hk
    rw [adjungaltAldeterminans_updateRow, Matrix.updateRow_self, Pi.single_eq_of_ne hk,
      zero_mul]
  · intro h; exact absurd (Finset.mem_univ i) h

/-- Az `A · adj A = |A| · E` azonosság: a főátlóban a kifejtési tétel, azon kívül a ferde
kifejtési tétel áll. -/
theorem mul_adjungaltMatrix (A : Matrix' T (n + 1) (n + 1)) :
    A * adjungaltMatrix A = det' A • (1 : Matrix' T (n + 1) (n + 1)) := by
  ext i j
  rw [Matrix.mul_apply]
  by_cases hij : i = j
  · subst hij
    simp only [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
    exact (det_kifejtes_sor A i).symm
  · simp only [Matrix.smul_apply, Matrix.one_apply_ne hij, smul_eq_mul, mul_zero]
    exact ferde_kifejtes_sor A hij

/-- Az `adj A · A = |A| · E` azonosság (a ferde kifejtési tétel oszlopokra vonatkozó
állításával). -/
theorem adjungaltMatrix_mul (A : Matrix' T (n + 1) (n + 1)) :
    adjungaltMatrix A * A = det' A • (1 : Matrix' T (n + 1) (n + 1)) := by
  rw [adjungaltMatrix_eq_adjugate, det'_eq_det, Matrix.adjugate_mul]

/-- **4.2. Tétel (második állítás, elegendőség).** Ha `|A| ≠ 0`, akkor `A`-nak van
inverze, mégpedig `A⁻¹ = (1/|A|)·adj A`, ahol `adj A` az adjungált aldeterminánsokból
alkotott mátrix transzponáltja. -/
theorem inverze_of_det_ne_zero {A : Matrix' T (n + 1) (n + 1)} (h : det' A ≠ 0) :
    Inverze A ((det' A)⁻¹ • adjungaltMatrix A) := by
  constructor
  · rw [Matrix.smul_mul, adjungaltMatrix_mul, smul_smul, inv_mul_cancel₀ h, one_smul]
  · rw [Matrix.mul_smul, mul_adjungaltMatrix, smul_smul, inv_mul_cancel₀ h, one_smul]

/-- **4.2. Tétel.** Egy négyzetes mátrixnak akkor és csak akkor van inverze, ha
`|A| ≠ 0`. -/
theorem inverze_letezik_iff (A : Matrix' T (n + 1) (n + 1)) :
    (∃ X, Inverze A X) ↔ det' A ≠ 0 :=
  ⟨fun ⟨_, hX⟩ => det_ne_zero_of_inverze hX, fun h => ⟨_, inverze_of_det_ne_zero h⟩⟩

/-- **4.2. Tétel.** `(A⁻¹)⁻¹ = A`: ha `X` az `A` inverze, akkor `A` az `X` inverze. -/
theorem inverz_inverze {A X : Matrix' T n n} (h : Inverze A X) : Inverze X A :=
  ⟨h.2, h.1⟩

/-- **4.2. Tétel.** `(AB)⁻¹ = B⁻¹A⁻¹`.

*Bizonyítás (a jegyzet szerint).* `(AB)(B⁻¹A⁻¹) = A(BB⁻¹)A⁻¹ = AA⁻¹ = E`, és hasonlóan
`(B⁻¹A⁻¹)(AB) = E`; az inverz egyértelműsége miatt tehát `(AB)⁻¹ = B⁻¹A⁻¹`. -/
theorem inverz_szorzat {A B X Y : Matrix' T n n} (hA : Inverze A X) (hB : Inverze B Y) :
    Inverze (A * B) (Y * X) := by
  constructor
  · calc (Y * X) * (A * B) = Y * ((X * A) * B) := by
          simp [Matrix.mul_assoc]
      _ = Y * B := by rw [hA.1, Matrix.one_mul]
      _ = 1 := hB.1
  · calc (A * B) * (Y * X) = A * ((B * Y) * X) := by
          simp [Matrix.mul_assoc]
      _ = A * X := by rw [hB.2, Matrix.one_mul]
      _ = 1 := hA.2

/-- **4.2. Tétel.** `(Aᵀ)⁻¹ = (A⁻¹)ᵀ`.

*Bizonyítás (a jegyzet szerint).* `Aᵀ(A⁻¹)ᵀ = (A⁻¹A)ᵀ = Eᵀ = E`, és hasonlóan
`(A⁻¹)ᵀAᵀ = E`. -/
theorem inverz_transzponalt {A X : Matrix' T n n} (h : Inverze A X) : Inverze Aᵀ Xᵀ := by
  constructor
  · rw [← Matrix.transpose_mul, h.2, Matrix.transpose_one]
  · rw [← Matrix.transpose_mul, h.1, Matrix.transpose_one]

/-! ## 4.3. Definíció: elfajuló és nemelfajuló mátrix -/

/-- **4.3. Definíció.** Az `A` négyzetes mátrix *elfajuló*, ha `|A| = 0`. -/
def Elfajulo (A : Matrix' T n n) : Prop := det' A = 0

/-- **4.3. Definíció.** Az `A` négyzetes mátrix *nemelfajuló*, ha `|A| ≠ 0`. -/
def Nemelfajulo (A : Matrix' T n n) : Prop := det' A ≠ 0

/-! ## 4.4. Definíció: hasonló mátrixok -/

/-- **4.4. Definíció.** Az `A` és `B` mátrix *hasonló* (`A ≈ B`), ha van olyan `X`
nemelfajuló mátrix, hogy `B = X⁻¹AX`. -/
def Hasonlo (A B : Matrix' T n n) : Prop :=
  ∃ X Y : Matrix' T n n, Inverze X Y ∧ B = Y * A * X

/-! ## 4.5. Tétel -/

/-- **4.5. Tétel (reflexivitás).** `A ≈ A`, hiszen `A = E⁻¹AE`. -/
theorem hasonlo_refl (A : Matrix' T n n) : Hasonlo A A :=
  ⟨1, 1, ⟨Matrix.one_mul 1, Matrix.one_mul 1⟩, by simp⟩

/-- **4.5. Tétel (szimmetria).** Ha `A ≈ B`, azaz `B = X⁻¹AX`, akkor
`A = XBX⁻¹ = (X⁻¹)⁻¹B X⁻¹`, tehát `B ≈ A`. -/
theorem hasonlo_symm {A B : Matrix' T n n} (h : Hasonlo A B) : Hasonlo B A := by
  obtain ⟨X, Y, hXY, hB⟩ := h
  refine ⟨Y, X, inverz_inverze hXY, ?_⟩
  rw [hB]
  calc A = (A * X) * Y := by rw [Matrix.mul_assoc, hXY.2, Matrix.mul_one]
    _ = (1 * A * X) * Y := by rw [Matrix.one_mul]
    _ = ((X * Y) * A * X) * Y := by rw [hXY.2]
    _ = X * (Y * A * X) * Y := by simp [Matrix.mul_assoc]

/-- **4.5. Tétel (tranzitivitás).** Ha `B = X⁻¹AX` és `C = Y⁻¹BY`, akkor
`C = (XY)⁻¹A(XY)`, tehát `A ≈ C`. -/
theorem hasonlo_trans {A B C : Matrix' T n n} (hAB : Hasonlo A B) (hBC : Hasonlo B C) :
    Hasonlo A C := by
  obtain ⟨X, X', hX, hB⟩ := hAB
  obtain ⟨Y, Y', hY, hC⟩ := hBC
  refine ⟨X * Y, Y' * X', inverz_szorzat hX hY, ?_⟩
  rw [hC, hB]
  simp [Matrix.mul_assoc]

/-- **4.5. Tétel.** Hasonló mátrixok determinánsa megegyezik.

*Bizonyítás (a jegyzet szerint).* A determinánsok szorzástétele szerint
`|B| = |X⁻¹AX| = |X⁻¹|·|A|·|X| = |A|·(|X⁻¹|·|X|) = |A|·|E| = |A|`. -/
theorem hasonlo_det {A B : Matrix' T n n} (h : Hasonlo A B) : det' B = det' A := by
  obtain ⟨X, Y, hXY, hB⟩ := h
  have hXY' : det' Y * det' X = 1 := by
    rw [det'_eq_det, det'_eq_det, ← Matrix.det_mul, hXY.1, Matrix.det_one]
  rw [hB, det'_eq_det, det'_eq_det, Matrix.det_mul, Matrix.det_mul]
  rw [det'_eq_det, det'_eq_det] at hXY'
  calc Y.det * A.det * X.det = A.det * (Y.det * X.det) := by ring
    _ = A.det := by rw [hXY', mul_one]

end Ch04
end SzaboLinAlg
