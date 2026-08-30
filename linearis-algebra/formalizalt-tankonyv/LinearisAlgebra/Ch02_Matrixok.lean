import LinearisAlgebra.Ch01_Bevezetes

/-!
# Szabó László: Bevezetés a lineáris algebrába — 2. fejezet: Mátrixok

A jegyzet 2. fejezetének (4–8. oldal) formalizálása: mátrixok, mátrixműveletek és azok
algebrai szabályai, transzponált.

A jegyzet tetszőleges `T` számtest felett dolgozik (1.1. Definíció, lásd
`SzaboLinAlg.Ch01.Szamtest`); mivel minden felhasznált tulajdonság a testaxiómákból
következik, itt tetszőleges (kommutatív, egységelemes) `T` gyűrű, illetve test felett
dolgozunk.  Az `m × n`-es mátrixokat a Mathlib `Matrix (Fin m) (Fin n) T` típusával
azonosítjuk; az indexelés `0`-tól `m-1`-ig, illetve `0`-tól `n-1`-ig fut.
-/

namespace SzaboLinAlg
namespace Ch02

open scoped BigOperators
open Matrix

variable {T : Type*} [CommRing T] {m n s t : ℕ}

/-! ## 2.1. Definíció: mátrixok és nevezetes mátrixtípusok -/

/-- **2.1. Definíció.** A `T` feletti `m × n`-es mátrixok halmaza `Tᵐˣⁿ`. -/
abbrev Matrix' (T : Type*) (m n : ℕ) := Matrix (Fin m) (Fin n) T

/-- **2.1. Definíció.** Az `A` mátrix `i`-edik *sorvektora*. -/
def sorvektor (A : Matrix' T m n) (i : Fin m) : Matrix' T 1 n := fun _ j => A i j

/-- **2.1. Definíció.** Az `A` mátrix `j`-edik *oszlopvektora*. -/
def oszlopvektor (A : Matrix' T m n) (j : Fin n) : Matrix' T m 1 := fun i _ => A i j

/-- **2.1. Definíció.** *Nullmátrix*: minden eleme nulla. -/
def Nullmatrix (A : Matrix' T m n) : Prop := ∀ i j, A i j = 0

theorem nullmatrix_zero : Nullmatrix (0 : Matrix' T m n) := fun _ _ => rfl

/-- **2.1. Definíció.** *Diagonális mátrix*: minden főátlón kívüli eleme nulla. -/
def Diagonalis (A : Matrix' T n n) : Prop := ∀ i j, i ≠ j → A i j = 0

/-- **2.1. Definíció.** *Felső trianguláris mátrix*: a főátló alatt minden elem nulla. -/
def FelsoTrianguláris (A : Matrix' T n n) : Prop := ∀ i j, j < i → A i j = 0

/-- **2.1. Definíció.** *Alsó trianguláris mátrix*: a főátló felett minden elem nulla. -/
def AlsoTrianguláris (A : Matrix' T n n) : Prop := ∀ i j, i < j → A i j = 0

/-- **2.1. Definíció.** Az `n`-edrendű *egységmátrix* `Eₙ`: diagonális mátrix, melynek
főátlójában minden elem `1`. -/
theorem egysegmatrix_apply (i j : Fin n) :
    (1 : Matrix' T n n) i j = if i = j then 1 else 0 := by
  simp [Matrix.one_apply]

theorem egysegmatrix_diagonalis : Diagonalis (1 : Matrix' T n n) := fun i j hij => by
  simp [hij]

/-- Egy mátrix pontosan akkor diagonális, ha egyszerre felső és alsó trianguláris. -/
theorem diagonalis_iff (A : Matrix' T n n) :
    Diagonalis A ↔ FelsoTrianguláris A ∧ AlsoTrianguláris A := by
  constructor
  · intro h
    exact ⟨fun i j hij => h i j (fun he => absurd he (Fin.ne_of_gt hij)),
      fun i j hij => h i j (Fin.ne_of_lt hij)⟩
  · rintro ⟨hf, ha⟩ i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact ha i j h
    · exact hf i j h

/-! ## 2.2. Definíció: összeadás és skalárral való szorzás -/

/-- **2.2. Definíció.** Mátrixok összeadása elemenként történik. -/
theorem osszeadas_apply (A B : Matrix' T m n) (i j) : (A + B) i j = A i j + B i j := rfl

/-- **2.2. Definíció.** Skalárral való szorzás elemenként történik. -/
theorem skalarszoros_apply (lam : T) (A : Matrix' T m n) (i j) :
    (lam • A) i j = lam * A i j := rfl

/-! ## 2.3. Tétel: az összeadás és a skalárral való szorzás tulajdonságai -/

/-- **2.3. Tétel.** A mátrixösszeadás kommutatív. -/
theorem osszeadas_kommutativ (A B : Matrix' T m n) : A + B = B + A := by
  ext i j; exact add_comm _ _

/-- **2.3. Tétel.** A mátrixösszeadás asszociatív. -/
theorem osszeadas_asszociativ (A B C : Matrix' T m n) : (A + B) + C = A + (B + C) := by
  ext i j; exact add_assoc _ _ _

/-- **2.3. Tétel.** A nullmátrix az összeadás egységeleme: `A + 0 = A`. -/
theorem osszeadas_nullmatrix (A : Matrix' T m n) : A + 0 = A := by
  ext i j; exact add_zero _

/-- **2.3. Tétel.** Minden `A` mátrixnak a `-A = (-1)A` mátrix additív inverze. -/
theorem additiv_inverz (A : Matrix' T m n) : A + (-1 : T) • A = 0 := by
  ext i j
  simp [Matrix.add_apply]

/-- **2.3. Tétel.** `λ(A + B) = λA + λB`. -/
theorem skalar_disztributiv_matrix (lam : T) (A B : Matrix' T m n) :
    lam • (A + B) = lam • A + lam • B := by
  ext i j; exact mul_add _ _ _

/-- **2.3. Tétel.** `(λ + μ)A = λA + μA`. -/
theorem skalar_disztributiv_skalar (lam mu : T) (A : Matrix' T m n) :
    (lam + mu) • A = lam • A + mu • A := by
  ext i j; exact add_mul _ _ _

/-- **2.3. Tétel.** `(λμ)A = λ(μA)`. -/
theorem skalar_asszociativ (lam mu : T) (A : Matrix' T m n) :
    (lam * mu) • A = lam • (mu • A) := by
  ext i j; exact mul_assoc _ _ _

/-! ## 2.4. Definíció: mátrixok szorzása -/

/-- **2.4. Definíció.** Ha `A` `m × n`-es és `B` `n × s`-es, akkor `AB` az az `m × s`-es
mátrix, melynek `(i,j)` eleme `∑ₖ aᵢₖbₖⱼ`. -/
theorem szorzat_apply (A : Matrix' T m n) (B : Matrix' T n s) (i : Fin m) (j : Fin s) :
    (A * B) i j = ∑ k : Fin n, A i k * B k j := by
  simp [Matrix.mul_apply]

/-! ## 2.5. Tétel: a szorzás tulajdonságai -/

/-- **2.5. Tétel.** `λ(AB) = (λA)B`.

*Bizonyítás (a jegyzet szerint, elemenként).*
`λ(AB)ᵢₖ = λ∑ⱼ aᵢⱼbⱼₖ = ∑ⱼ (λaᵢⱼ)bⱼₖ = ((λA)B)ᵢₖ`. -/
theorem skalar_szorzat_bal (lam : T) (A : Matrix' T m n) (B : Matrix' T n s) :
    lam • (A * B) = (lam • A) * B := by
  ext i k
  simp [Matrix.mul_apply, Finset.mul_sum, mul_assoc]

/-- **2.5. Tétel.** `λ(AB) = A(λB)`. -/
theorem skalar_szorzat_jobb (lam : T) (A : Matrix' T m n) (B : Matrix' T n s) :
    lam • (A * B) = A * (lam • B) := by
  ext i k
  simp only [Matrix.smul_apply, Matrix.mul_apply, Finset.mul_sum, smul_eq_mul]
  exact Finset.sum_congr rfl fun j _ => by ring

/-- **2.5. Tétel.** A mátrixszorzás asszociatív: `A(BC) = (AB)C`.

*Bizonyítás (a jegyzet szerint).* Kettős összegek felcserélésével:
`((AB)C)ᵢₗ = ∑ₖ (∑ⱼ aᵢⱼbⱼₖ) cₖₗ = ∑ⱼ aᵢⱼ (∑ₖ bⱼₖcₖₗ) = (A(BC))ᵢₗ`. -/
theorem szorzas_asszociativ (A : Matrix' T m n) (B : Matrix' T n s) (C : Matrix' T s t) :
    A * (B * C) = (A * B) * C := by
  ext i l
  simp only [Matrix.mul_apply, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => (mul_assoc _ _ _).symm

/-- **2.5. Tétel.** `A(B + C) = AB + AC`. -/
theorem szorzas_disztributiv_bal (A : Matrix' T m n) (B C : Matrix' T n s) :
    A * (B + C) = A * B + A * C := by
  ext i k
  simp only [Matrix.mul_apply, Matrix.add_apply, mul_add]
  rw [Finset.sum_add_distrib]

/-- **2.5. Tétel.** `(A + B)C = AC + BC`. -/
theorem szorzas_disztributiv_jobb (A B : Matrix' T m n) (C : Matrix' T n s) :
    (A + B) * C = A * C + B * C := by
  ext i k
  simp only [Matrix.mul_apply, Matrix.add_apply, add_mul]
  rw [Finset.sum_add_distrib]

/-- **2.5. Tétel.** `EₘA = AEₙ = A`. -/
theorem egysegmatrix_szorzas (A : Matrix' T m n) :
    (1 : Matrix' T m m) * A = A ∧ A * (1 : Matrix' T n n) = A :=
  ⟨Matrix.one_mul A, Matrix.mul_one A⟩

/-! ## 2.6. Definíció: transzponált -/

omit [CommRing T] in
/-- **2.6. Definíció.** Az `A = (aᵢⱼ)ₘₓₙ` mátrix *transzponáltja* az az `Aᵀ = (bᵢⱼ)ₙₓₘ`
mátrix, melyre `bᵢⱼ = aⱼᵢ`. -/
theorem transzponalt_apply (A : Matrix' T m n) (i : Fin n) (j : Fin m) :
    Aᵀ i j = A j i := rfl

/-- **2.6. Definíció.** `A` *szimmetrikus mátrix*, ha `A = Aᵀ`; ez szükségképpen
négyzetes mátrix. -/
def Szimmetrikus (A : Matrix' T n n) : Prop := Aᵀ = A

/-! ## 2.7. Tétel: a transzponálás tulajdonságai -/

omit [CommRing T] in
/-- **2.7. Tétel.** `(Aᵀ)ᵀ = A`. -/
theorem transzponalt_ketszer (A : Matrix' T m n) : (Aᵀ)ᵀ = A := rfl

/-- **2.7. Tétel.** `(λA)ᵀ = λAᵀ`. -/
theorem transzponalt_skalar (lam : T) (A : Matrix' T m n) : (lam • A)ᵀ = lam • Aᵀ := rfl

/-- **2.7. Tétel.** `(A + B)ᵀ = Aᵀ + Bᵀ`. -/
theorem transzponalt_osszeg (A B : Matrix' T m n) : (A + B)ᵀ = Aᵀ + Bᵀ := rfl

/-- **2.7. Tétel.** `(AB)ᵀ = BᵀAᵀ`.

*Bizonyítás (a jegyzet szerint).*
`((AB)ᵀ)ᵢₖ = (AB)ₖᵢ = ∑ⱼ aₖⱼbⱼᵢ = ∑ⱼ (Bᵀ)ᵢⱼ(Aᵀ)ⱼₖ = (BᵀAᵀ)ᵢₖ`. -/
theorem transzponalt_szorzat (A : Matrix' T m n) (B : Matrix' T n s) :
    (A * B)ᵀ = Bᵀ * Aᵀ := by
  ext i k
  simp only [Matrix.transpose_apply, Matrix.mul_apply]
  exact Finset.sum_congr rfl fun j _ => mul_comm _ _

end Ch02
end SzaboLinAlg
