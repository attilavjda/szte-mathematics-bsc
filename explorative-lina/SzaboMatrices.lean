import Mathlib

/-!
# Szabó, §2: matrices, proved from scratch and read as circuit diagrams

This file formalises the whole of section 2 of L. Szabó, *Bevezetés a lineáris
algebrába*: definitions 2.1, 2.2, 2.4, 2.6 and theorems 2.3, 2.5, 2.7.

Everything is proved *by hand*, entry by entry, exactly as in the notes (and as
in an undergraduate exam): the only inputs are the ring axioms of the scalars
and the elementary rules for finite sums.  We deliberately do **not** invoke
Mathlib's `Matrix.mul_assoc` etc.; instead we prove our operations agree with
Mathlib's at the end of the file (`mmul_eq_hMul`, `mtrans_eq_transpose`), which
is what lets the rest of the project reuse the library.

## Diagrammatic reading

In graphical linear algebra a matrix `A : Mat T m n` is a *circuit* with `n`
dangling wires on the left and `m` on the right.  Then

* `mmul A B` is **plugging circuits together in series**;
* `madd A B` is **two circuits in parallel, with copy on the left and add on
  the right**;
* `smul l A` is a scalar box `l` in series with `A`;
* `mtrans A` is the circuit **reflected in a vertical mirror**;
* `E n` is a bundle of `n` plain wires.

Theorem 2.5 says series composition is associative and interacts correctly
with the copy/add structure; theorem 2.7 says mirroring reverses series
composition.  `guide.tex` draws all of these.
-/

namespace Szabo

open Finset Matrix

open scoped BigOperators

variable {T : Type*} [CommRing T]

/-- §2.1 Definíció.  An `m × n` matrix over `T`. -/
abbrev Mat (T : Type*) (m n : ℕ) := Matrix (Fin m) (Fin n) T

variable {m n s t : ℕ}

/-- §2.2 Definíció: addition of matrices, entrywise. -/
def madd (A B : Mat T m n) : Mat T m n := fun i j => A i j + B i j

/-- §2.2 Definíció: multiplication by a scalar, entrywise. -/
def smul (l : T) (A : Mat T m n) : Mat T m n := fun i j => l * A i j

/-- The zero matrix ("nullmátrix"). -/
def mzero : Mat T m n := fun _ _ => 0

/-- §2.4 Definíció: the product `AB`, `(AB)ᵢⱼ = ∑ₖ aᵢₖ bₖⱼ`. -/
def mmul (A : Mat T m n) (B : Mat T n s) : Mat T m s := fun i j => ∑ k, A i k * B k j

/-- §2.6 Definíció: the transpose `Aᵀ`. -/
def mtrans (A : Mat T m n) : Mat T n m := fun i j => A j i

/-- The `n × n` identity matrix `Eₙ` ("egységmátrix"). -/
def E (T : Type*) [CommRing T] (n : ℕ) : Mat T n n := fun i j => if i = j then 1 else 0

@[simp] theorem madd_apply (A B : Mat T m n) (i j) : madd A B i j = A i j + B i j := rfl
@[simp] theorem smul_apply (l : T) (A : Mat T m n) (i j) : smul l A i j = l * A i j := rfl
@[simp] theorem mzero_apply (i : Fin m) (j : Fin n) : (mzero : Mat T m n) i j = 0 := rfl
@[simp] theorem mmul_apply (A : Mat T m n) (B : Mat T n s) (i j) :
    mmul A B i j = ∑ k, A i k * B k j := rfl
omit [CommRing T] in
@[simp] theorem mtrans_apply (A : Mat T m n) (i j) : mtrans A i j = A j i := rfl
@[simp] theorem E_apply (i j : Fin n) : (E T n) i j = if i = j then 1 else 0 := rfl

/-! ## 2.3 Tétel

`Tᵐˣⁿ` is a `T`-module: addition is commutative and associative with unit the
zero matrix and inverse `(-1) • A`, and the two distributive laws and the
"associativity of scalars" hold. -/

/-- 2.3 Tétel (i): addition is commutative. -/
theorem madd_comm (A B : Mat T m n) : madd A B = madd B A := by
  funext i j; exact add_comm _ _

/-- 2.3 Tétel (ii): addition is associative. -/
theorem madd_assoc (A B C : Mat T m n) : madd (madd A B) C = madd A (madd B C) := by
  funext i j; exact add_assoc _ _ _

/-- 2.3 Tétel (iii): the zero matrix is a unit for addition. -/
theorem madd_zero (A : Mat T m n) : madd A mzero = A := by
  funext i j; exact add_zero _

/-- 2.3 Tétel (iv): `(-1)A` is an additive inverse of `A`. -/
theorem madd_neg (A : Mat T m n) : madd A (smul (-1) A) = mzero := by
  funext i j; simp

/-- 2.3 Tétel (v): `λ(A + B) = λA + λB`. -/
theorem smul_madd (l : T) (A B : Mat T m n) :
    smul l (madd A B) = madd (smul l A) (smul l B) := by
  funext i j; exact mul_add _ _ _

/-- 2.3 Tétel (vi): `(λ + μ)A = λA + μA`. -/
theorem add_smul_mat (l mu : T) (A : Mat T m n) :
    smul (l + mu) A = madd (smul l A) (smul mu A) := by
  funext i j; exact add_mul _ _ _

/-- 2.3 Tétel (vii): `(λμ)A = λ(μA)`. -/
theorem smul_smul_mat (l mu : T) (A : Mat T m n) :
    smul (l * mu) A = smul l (smul mu A) := by
  funext i j; exact mul_assoc _ _ _

/-! ## 2.5 Tétel

The four laws of matrix multiplication, proved exactly as in the notes by
computing the `(i,k)` entry of both sides. -/

/-- 2.5 Tétel (i): `λ(AB) = (λA)B`. -/
theorem smul_mmul (l : T) (A : Mat T m n) (B : Mat T n s) :
    smul l (mmul A B) = mmul (smul l A) B := by
  funext i k
  calc l * ∑ j, A i j * B j k = ∑ j, l * (A i j * B j k) := by rw [Finset.mul_sum]
    _ = ∑ j, (l * A i j) * B j k := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [mul_assoc]

/-- 2.5 Tétel (i'): `λ(AB) = A(λB)`. -/
theorem smul_mmul' (l : T) (A : Mat T m n) (B : Mat T n s) :
    smul l (mmul A B) = mmul A (smul l B) := by
  funext i k
  calc l * ∑ j, A i j * B j k = ∑ j, l * (A i j * B j k) := by rw [Finset.mul_sum]
    _ = ∑ j, A i j * (l * B j k) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        ring

/-- 2.5 Tétel (ii): matrix multiplication is associative,
`(AB)C = A(BC)`.  Diagrammatically: connecting three circuits in series does
not depend on the bracketing. -/
theorem mmul_assoc (A : Mat T m n) (B : Mat T n s) (C : Mat T s t) :
    mmul (mmul A B) C = mmul A (mmul B C) := by
  funext i l
  calc ∑ k, (∑ j, A i j * B j k) * C k l
      = ∑ k, ∑ j, (A i j * B j k) * C k l := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [Finset.sum_mul]
    _ = ∑ j, ∑ k, (A i j * B j k) * C k l := Finset.sum_comm
    _ = ∑ j, ∑ k, A i j * (B j k * C k l) := by
        refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
        rw [mul_assoc]
    _ = ∑ j, A i j * ∑ k, B j k * C k l := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.mul_sum]

/-- 2.5 Tétel (iii): `A(B + C) = AB + AC`. -/
theorem mmul_madd (A : Mat T m n) (B C : Mat T n s) :
    mmul A (madd B C) = madd (mmul A B) (mmul A C) := by
  funext i k
  calc ∑ j, A i j * (B j k + C j k)
      = ∑ j, (A i j * B j k + A i j * C j k) := by
        refine Finset.sum_congr rfl fun j _ => mul_add _ _ _
    _ = (∑ j, A i j * B j k) + ∑ j, A i j * C j k := Finset.sum_add_distrib

/-- 2.5 Tétel (iv): `(A + B)C = AC + BC`. -/
theorem madd_mmul (A B : Mat T m n) (C : Mat T n s) :
    mmul (madd A B) C = madd (mmul A C) (mmul B C) := by
  funext i k
  calc ∑ j, (A i j + B i j) * C j k
      = ∑ j, (A i j * C j k + B i j * C j k) := by
        refine Finset.sum_congr rfl fun j _ => add_mul _ _ _
    _ = (∑ j, A i j * C j k) + ∑ j, B i j * C j k := Finset.sum_add_distrib

/-- 2.5 Tétel (v): `Eₘ A = A`.  Diagrammatically: a bundle of plain wires in
front of a circuit changes nothing. -/
theorem E_mmul (A : Mat T m n) : mmul (E T m) A = A := by
  funext i j
  simp [mmul, E]

/-- 2.5 Tétel (v'): `A Eₙ = A`. -/
theorem mmul_E (A : Mat T m n) : mmul A (E T n) = A := by
  funext i j
  simp [mmul, E]

/-! ## 2.7 Tétel: the transpose -/

omit [CommRing T] in
/-- 2.7 Tétel (i): `(Aᵀ)ᵀ = A`.  Reflecting a circuit twice restores it. -/
theorem mtrans_mtrans (A : Mat T m n) : mtrans (mtrans A) = A := rfl

/-- 2.7 Tétel (ii): `(λA)ᵀ = λAᵀ`. -/
theorem mtrans_smul (l : T) (A : Mat T m n) : mtrans (smul l A) = smul l (mtrans A) := rfl

/-- 2.7 Tétel (iii): `(A + B)ᵀ = Aᵀ + Bᵀ`. -/
theorem mtrans_madd (A B : Mat T m n) : mtrans (madd A B) = madd (mtrans A) (mtrans B) := rfl

/-- 2.7 Tétel (iv): `(AB)ᵀ = BᵀAᵀ`.  Diagrammatically: reflecting a series
composite reverses the order of the factors. -/
theorem mtrans_mmul (A : Mat T m n) (B : Mat T n s) :
    mtrans (mmul A B) = mmul (mtrans B) (mtrans A) := by
  funext k i
  calc (∑ j, A i j * B j k) = ∑ j, B j k * A i j := by
        refine Finset.sum_congr rfl fun j _ => mul_comm _ _
    _ = ∑ j, mtrans B k j * mtrans A j i := rfl

/-- A matrix is symmetric if it equals its transpose; necessarily square. -/
def IsSymm (A : Mat T n n) : Prop := mtrans A = A

theorem isSymm_E : IsSymm (E T n) := by
  funext i j
  by_cases h : i = j <;> simp [mtrans, E, h, eq_comm]

/-! ## Agreement with Mathlib

The by-hand definitions above are the library's, so all later files may use
Mathlib's matrix API. -/

@[simp] theorem madd_eq_add (A B : Mat T m n) : madd A B = A + B := rfl
@[simp] theorem smul_eq_smul (l : T) (A : Mat T m n) : smul l A = l • A := rfl
@[simp] theorem mmul_eq_hMul (A : Mat T m n) (B : Mat T n s) : mmul A B = A * B := rfl
omit [CommRing T] in
@[simp] theorem mtrans_eq_transpose (A : Mat T m n) : mtrans A = Matrix.transpose A := rfl
@[simp] theorem E_eq_one : E T n = (1 : Mat T n n) := by
  funext i j
  by_cases h : i = j <;> simp [E, Matrix.one_apply, h]

end Szabo
