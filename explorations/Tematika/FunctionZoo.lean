import Mathlib
import Atlas.Relation.Slope
import Genesis.Statement.Defs

/-!
# Tematika 04 — "Polinomok, racionális törtfüggvények, gyökös, trigonometrikus,
exponenciális függvények és inverzeik"

**Syllabus item.**  *Polinomok, racionális törtfüggvények, gyökös,
trigonometrikus, exponenciális függvények és inverzeik.*

**Categorical reading.**  Calculus I's zoo of elementary functions is a list of
*representable* constructions, each one determined by a universal property or a
functional equation rather than by a formula; transporting the functional
equation along a change of ground object gives the library's zoo:

| Calculus I | functional equation / universal property | library |
| :-- | :-- | :-- |
| polynomials | the free commutative `ℝ`-algebra on one generator | the Kasami monomial `x ↦ x ^ (4^k − 2^k + 1)` |
| rational functions | the localisation at the nonvanishing locus | the slope `(x + z)/(y + z)`, defined off `y = z` |
| `exp` | `f (x + y) = f x · f y` | the additive characters `ψ : K → ℂˣ` |
| `cos (n θ)` | `T_n (cos θ) = cos (n θ)` | the Dickson polynomials, `D_n (x + x⁻¹) = xⁿ + x⁻ⁿ` |
| `√` | inverse of `x ↦ x²` | the inverse Frobenius, an *automorphism* here |

The exponential row is the sharpest: over `ℝ` and over `K` the object is the
same, a **group homomorphism out of the additive group**, i.e. a functor
between one-object groupoids — the library's whole Fourier half is built from
`AddChar K ℂ`, and `Real.exp_add` and `AddChar.map_add_eq_mul` are the same
statement.

The trigonometric row is an equality of *polynomials*: the Dickson polynomials
the library uses (`Genesis/Dickson/`) are, after the substitution
`x = 2 cos θ`, exactly the Chebyshev multiple-angle polynomials of Calculus I
(`Tematika.FunctionZoo.dickson_eval_two_cos`), while over a finite field the
same polynomial computes power sums `xⁿ + x⁻ⁿ`
(`Tematika.FunctionZoo.dickson_eval_add_inv`).  One polynomial identity, two
readings; the change of context is `x + x⁻¹ ↦ 2 cos θ`, i.e. the parametrisation
of the norm-one torus.
-/

namespace Tematika.FunctionZoo

open Polynomial

/-! ### Exponenciális függvény: the functional equation is the object -/

/-- Calculus I: the exponential is a homomorphism from `(ℝ, +)` to `(ℝ, ·)`. -/
theorem real_exp_hom (x y : ℝ) : Real.exp (x + y) = Real.exp x * Real.exp y :=
  Real.exp_add x y

/-- The library: an additive character is a homomorphism from `(K, +)` to
`(ℂ, ·)` — the same functor between one-object groupoids, with a different
source. -/
theorem addChar_hom {K : Type*} [AddGroup K] (ψ : AddChar K ℂ) (x y : K) :
    ψ (x + y) = ψ x * ψ y :=
  ψ.map_add_eq_mul x y

/-- Inverse of the exponential over `ℝ`. -/
theorem real_log_exp (x : ℝ) : Real.log (Real.exp x) = x := Real.log_exp x

/-! ### Trigonometrikus függvények: Dickson = Chebyshev = multiple angle -/

/-- **Calculus I reading.**  Under `x = 2 cos θ` the Dickson polynomial used by
the library is the multiple-angle polynomial: `D_n (2 cos θ) = 2 cos (n θ)`. -/
theorem dickson_eval_two_cos (n : ℕ) (t : ℝ) :
    (dickson 1 1 n).eval (2 * Real.cos t) = 2 * Real.cos (n * t) := by
  rw [dickson_one_one_eq_chebyshev_T ℝ n]
  simp [Chebyshev.T_real_cos]

/-- **Library reading.**  The same polynomial over any commutative ring computes
power sums on the "unit circle" `x · y = 1`. -/
theorem dickson_eval_add_inv {R : Type*} [CommRing R] (x y : R) (h : x * y = 1) (n : ℕ) :
    (dickson 1 1 n).eval (x + y) = x ^ n + y ^ n :=
  dickson_one_one_eval_add_inv x y h n

/-! ### Gyökös függvények: the square root is an automorphism here -/

/-- **Gyökös függvény, characteristic two.**  Over `ℝ` the square root is a
partial inverse of a two-to-one map; over a finite field of characteristic two
squaring is *bijective*, so the square root is a genuine automorphism — the
inverse Frobenius. -/
theorem sq_inverseFrobenius {K : Type*} [Field K] [Fintype K] [CharP K 2] (x : K) :
    ((frobeniusEquiv K 2).symm x) ^ 2 = x := by
  simp [← frobenius_def]

/-- and it is a two-sided inverse. -/
theorem inverseFrobenius_sq {K : Type*} [Field K] [Fintype K] [CharP K 2] (x : K) :
    (frobeniusEquiv K 2).symm (x ^ 2) = x := by
  have h : (frobeniusEquiv K 2) x = x ^ 2 := by simp [frobeniusEquiv, frobenius_def]
  rw [← h]
  exact (frobeniusEquiv K 2).symm_apply_apply x

/-! ### Polinomok és racionális törtfüggvények -/

/-- **Polinom.**  The library's basic function is a monomial: the Kasami power
map, of exponent `4^k − 2^k + 1`. -/
theorem kasamiExponent_def (k : ℕ) : Genesis.Kasami.kasamiExponent k = 4 ^ k - 2 ^ k + 1 := rfl

/-- **Racionális törtfüggvény és értelmezési tartománya.**  The admissible
slopes are the points where the anharmonic rational functions `ρ ↦ ρ⁻¹` and
`ρ ↦ 1 + ρ` are all defined: `ρ ∉ {0, 1}`. -/
theorem admissible_iff {K : Type*} [Field K] (ρ : K) :
    Atlas.Admissible ρ ↔ ρ ≠ 0 ∧ ρ ≠ 1 := Iff.rfl

end Tematika.FunctionZoo
