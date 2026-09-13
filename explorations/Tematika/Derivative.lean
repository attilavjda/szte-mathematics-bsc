import Mathlib
import Atlas.Relation.SlopeFibre
import Atlas.HalfSet.Fibration
import Genesis.Statement.Defs

/-!
# Tematika 09 — "Pontbeli derivált és érintőegyenes", "deriválási szabályok",
"láncszabály, implicit deriválás", "elemi függvények deriváltja"

**Syllabus items.**  *Pontbeli derivált és érintőegyenes.  Kapcsolat a
folytonossággal, deriválási szabályok.  Elemi függvények deriváltja.
Láncszabály, implicit deriválás.*

**Categorical reading.**  The derivative is not a limit here but the same
*functor* read in a different site.  On a commutative ring `K` the operator

`D_a f := (x ↦ f (x + a) − f x)`

is the difference of `f` with its translate, i.e. `D_a = T_a^* − id` where
`T_a^*` is the pullback along translation by `a`; translations form a group
acting on the ring of functions, so `a ↦ T_a^*` is a functor from the
one-object groupoid `(K, +)` to `End(K → K)` and `D` is the *deviation of that
functor from the constant one*.  Over `ℝ` one further divides by `a` and takes
the colimit `a → 0`; over a finite field there is no such colimit, and the
difference operator *is* the derivative.  Everything Calculus I proves about
`d/dx` that does not use the limit holds verbatim:

* linearity (`diff_add`), the Leibniz rule (`diff_mul`), the chain rule
  (`diff_comp`), and Clairaut/Schwarz symmetry of mixed second derivatives
  (`diff_diff_comm`);
* "the derivative of a linear function is its slope" (`diff_addMonoidHom`), the
  characteristic-two computation `D_a (x ↦ x²) = a²` (`diff_sq`).

**Where the library uses it.**  The set `Δ` the whole proof is about is the
image of a derivative: `Genesis.Kasami.kasamiDerivative` is `D_1` of the Kasami
power map, normalised by its value at `0`
(`Tematika.Derivative.kasamiDerivative_eq_diff`).  The half-size input to the
counting argument is a *second derivative* statement: `D_t D_1 F = 0` says the
first derivative is invariant under translation by `t`, and together with "no
further coincidences" this makes `D_1 F` two-to-one and its image exactly half
of `K` (`Tematika.Derivative.isHalf_image_of_secondDiff_vanishing`, which is
`Atlas.isHalf_image_of_kernel_pair` read as a second-derivative test).

**Érintőegyenes.**  The tangent line is the first-order Taylor datum, and
"tangency = double contact" is an algebraic identity, not a limit: `a` is a
double root of `P` exactly when `P` and its formal derivative vanish at `a`
(`Tematika.Derivative.sq_X_sub_C_dvd_iff`).  This is the form of the tangent
line used in the library's curve half, where the group law is defined by
secant-and-tangent and the tangent case is detected by a vanishing denominator
(`Genesis/Curve/SecantSlopeXCoordinate.lean`,
`Genesis/Curve/VanishingNonvanishingHessianDenominators.lean`) — that vanishing
denominator is precisely "implicit deriválás" giving a vertical tangent.

**Difference quotient.**  The library's slope `Atlas.slopeOfTriple x y z`
*is* Calculus I's difference quotient `(x − z)/(y − z)`
(`Tematika.Derivative.slopeOfTriple_eq_difference_quotient`), and its
degenerate case `y = z` — where the quotient reads `0/0` and Calculus I passes
to the derivative — is the case the library treats separately
(`Atlas.mem_solutions_slope_iff_of_eq`).
-/

namespace Tematika.Derivative

open Polynomial

section Ring

variable {K : Type*} [CommRing K]

/-- **The discrete derivative** in direction `a`: `D_a f (x) = f (x + a) − f x`. -/
def diff (f : K → K) (a : K) : K → K := fun x => f (x + a) - f x

@[simp] theorem diff_apply (f : K → K) (a x : K) : diff f a x = f (x + a) - f x := rfl

/-- `D_a` is additive in the function: the derivative of a sum is the sum of the
derivatives. -/
theorem diff_add (f g : K → K) (a : K) :
    diff (fun y => f y + g y) a = fun x => diff f a x + diff g a x := by
  funext x; simp [diff]; ring

/-- `D_a` kills constants. -/
@[simp] theorem diff_const (c a : K) : diff (fun _ => c) a = fun _ => 0 := by
  funext x; simp [diff]

/-- **Leibniz rule.**  The discrete product rule; over `ℝ` the first factor
`f (x + a)` becomes `f x` in the limit `a → 0`. -/
theorem diff_mul (f g : K → K) (a x : K) :
    diff (fun y => f y * g y) a x = f (x + a) * diff g a x + diff f a x * g x := by
  simp [diff]; ring

/-- **Láncszabály (chain rule).**  The derivative of a composite is the
derivative of the outer function *in the direction given by the derivative of
the inner one*, evaluated at the inner value.  Over `ℝ`, after dividing by `a`,
this is `(g ∘ f)' = (g' ∘ f) · f'`. -/
theorem diff_comp (f g : K → K) (a x : K) :
    diff (g ∘ f) a x = diff g (diff f a x) (f x) := by
  simp [diff]

/-- **Clairaut/Schwarz: mixed second derivatives commute.** -/
theorem diff_diff_comm (f : K → K) (a b : K) (x : K) :
    diff (diff f a) b x = diff (diff f b) a x := by
  simp [diff]
  ring_nf

/-- "The derivative of a linear function is its slope": for an additive map the
difference quotient is constant, equal to the value at the direction. -/
theorem diff_addMonoidHom (g : K →+ K) (a x : K) : diff (g : K → K) a x = g a := by
  simp [diff]

/-- **Elemi függvény deriváltja, characteristic two.**  `D_a (x ↦ x²) = a²`;
the squaring map is additive in characteristic two, so its derivative is
constant. -/
theorem diff_sq [CharP K 2] (a x : K) : diff (fun y => y ^ 2) a x = a ^ 2 := by
  have h : (x + a) ^ 2 = x ^ 2 + a ^ 2 := by
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    have : (x + a) ^ 2 = x ^ 2 + 2 * (x * a) + a ^ 2 := by ring
    rw [this, h2]
    ring
  rw [diff_apply, h, CharTwo.sub_eq_add, add_comm (x ^ 2) (a ^ 2), add_assoc,
    CharTwo.add_self_eq_zero, add_zero]

end Ring

section Tangent

variable {K : Type*} [CommRing K]

/-- **Érintőegyenes = double contact.**  `a` is a double root of `P` — that is,
the line through `(a, P a)` given by the first-order Taylor datum meets the
graph to second order — exactly when `P` and its formal derivative vanish at
`a`.  This is the limit-free form of "the tangent line is the best affine
approximation", and the criterion used in the curve half of the library. -/
theorem sq_X_sub_C_dvd_iff (P : K[X]) (a : K) :
    (X - C a) ^ 2 ∣ P ↔ P.eval a = 0 ∧ (Polynomial.derivative P).eval a = 0 := by
  rw [X_sub_C_pow_dvd_iff, ← taylor_apply, X_pow_dvd_iff]
  constructor
  · intro h
    exact ⟨by simpa using h 0 (by norm_num), by simpa using h 1 (by norm_num)⟩
  · rintro ⟨h0, h1⟩ i hi
    interval_cases i
    · simpa using h0
    · simpa using h1

end Tangent

section DifferenceQuotient

variable {K : Type*} [Field K]

/-- **The library's slope is Calculus I's difference quotient.**  In
characteristic two `Atlas.slopeOfTriple x y z = (x + z)/(y + z)` is literally
`(x − z)/(y − z)`: the slope of the secant through two points of the graph. -/
theorem slopeOfTriple_eq_difference_quotient [CharP K 2] (x y z : K) :
    Atlas.slopeOfTriple x y z = (x - z) / (y - z) := by
  simp [Atlas.slopeOfTriple, CharTwo.sub_eq_add]

end DifferenceQuotient

section SecondDerivative

variable {K : Type*} [AddCommGroup K] [Fintype K] [DecidableEq K]

/-- **The second derivative test behind the half-size step.**  If the first
derivative `g` is additive, its own derivative in direction `t` vanishes
(`D_t g = 0`, i.e. `g` is `t`-periodic) and it has no coincidences beyond that
period, then `g` is two-to-one and its image is exactly half of `K`.

This is `Atlas.isHalf_image_of_kernel_pair` read as a statement about second
derivatives; in the library it is what makes `Δ` a half set. -/
theorem isHalf_image_of_secondDiff_vanishing (g : K →+ K) {t : K} (ht : t ≠ 0)
    (hperiod : ∀ x, g (x + t) - g x = 0)
    (hpair : ∀ x y : K, g x = g y → (y = x ∨ y = x + t)) :
    Atlas.IsHalf (Finset.image (g : K → K) Finset.univ) := by
  refine Atlas.isHalf_image_of_kernel_pair g ht fun x y => ⟨hpair x y, ?_⟩
  rintro (rfl | rfl)
  · rfl
  · exact (sub_eq_zero.mp (hperiod x)).symm

end SecondDerivative

section Kasami

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

omit [Fintype K] [DecidableEq K] in
/-- **The set the whole proof is about is the image of a derivative.**  In
characteristic two the normalised Kasami derivative is `D_1` of the Kasami power
map, shifted by its value at `0`. -/
theorem kasamiDerivative_eq_diff [CharP K 2] (k : ℕ) (b : K) :
    Genesis.Kasami.kasamiDerivative k b
      = diff (fun y : K => y ^ Genesis.Kasami.kasamiExponent k) 1 b + 1 := by
  simp [Genesis.Kasami.kasamiDerivative, diff, CharTwo.sub_eq_add]

/-- **Értékkészlet of a derivative.**  `Δ` is, by definition, the range of the
derivative map. -/
theorem derivativeImage_eq_range (k : ℕ) :
    ((Genesis.Kasami.derivativeImage k K : Finset K) : Set K)
      = Set.range (Genesis.Kasami.kasamiDerivative k) := by
  simp [Genesis.Kasami.derivativeImage]

end Kasami

end Tematika.Derivative
