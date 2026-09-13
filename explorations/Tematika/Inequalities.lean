import Mathlib
import Atlas.Moment.Parseval

/-!
# Tematika 03 — "Nevezetes egyenlőtlenségek" (the classical inequalities)

**Syllabus item.**  *Nevezetes egyenlőtlenségek.*

**Categorical reading.**  An inequality `x ≤ y` is a **morphism in the poset
`ℝ`** viewed as a category; a chain of estimates is a composite, and a two-sided
estimate is an isomorphism, i.e. an equality.  The classical inequalities are
the shadows of two structures:

* *positivity of a quadratic form* — `0 ≤ ‖z‖²` — which gives AM–GM and
  Cauchy–Schwarz (`Tematika.Inequalities.two_mul_le_sq_add_sq`,
  `Tematika.Inequalities.cauchy_schwarz`);
* *the dagger structure of the space of functions* — the inner product and the
  adjoint — of which **Parseval's identity is the isometry statement**: the
  Fourier transform is a unitary up to the scalar `|K|`
  (`Tematika.Inequalities.parseval`).

**Where the library uses it.**  Exactly there.  The counting argument closes by
comparing a family of counts with their average, and the comparison is possible
because the correction term is a *nonnegative* quantity: a real part of a
product that positivity of the quadratic form makes nonnegative.  Parseval
(`Atlas.parseval`, `Atlas.parseval_indicator`) plays the role of "the total mass
is preserved", the same bookkeeping that in Calculus I lets one bound a sum by
its `ℓ²` norm; the triangle inequality is used for character sums in exactly the
form `‖∑ f‖ ≤ ∑ ‖f‖` (`Tematika.Inequalities.norm_sum_le'`).
-/

namespace Tematika.Inequalities

/-- **AM–GM, two variables**: the archetypal consequence of `0 ≤ (a − b)²`. -/
theorem two_mul_le_sq_add_sq (a b : ℝ) : 2 * (a * b) ≤ a ^ 2 + b ^ 2 := by
  nlinarith [sq_nonneg (a - b)]

/-- **Cauchy–Schwarz** for finite sums: positivity of the Gram quadratic form. -/
theorem cauchy_schwarz {ι : Type*} (s : Finset ι) (f g : ι → ℝ) :
    (∑ i ∈ s, f i * g i) ^ 2 ≤ (∑ i ∈ s, f i ^ 2) * ∑ i ∈ s, g i ^ 2 :=
  Finset.sum_mul_sq_le_sq_mul_sq s f g

/-- **Triangle inequality** for finite sums, the form used for character sums. -/
theorem norm_sum_le' {ι : Type*} (s : Finset ι) (f : ι → ℂ) :
    ‖∑ i ∈ s, f i‖ ≤ ∑ i ∈ s, ‖f i‖ :=
  norm_sum_le s f

/-- **Parseval: the transform is an isometry up to the factor `|K|`.**  This is
the library's form of "the classical inequality that is really an identity";
the estimates of the counting argument are all bookkeeping around it. -/
theorem parseval {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (ψ : AddChar K ℂ) (hψ : ψ.IsPrimitive) (f : K → ℂ) :
    ∑ a : K, Atlas.transform ψ f a * (starRingEnd ℂ) (Atlas.transform ψ f a)
      = (Fintype.card K : ℂ) * ∑ x : K, f x * (starRingEnd ℂ) (f x) :=
  Atlas.parseval ψ hψ f

end Tematika.Inequalities
