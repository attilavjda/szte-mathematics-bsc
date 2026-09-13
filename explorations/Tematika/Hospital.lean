import Mathlib
import Atlas.Relation.SlopeFibre

/-!
# Tematika 15 — "L'Hospital szabályok és alkalmazásaik"

**Syllabus item.**  *L'Hospital szabályok és alkalmazásaik.*

**Categorical reading.**  A `0/0` expression is a **quotient that is not
determined by its zeroth-order data**: the diagram whose colimit one wants is
constant-zero on both entries, so the answer must be read off the *next* layer
of the filtration — the first-order (derivative) data.  L'Hospital's rule is the
statement that passing to the associated graded piece is compatible with the
quotient.

Both halves of that description occur in the library.

* **The indeterminate form itself.**  The library's slope is a difference
  quotient (see `Tematika/Derivative.lean`), and on the degenerate locus
  `y = z` both its numerator and its denominator vanish.  There the relation
  does not determine the slope at all: *every* value of `ρ` satisfies it
  (`Tematika.Hospital.slope_indeterminate`) — this is `0/0` in its exact
  meaning, "every value is a candidate".  The library therefore does not divide
  there; it treats the degenerate locus by a separate lemma
  (`Atlas.mem_solutions_slope_iff_of_eq`), which is the counting analogue of
  "differentiate numerator and denominator".
* **The resolution by first-order data.**  In the counting argument each count
  is written as `N = c + Z/Q` with `Q = |K|` large: the leading term is `c` for
  every slope, so the zeroth-order data is indeterminate, and the whole content
  sits in the first-order term `Z`, recovered as the *rescaled difference*
  `(N − c)·Q = Z` (`Tematika.Hospital.first_order_term`).  Nonnegativity of that
  first-order term, with an average already equal to `c`, is what forces
  `Z = 0` (see `Tematika/Extrema.lean`) — the same "compare the derivatives"
  move.

For comparison, the genuine analytic rule is proved here in one classical
instance, `Tematika.Hospital.tendsto_sin_div_atZero`: `sin x / x → 1`, obtained
from Mathlib's L'Hospital theorem by differentiating numerator and denominator.
-/

namespace Tematika.Hospital

/-- **`0/0` means "every value is a candidate".**  On the degenerate locus, where
the difference quotient has vanishing numerator and denominator, *every* slope
satisfies the relation: the zeroth-order data determines nothing. -/
theorem slope_indeterminate {K : Type*} [Field K] (h2 : Atlas.IsTwoTorsion K) (y : K) (ρ : K) :
    ((y, y, y) : K × K × K) ∈ Atlas.solutions (M := K) 1 ρ (1 + ρ) :=
  (Atlas.mem_solutions_slope_iff_of_eq h2 y y ρ).mpr rfl

/-- **The first-order term.**  When the zeroth-order data is the same for every
member of the family, the content is the rescaled difference — the discrete
"derivative" that the library's positivity hypothesis is about. -/
theorem first_order_term {N Z c Q : ℝ} (hQ : Q ≠ 0) (h : N = c + Z / Q) : (N - c) * Q = Z := by
  rw [h, add_sub_cancel_left, div_mul_cancel₀ _ hQ]

/-- **The analytic rule, one instance.**  `sin x / x → 1` as `x → 0`, proved by
L'Hospital: both numerator and denominator tend to `0`, and the quotient of the
derivatives, `cos x / 1`, tends to `1`. -/
theorem tendsto_sin_div_atZero :
    Filter.Tendsto (fun x : ℝ => Real.sin x / x) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds 1) := by
  have hf : ∀ᶠ x : ℝ in nhds 0, DifferentiableAt ℝ Real.sin x :=
    Filter.Eventually.of_forall fun x => Real.differentiable_sin x
  have hg : ∀ᶠ x : ℝ in nhds 0, deriv (fun y : ℝ => y) x ≠ 0 := by
    filter_upwards with x
    simp
  have h1 : Filter.Tendsto Real.sin (nhds 0) (nhds 0) := by
    simpa using Real.continuous_sin.tendsto 0
  have h2 : Filter.Tendsto (fun x : ℝ => x) (nhds 0) (nhds 0) := by
    simpa using continuous_id.tendsto (0 : ℝ)
  have h3 : Filter.Tendsto (fun x : ℝ => deriv Real.sin x / deriv (fun y : ℝ => y) x)
      (nhds 0) (nhds 1) := by
    have hquot : (fun x : ℝ => deriv Real.sin x / deriv (fun y : ℝ => y) x)
        = fun x => Real.cos x := by
      funext x
      simp [Real.deriv_sin]
    rw [hquot]
    simpa using Real.continuous_cos.tendsto 0
  exact deriv.lhopital_zero_nhds hf hg h1 h2 h3

end Tematika.Hospital
