import Mathlib
import Atlas.Interface.Forcing
import Atlas.Interface.HalfSetTheorem

/-!
# Tematika 10–14 — "Középérték-tételek.  Monotonitás és derivált kapcsolata.
Lokális szélsőérték és derivált.  Konvexitás.  Grafikon vázolása."

**Syllabus items.**  *Középérték-tételek.  Monotonitás és derivált kapcsolata.
Lokális szélsőérték és derivált (első és második derivált teszt), intervallumon
vett szélsőértékek.  Konvexitás fogalma, kapcsolata a második deriválttal.
Függvények grafikonjának vázolása.*

**Categorical reading.**  An extremum is a **(co)limit in a poset**: `max` is a
colimit of the diagram of values, `min` a limit, and "the maximum is attained"
says the colimit is representable by an element of the diagram.  The whole
block — mean value theorem, first derivative test, second derivative test,
convexity — is one pattern:

> a **monotone functor** between posets whose two endpoint values agree is
> constant,

and the derivative hypotheses are just different ways of producing the
monotonicity.  The pattern itself is order-theoretic and context-free:
`Tematika.Extrema.const_of_monotoneOn_endpoints`.

* **Calculus I instance.**  Monotonicity comes from `f' ≥ 0` (this is the mean
  value theorem), and equal endpoints then force constancy:
  `Tematika.Extrema.const_of_deriv_nonneg_of_endpoints` — Rolle's theorem in
  the form "nonnegative derivative and no net increase ⇒ nothing happens".
* **Library instance.**  Monotonicity comes from the *nonnegativity of a
  square*: each slope count is `main term + (a nonnegative correction)/|K|`, and
  the average over all admissible slopes is exactly the main term.  The same
  order-theoretic pattern then forces every correction to vanish:
  `Tematika.Extrema.const_of_mean_of_ge` (the arithmetic heart of
  `Atlas.forcing_of_average_and_nonneg`), which is what
  `Atlas.slopeCount_eq_of_moment_nonneg` runs on.  **This is the step where the
  library's proof is a calculus argument**: an inequality plus an exactly
  matching average is an equality case, i.e. "the function attains its minimum
  everywhere, so its derivative vanishes everywhere".
* **Second derivative / convexity.**  The nonnegative correction is a
  *quadratic* quantity, `z ↦ (z · z̄).re = ‖z‖²`
  (`Tematika.Extrema.normSq_nonneg_re`), and `x ↦ x²` is the archetypal convex
  function (`Tematika.Extrema.convexOn_sq`).  Convexity from the second
  derivative over `ℝ` is `Tematika.Extrema.convexOn_of_deriv2_nonneg_real`;
  over the finite ground object the second derivative is the second difference
  (see `Tematika/Derivative.lean`), and the positivity it provides is the
  library's `0 ≤ (thirdMoment …).re` hypothesis.
* **Fermat's stationary point condition.**  Over `ℝ` a local maximum forces the
  derivative to vanish (`Tematika.Extrema.deriv_eq_zero_of_isLocalMax`).  Its
  library form is the second conclusion of the forcing lemma: at the equality
  case the correction — the analogue of the derivative — is exactly zero.
* **Grafikon vázolása** is then the assembled picture: domain, symmetry,
  monotonicity, extrema, convexity are collected into one description of the
  object.  The library's "sketch" is the statement that the slope-count function
  on the admissible slope line is *constant*, equal to `|K|²/8`.
-/

namespace Tematika.Extrema

/-! ### The order-theoretic pattern -/

/-- **The pattern.**  A monotone function on `[a, b]` with equal endpoint values
is constant: a monotone functor between posets that identifies the ends
identifies everything in between. -/
theorem const_of_monotoneOn_endpoints {a b : ℝ} (f : ℝ → ℝ) (hab : a ≤ b)
    (hmono : MonotoneOn f (Set.Icc a b)) (hend : f a = f b) :
    ∀ x ∈ Set.Icc a b, f x = f a := by
  intro x hx
  have h1 : f a ≤ f x := hmono (Set.left_mem_Icc.mpr hab) hx hx.1
  have h2 : f x ≤ f b := hmono hx (Set.right_mem_Icc.mpr hab) hx.2
  rw [← hend] at h2
  linarith

/-! ### Calculus I instance: the mean value theorem -/

/-- **Középérték-tétel, applied.**  A function with nonnegative derivative and
equal endpoint values is constant. -/
theorem const_of_deriv_nonneg_of_endpoints {a b : ℝ} {f : ℝ → ℝ} (hab : a ≤ b)
    (hc : ContinuousOn f (Set.Icc a b))
    (hd : DifferentiableOn ℝ f (interior (Set.Icc a b)))
    (hderiv : ∀ x ∈ interior (Set.Icc a b), 0 ≤ deriv f x)
    (hend : f a = f b) :
    ∀ x ∈ Set.Icc a b, f x = f a :=
  const_of_monotoneOn_endpoints f hab
    (monotoneOn_of_deriv_nonneg (convex_Icc a b) hc hd hderiv) hend

/-- **Fermat.**  At a local maximum the derivative vanishes. -/
theorem deriv_eq_zero_of_isLocalMax {f : ℝ → ℝ} {a : ℝ} (h : IsLocalMax f a) :
    deriv f a = 0 :=
  h.deriv_eq_zero

/-- **Second derivative test / convexity, over `ℝ`.** -/
theorem convexOn_of_deriv2_nonneg_real {D : Set ℝ} (hD : Convex ℝ D) {f : ℝ → ℝ}
    (hc : ContinuousOn f D) (hd : DifferentiableOn ℝ f (interior D))
    (hd2 : DifferentiableOn ℝ (deriv f) (interior D))
    (h2 : ∀ x ∈ interior D, 0 ≤ deriv^[2] f x) : ConvexOn ℝ D f :=
  convexOn_of_deriv2_nonneg hD hc hd hd2 h2

/-- The archetypal convex function, whose nonnegativity is the positivity input
of the library. -/
theorem convexOn_sq : ConvexOn ℝ Set.univ fun x : ℝ => x ^ 2 :=
  (Even.convexOn_pow (by norm_num)).subset (Set.subset_univ _) convex_univ

/-! ### Library instance: an inequality with a matching average -/

/-- **The discrete mean value / equality case.**  If every member of a finite
family is at least `c` and the total is exactly `s.card * c`, every member
equals `c`.  This is the arithmetic heart of `Atlas.forcing_of_average_and_nonneg`
and the exact analogue of "nonnegative derivative, no net increase ⇒ constant". -/
theorem const_of_mean_of_ge {ι : Type*} (s : Finset ι) (N : ι → ℝ) (c : ℝ)
    (hsum : ∑ i ∈ s, N i = (s.card : ℝ) * c) (hge : ∀ i ∈ s, c ≤ N i) :
    ∀ i ∈ s, N i = c := by
  have hZ : ∀ i ∈ s, 0 ≤ N i - c := fun i hi => sub_nonneg.mpr (hge i hi)
  have hsum' : ∑ i ∈ s, (N i - c) = 0 := by
    rw [Finset.sum_sub_distrib, hsum, Finset.sum_const, nsmul_eq_mul]
    ring
  intro i hi
  have := (Finset.sum_eq_zero_iff_of_nonneg hZ).1 hsum' i hi
  linarith

/-- **The library's equality case, as it is actually used.**  With a half set and
a nonnegative third moment at every admissible slope, every slope count equals
the mean `|K|² / 8` *and* the moment vanishes identically: the maximum and the
minimum coincide, so the "derivative" is zero everywhere. -/
theorem slopeCount_const_of_moment_nonneg {K : Type*} [Field K] [Fintype K] [DecidableEq K]
    (h2 : Atlas.IsTwoTorsion K) (ψ : AddChar K ℂ) (hψ : ψ.IsPrimitive) {Δ : Finset K}
    (hhalf : Atlas.IsHalf Δ) (hK : 2 < Fintype.card K)
    (hnonneg : ∀ ρ ∈ Atlas.slopeSet K,
      0 ≤ (Atlas.thirdMoment (Atlas.transform ψ (Atlas.indicator Δ)) ρ (1 + ρ)).re) :
    ∀ ρ ∈ Atlas.slopeSet K,
      (Atlas.slopeCount (↑Δ : Set K) ρ : ℝ) = (Fintype.card K : ℝ) ^ 2 / 8
        ∧ (Atlas.thirdMoment (Atlas.transform ψ (Atlas.indicator Δ)) ρ (1 + ρ)).re = 0 :=
  Atlas.slopeCount_eq_of_moment_nonneg h2 ψ hψ hhalf hK hnonneg

/-- **The positivity is a square.**  The nonnegative quantity fed into the
forcing step is of the form `‖z‖²` — the value of the archetypal convex
function. -/
theorem normSq_nonneg_re (z : ℂ) : 0 ≤ (z * (starRingEnd ℂ) z).re := by
  rw [Complex.mul_conj]
  simpa using Complex.normSq_nonneg z

end Tematika.Extrema
