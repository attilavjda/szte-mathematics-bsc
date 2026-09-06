/-
# Ten tiny LEGO blocks for a first calculus exam

Each block below is *one structural move*: a picture / a diagram / a logical step
that you can snap onto a problem before (or instead of) doing algebra.
Every block is stated once, in maximal generality, and then *clicked onto* the
running example

    fExam x = arctan (3 * (x³+1)^(-1/3)) + e^π

from `RequestProject/CalcExam.lean`.

The companion prose is `BLOCKS.md`; the drawings live there, the proofs live here.
-/
import Mathlib
import RequestProject.CalcExam

open Real Filter Topology Set

namespace CalcBlocks

/-!
## Block 1 — ARROW ▸ ARROW  (chain rule = functoriality of `D`)

Picture: `x —f→ • —g→ •`, and under it the linearised row `1 —u→ 1 —v→ 1`.
`D` is a functor, so a composite arrow maps to the composite of the labels, and
composing `1 × 1` matrices is *multiplying numbers*.  Never differentiate a
formula: draw the arrows, label them, multiply.
-/
theorem block_compose_arrows {f g : ℝ → ℝ} {x u v : ℝ}
    (hf : HasDerivAt f u x) (hg : HasDerivAt g v (f x)) :
    HasDerivAt (g ∘ f) (v * u) x :=
  hg.comp x hf

/-!
## Block 2 — TERMINAL ARROW  (constants are invisible to `D`)

Picture: a box with no wire coming in.  `e^π ≈ 23.14` is scary-looking and
contributes exactly nothing.  Cross it out *before* you start.
-/
theorem block_kill_constant (f : ℝ → ℝ) (c x : ℝ) :
    deriv (fun y => f y + c) x = deriv f x :=
  deriv_add_const c

/-- The same move applied to the exam function: the `e^π` summand is dead weight. -/
theorem exam_const_is_dead (x : ℝ) :
    deriv fExam x = deriv (fun y => arctan (3 * (y ^ 3 + 1) ^ (-(1/3) : ℝ))) x :=
  block_kill_constant _ (Real.exp π) x

/-!
## Block 3 — SCALARS SLIDE  (`D` is linear, so numbers walk through it)

Picture: a wire with a bead `c` on it; the bead slides past the `D` box.
-/
theorem block_scalar_slides {f : ℝ → ℝ} {x u : ℝ} (c : ℝ) (hf : HasDerivAt f u x) :
    HasDerivAt (fun y => c * f y) (c * u) x :=
  hf.const_mul c

/-!
## Block 4 — ISO ▸ ISO  (an invertible arrow has an invertible label)

If `g` undoes `f`, then along the bottom row the labels must multiply to `1`.
This is how you *recall* `(arctan)' = 1/(1+x²)` from `(tan)' = 1+tan²` under exam
stress, and how you get any inverse-function derivative with no algebra at all.
-/
theorem block_inverse_labels {f g : ℝ → ℝ} {x u v : ℝ}
    (hf : HasDerivAt f u x) (hg : HasDerivAt g v (f x)) (hgf : ∀ y, g (f y) = y) :
    v * u = 1 := by
  have h1 : HasDerivAt (g ∘ f) (v * u) x := hg.comp x hf
  have h2 : HasDerivAt (g ∘ f) 1 x := by
    have : (g ∘ f) = fun y => y := funext hgf
    rw [this]
    exact hasDerivAt_id x
  exact h1.unique h2

/-!
## Block 5 — SIGN ▸ ORDER  (the sign of the label is a functor to `≤`)

You almost never need the value of `f′`; you need its *sign*.  A negative label
on a connected piece turns into "the graph goes down there", i.e. strict
antitonicity — and then injectivity, at most one root, etc., all for free.
-/
theorem block_sign_to_order {f : ℝ → ℝ} {D : Set ℝ} (hD : Convex ℝ D)
    (hc : ContinuousOn f D) (h : ∀ x ∈ interior D, deriv f x < 0) :
    StrictAntiOn f D :=
  strictAntiOn_of_deriv_neg hD hc h

/-- Clicked onto the exam function: it is strictly decreasing on `[0, ∞)`,
read straight off the single minus sign in the diagram. -/
theorem exam_strictAntiOn : StrictAntiOn fExam (Ici 0) := by
  refine block_sign_to_order (convex_Ici 0) ?_ ?_
  · intro x hx0
    have hx0' : (0:ℝ) ≤ x := hx0
    have hx : 0 < x ^ 3 + 1 := by positivity
    exact (hasDerivAt_fExam hx).continuousAt.continuousWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    exact deriv_fExam_neg hx

/-- …and therefore injective there: no algebra, just the picture of a falling graph. -/
theorem exam_injOn : InjOn fExam (Ici 0) := exam_strictAntiOn.injOn

/-!
## Block 6 — SYMMETRY  (a symmetry of the picture is a symmetry of the answer)

Fold the paper along the `y`-axis.  If `f` is even, `f′` is odd (and vice versa).
Half of every symmetric problem is already done; also a free sanity check on any
derivative you computed.
-/
theorem block_even_deriv_odd {f : ℝ → ℝ} (hf : ∀ x, f (-x) = f x) (x : ℝ) :
    deriv f (-x) = -deriv f x := by
  have h : deriv (fun y => f (-y)) x = deriv f x := by
    simp only [hf]
  rw [deriv_comp_neg] at h
  linarith

theorem block_odd_deriv_even {f : ℝ → ℝ} (hf : ∀ x, f (-x) = -f x) (x : ℝ) :
    deriv f (-x) = deriv f x := by
  have h : deriv (fun y => f (-y)) x = deriv (fun y => -f y) x := by
    simp only [hf]
  rw [deriv_comp_neg, deriv.fun_neg] at h
  linarith

/-!
## Block 7 — ZERO LABEL ▸ ONE POINT  (identities without algebra)

To prove `F = G` do **not** expand: check `F′ = G′` and check one value.
A connected domain plus a vanishing derivative means the arrow factors through
the one-point space.  This is *the* trick for arctan/log identities.
-/
theorem block_identity_by_deriv {F G : ℝ → ℝ}
    (hF : Differentiable ℝ F) (hG : Differentiable ℝ G)
    (hd : ∀ x, deriv F x = deriv G x) {x₀ : ℝ} (h₀ : F x₀ = G x₀) (x : ℝ) :
    F x = G x := by
  have hdiff : Differentiable ℝ (fun y => F y - G y) := hF.sub hG
  have hz : ∀ y, deriv (fun y => F y - G y) y = 0 := by
    intro y
    rw [deriv_fun_sub (hF y) (hG y), hd y, sub_self]
  have := is_const_of_deriv_eq_zero hdiff hz x x₀
  simp only at this
  linarith [this, h₀]

/-- A textbook payoff of Block 7 (here Mathlib already knows the identity):
`arctan x + arctan (1/x) = π/2` for `x > 0` — both sides have derivative
`1/(1+x²) − 1/(1+x²) = 0`, and at `x = 1` both are `π/2`. -/
theorem arctan_add_arctan_inv {x : ℝ} (hx : 0 < x) :
    arctan x + arctan x⁻¹ = π / 2 := by
  rw [Real.arctan_inv_of_pos hx]; ring

/-!
## Block 8 — CODOMAIN ▸ BOUND  (read the target object, not the formula)

`arctan` lands in `(−π/2, π/2)` whatever you feed it.  So anything of the shape
`arctan (mess) + c` is trapped in a horizontal strip: boundedness, asymptotes and
"can this equation have a solution?" are answered by the *type* of the arrow.
-/
theorem block_codomain_bound (u c : ℝ) :
    |arctan u + c - c| < π / 2 := by
  have h₁ := Real.arctan_lt_pi_div_two u
  have h₂ := Real.neg_pi_div_two_lt_arctan u
  rw [abs_lt]
  constructor <;> linarith

/-- The exam function never leaves the strip `e^π ± π/2`; in particular it is
bounded, and `fExam x = 0` has no solution. -/
theorem exam_in_strip (x : ℝ) : |fExam x - Real.exp π| < π / 2 :=
  block_codomain_bound _ _

theorem exam_ne_zero (x : ℝ) : fExam x ≠ 0 := by
  have hstrip := exam_in_strip x
  rw [abs_lt] at hstrip
  have hpi : 3 < π := Real.pi_gt_three
  have hexp : π + 1 ≤ Real.exp π := Real.add_one_le_exp π
  intro h
  rw [h] at hstrip
  linarith

/-!
## Block 9 — LIMITS COMPOSE  (a limit is transported along a continuous arrow)

Same picture as Block 1, one level down: to find `lim f`, walk the chain of
arrows and push the limit through each one.  Continuity is exactly the licence
to move `lim` past an arrow.
-/
theorem block_push_limit {f g : ℝ → ℝ} {l : Filter ℝ} {a b : ℝ}
    (hf : Tendsto f l (𝓝 a)) (hg : ContinuousAt g a) (hb : g a = b) :
    Tendsto (g ∘ f) l (𝓝 b) := by
  rw [← hb]
  exact hg.tendsto.comp hf

/-- Walking the chain at `+∞`: `x³+1 → +∞`, so `(x³+1)^(−1/3) → 0`, so the
`arctan` argument `→ 0`, so `fExam x → e^π`.  The horizontal asymptote is read
off the diagram, not computed. -/
theorem exam_tendsto_atTop : Tendsto fExam atTop (𝓝 (Real.exp π)) := by
  have hcube : Tendsto (fun x : ℝ => x ^ 3 + 1) atTop atTop :=
    (tendsto_pow_atTop (by norm_num)).atTop_add tendsto_const_nhds
  have hrpow : Tendsto (fun x : ℝ => (x ^ 3 + 1) ^ (-(1/3) : ℝ)) atTop (𝓝 0) :=
    (tendsto_rpow_neg_atTop (y := (1/3 : ℝ)) (by norm_num)).comp hcube
  have hmul : Tendsto (fun x : ℝ => 3 * (x ^ 3 + 1) ^ (-(1/3) : ℝ)) atTop (𝓝 0) := by
    simpa using hrpow.const_mul (3 : ℝ)
  have harc : Tendsto (fun x : ℝ => arctan (3 * (x ^ 3 + 1) ^ (-(1/3) : ℝ))) atTop (𝓝 0) := by
    simpa using (Real.continuous_arctan.continuousAt (x := (0:ℝ))).tendsto.comp hmul
  simpa only [fExam, zero_add] using harc.add_const (Real.exp π)

/-!
## Block 10 — CONNECTEDNESS ▸ EXISTENCE  (solve nothing, still find a root)

The intermediate value theorem is the statement that a continuous arrow sends a
connected object to a connected object.  Two sample values of opposite side of
`y` and you own a solution — no formula for it, and none needed.
-/
theorem block_ivt {f : ℝ → ℝ} {a b y : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn f (Icc a b)) (hy : y ∈ Icc (f a) (f b)) :
    ∃ c ∈ Icc a b, f c = y := by
  obtain ⟨c, hc1, hc2⟩ := intermediate_value_Icc hab hc hy
  exact ⟨c, hc1, hc2⟩

/-- Same block, drawn for a *falling* graph (`f b ≤ y ≤ f a`). -/
theorem block_ivt_anti {f : ℝ → ℝ} {a b y : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn f (Icc a b)) (hy : y ∈ Icc (f b) (f a)) :
    ∃ c ∈ Icc a b, f c = y := by
  obtain ⟨c, hc1, hc2⟩ := intermediate_value_Icc' hab hc hy
  exact ⟨c, hc1, hc2⟩

/-- Two blocks snapped together (10 + 5): `fExam` is continuous and strictly
decreasing on `[0,1]`, hence it attains **every** value between `fExam 1` and
`fExam 0`, exactly once. -/
theorem exam_attains_between {y : ℝ} (hy : y ∈ Icc (fExam 1) (fExam 0)) :
    ∃! c, c ∈ Icc (0:ℝ) 1 ∧ fExam c = y := by
  have hcont : ContinuousOn fExam (Icc 0 1) := by
    intro x hx0
    have hx0' : (0:ℝ) ≤ x := hx0.1
    have hx : 0 < x ^ 3 + 1 := by positivity
    exact (hasDerivAt_fExam hx).continuousAt.continuousWithinAt
  obtain ⟨c, hc1, hc2⟩ := block_ivt_anti (by norm_num : (0:ℝ) ≤ 1) hcont hy
  refine ⟨c, ⟨hc1, hc2⟩, ?_⟩
  rintro d ⟨hd1, hd2⟩
  have hsub : Icc (0:ℝ) 1 ⊆ Ici 0 := Icc_subset_Ici_self
  exact exam_injOn (hsub hd1) (hsub hc1) (by rw [hd2, hc2])

end CalcBlocks
