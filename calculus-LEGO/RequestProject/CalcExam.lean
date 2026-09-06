/-
# A "categorical" pen-and-paper solution of one calculus exercise

    f(x) = arctan (3 / (x³+1)^(1/3)) + e^π

Read `f` as a *composite arrow* in the category of (pointed) differentiable maps,
and the derivative as a *functor* `D` sending an arrow to its linearisation:

      x  ──cube+1──▶  t  ──(·)^(-1/3)──▶  u  ──3·(−)──▶  v  ──arctan──▶  w  ──+e^π──▶ f(x)
      │               │                    │              │                │
   D  ▼               ▼                    ▼              ▼                ▼
      1 ──3x²──▶      1 ──(-1/3)t^(-4/3)──▶ 1 ──3·(−)──▶  1 ──1/(1+v²)──▶  1 ──id──▶ f'(x)

The chain rule is exactly functoriality, `D(g ∘ f) = D g ∘ D f`, so the answer is
the *composite of the labels* along the bottom row; the terminal `+ e^π` is a
constant arrow, whose linearisation is `0` — it never enters the product.

Everything below is that one composite, checked by Lean.
-/
import Mathlib

open Real

/-- The exam function, on the region where `x³+1 > 0` (so the cube root is honest).
`3 / (x³+1)^(1/3)` is written as `3 * (x³+1)^(-1/3)`. -/
noncomputable def fExam (x : ℝ) : ℝ := arctan (3 * (x ^ 3 + 1) ^ (-(1/3) : ℝ)) + Real.exp π

/-- Chain rule as functoriality: composing the labels
`3x²`, `(-1/3)t^(-4/3)`, `3·(−)`, `1/(1+v²)`, `+0` gives

  `f'(x) = -3x² / ( (x³+1)^(2/3) · ((x³+1)^(2/3) + 9) )`. -/
theorem hasDerivAt_fExam {x : ℝ} (hx : 0 < x ^ 3 + 1) :
    HasDerivAt fExam
      (-3 * x ^ 2 / ((x ^ 3 + 1) ^ ((2/3) : ℝ) * ((x ^ 3 + 1) ^ ((2/3) : ℝ) + 9))) x := by
  set t : ℝ := x ^ 3 + 1 with ht_def
  set a : ℝ := t ^ ((1/3) : ℝ) with ha_def
  have ha : 0 < a := Real.rpow_pos_of_pos hx _
  have h3a : a ^ 3 = t := by
    rw [ha_def, ← Real.rpow_natCast (t ^ ((1/3) : ℝ)) 3, ← Real.rpow_mul hx.le]
    norm_num
  have e1 : t ^ (-(1/3) : ℝ) = a⁻¹ := by rw [Real.rpow_neg hx.le, ha_def]
  have e2 : t ^ (-(1/3) - 1 : ℝ) = a⁻¹ * t⁻¹ := by
    rw [Real.rpow_sub hx, Real.rpow_one, e1]
    ring
  have e3 : t ^ ((2/3) : ℝ) = a ^ 2 := by
    rw [ha_def, ← Real.rpow_natCast (t ^ ((1/3) : ℝ)) 2, ← Real.rpow_mul hx.le]
    norm_num
  -- the arrows of the diagram, in order
  have h1 : HasDerivAt (fun y : ℝ => y ^ 3 + 1) (3 * x ^ 2) x := by
    simpa using ((hasDerivAt_pow 3 x).add_const 1)
  have h2 := (h1.rpow_const (p := -(1/3)) (Or.inl hx.ne')).const_mul (3 : ℝ)
  have h4 := (h2.arctan).add_const (Real.exp π)
  convert h4 using 1
  rw [e1, e2, e3, ← h3a]
  have ha0 : a ≠ 0 := ha.ne'
  field_simp
  ring

/-- The same statement phrased with `deriv`. -/
theorem deriv_fExam {x : ℝ} (hx : 0 < x ^ 3 + 1) :
    deriv fExam x =
      -3 * x ^ 2 / ((x ^ 3 + 1) ^ ((2/3) : ℝ) * ((x ^ 3 + 1) ^ ((2/3) : ℝ) + 9)) :=
  (hasDerivAt_fExam hx).deriv

/-- Sanity check that the constant `e^π` really is a "terminal object" for `D`:
it is killed by differentiation, i.e. `f` and `f - e^π` have the same derivative. -/
theorem deriv_const_exp_pi : deriv (fun _ : ℝ => Real.exp π) = 0 := by
  funext x
  simp

/-- Sign reading off the diagram: on `x > 0` the only negative label is `-1/3`,
so `f` is strictly decreasing there (derivative `< 0`). -/
theorem deriv_fExam_neg {x : ℝ} (hx : 0 < x) :
    deriv fExam x < 0 := by
  have ht : 0 < x ^ 3 + 1 := by positivity
  rw [deriv_fExam ht]
  have h1 : (0 : ℝ) < (x ^ 3 + 1) ^ ((2/3) : ℝ) := Real.rpow_pos_of_pos ht _
  have h2 : (0 : ℝ) < x ^ 2 := by positivity
  apply div_neg_of_neg_of_pos <;> nlinarith
