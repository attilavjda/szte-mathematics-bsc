import Mathlib

/-!
# Machine-checked counterparts of the diagrammatic proofs

This file accompanies `diagrams/DiagrammaticReasoning.tex` (and the PDF built from it).
That document explains how the two shared syllabus items of *Kalkulus I* and
*Lineáris algebra I* — the **triangle inequality** and the **inverse** — can be drawn,
and how one can reason about them using pictures only.  Every picture in the document
carries an algebraic content, and this file states and proves exactly those contents,
so that no figure has to be believed on faith.

Each declaration below is tagged with the figure of the document it certifies and, where
applicable, with the exercise of `kalkulus_gyakorlo.pdf` it solves.
-/

namespace DiagramProofs

open Finset Matrix

/-! ## 1. The triangle inequality pictures -/

/-- **Figure: the detour.**  `d x z ≤ d x y + d y z` in any metric space: going from `x`
to `z` through `y` is never shorter than going directly.  This is the picture that all
other triangle pictures are instances of. -/
theorem detour {X : Type*} [MetricSpace X] (x y z : X) :
    dist x z ≤ dist x y + dist y z :=
  dist_triangle x y z

/-- **Figure: the ball inside a ball** (the triangle inequality as an inclusion of discs).
If `y` lies in the open ball around `x` of radius `r`, then the ball around `y` of the
leftover radius `r - dist x y` is contained in the original ball.  Drawing two nested
discs *is* a proof of the triangle inequality, and conversely.  This is the picture
behind "an open set contains a ball around each of its points". -/
theorem ball_subset_ball_of_mem {X : Type*} [MetricSpace X] (x y : X) (r : ℝ) :
    Metric.ball y (r - dist y x) ⊆ Metric.ball x r := by
  intro z hz
  have hz' : dist z y < r - dist y x := Metric.mem_ball.mp hz
  have : dist z x ≤ dist z y + dist y x := dist_triangle z y x
  exact Metric.mem_ball.mpr (by linarith)

/-- **Figure: the reversed triangle** — exercise 1.11 of `kalkulus_gyakorlo.pdf`:
`| |x| − |y| | ≤ |x − y|`.  Drawn as the triangle with vertices `0, x, y`: the side
`x − y` is at least the difference of the other two sides. -/
theorem abs_abs_sub_abs_le (x y : ℝ) : |(|x| - |y|)| ≤ |x - y| :=
  abs_abs_sub_abs_le_abs_sub x y

/-- **Figure: the polygon** — exercise 1.13 of `kalkulus_gyakorlo.pdf`, the generalised
triangle inequality `|a₁ + ⋯ + aₙ| ≤ |a₁| + ⋯ + |aₙ|`.  Drawn as a closed polygonal path:
the straight segment from the first vertex to the last is shorter than the broken line. -/
theorem abs_sum_range_le_sum_abs (a : ℕ → ℝ) (n : ℕ) :
    |∑ i ∈ range n, a i| ≤ ∑ i ∈ range n, |a i| :=
  Finset.abs_sum_le_sum_abs a (range n)

/-- **Figure: the vector polygon** — the same picture in `ℝⁿ`, which is the *Lineáris
algebra I* form of the statement: `‖u + v‖ ≤ ‖u‖ + ‖v‖`. -/
theorem norm_add_le' {n : ℕ} (u v : EuclideanSpace ℝ (Fin n)) : ‖u + v‖ ≤ ‖u‖ + ‖v‖ :=
  norm_add_le u v

/-- **Figure: the ε-interval** — exercise 1.12 i) of `kalkulus_gyakorlo.pdf`.
`|x − 5| ≤ ε` is drawn as the symmetric interval of radius `ε` centred at `5`; solving the
inequality *is* reading off the endpoints of that interval. -/
theorem abs_sub_le_iff_mem_Icc (c x ε : ℝ) :
    |x - c| ≤ ε ↔ x ∈ Set.Icc (c - ε) (c + ε) := by
  rw [abs_sub_le_iff, Set.mem_Icc]
  constructor
  · rintro ⟨h₁, h₂⟩; constructor <;> linarith
  · rintro ⟨h₁, h₂⟩; constructor <;> linarith

/-- **Figure: two ε-intervals** — exercise 1.12 a) of `kalkulus_gyakorlo.pdf`,
`|x + 2| > 4`.  The picture is the complement of an interval: two rays. -/
theorem abs_add_gt_iff (x : ℝ) : |x + 2| > 4 ↔ x < -6 ∨ 2 < x := by
  rw [gt_iff_lt, lt_abs]
  constructor
  · rintro (h | h)
    · exact Or.inr (by linarith)
    · exact Or.inl (by linarith)
  · rintro (h | h)
    · exact Or.inr (by linarith)
    · exact Or.inl (by linarith)

/-- **Figure: the ε-band and the δ-strip** — exercise 3.1 a) of `kalkulus_gyakorlo.pdf`.
The limit statement `lim_{x→1} 1/(x³+2) = 1/3` is the picture of the graph entering every
horizontal band of half-width `ε` once `x` is inside a vertical strip of half-width `δ`. -/
theorem tendsto_3_1a :
    Filter.Tendsto (fun x : ℝ => 1 / (x ^ 3 + 2)) (nhds 1) (nhds (1 / 3)) := by
  have h : ((1 : ℝ) ^ 3 + 2) ≠ 0 := by norm_num
  have hc : ContinuousAt (fun x : ℝ => 1 / (x ^ 3 + 2)) 1 :=
    ContinuousAt.div continuousAt_const (by fun_prop) h
  have := hc.tendsto
  norm_num at this
  simpa using this

/-- **Figure: the Nelsen square** — the two-variable AM–GM inequality `√(ab) ≤ (a+b)/2`,
the archetype of a *proof without words*: the geometric mean is the altitude of a right
triangle in a semicircle of diameter `a + b`, hence at most the radius. -/
theorem sqrt_mul_le_add_div_two {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a * b) ≤ (a + b) / 2 := by
  have hsq : a * b ≤ ((a + b) / 2) ^ 2 := by nlinarith [sq_nonneg (a - b)]
  have h2 : (0 : ℝ) ≤ (a + b) / 2 := by linarith
  calc Real.sqrt (a * b) ≤ Real.sqrt (((a + b) / 2) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = (a + b) / 2 := by rw [Real.sqrt_sq h2]

/-- **Figure: the rectangle in the square** — exercise 4.11 a) of `kalkulus_gyakorlo.pdf`:
splitting `20` into two summands of maximal product.  The picture is a rectangle of fixed
perimeter inscribed in the square of the same perimeter; no derivative is needed. -/
theorem split_twenty_max_product (x : ℝ) : x * (20 - x) ≤ 10 * 10 := by
  nlinarith [sq_nonneg (x - 10)]

/-- **Figure: the staircase of `2n+1`-gnomons** — exercise 1.16 of
`kalkulus_gyakorlo.pdf`, the "proof without words" for `∑ i² = n(n+1)(2n+1)/6`, stated in
the cleared-denominator form that the picture actually produces (three copies of the
staircase tile a box). -/
theorem six_mul_sum_sq (n : ℕ) :
    6 * ∑ i ∈ range (n + 1), (i : ℕ) ^ 2 = n * (n + 1) * (2 * n + 1) := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ, Nat.mul_add, ih]
      ring

/-! ## 2. The inverse pictures -/

/-- **Figure: the mirror in the line `y = x`** — the universal picture for inverse
functions, used in exercises 2.3–2.9 of `kalkulus_gyakorlo.pdf`.  A point is on the graph
of `f` exactly when its mirror image is on the graph of `f⁻¹`. -/
theorem mem_graph_iff_swap_mem_graph_symm {α β : Type*} (e : α ≃ β) (a : α) (b : β) :
    b = e a ↔ a = e.symm b := by
  constructor
  · rintro rfl; exact (e.symm_apply_apply a).symm
  · rintro rfl; exact (e.apply_symm_apply b).symm

/-- **Figure: the snake / the two triangles** — the categorical content of "inverse":
a two-sided inverse is unique.  Diagrammatically this is the statement that a wire with a
zig and a zag can be pulled straight; equivalently, that the two triangles of the
composition diagram paste into one. -/
theorem inverse_unique {α β : Type*} (f : α → β) (g g' : β → α)
    (hg : ∀ a, g (f a) = a) (hg' : ∀ b, f (g' b) = b) : g = g' := by
  funext b
  calc g b = g (f (g' b)) := by rw [hg' b]
    _ = g' b := hg (g' b)

/-- **Figure: the mirror is an involution** — exercise 2.7 of `kalkulus_gyakorlo.pdf`:
`f(x) = (x+1)/(x−1)` satisfies `f ∘ f = id`, so its graph is *symmetric* about the line
`y = x`; the picture is a single hyperbola invariant under the mirror. -/
theorem self_inverse_2_7 {x : ℝ} (hx : x ≠ 1) :
    ((x + 1) / (x - 1) + 1) / ((x + 1) / (x - 1) - 1) = x := by
  have h : x - 1 ≠ 0 := sub_ne_zero.mpr hx
  field_simp
  ring

/-- **Figure: the horizontal line test** — a strictly monotone function is injective, the
reason why the pictures of exercises 2.2 and 2.5 decide injectivity at a glance. -/
theorem strictMono_injective {f : ℝ → ℝ} (hf : StrictMono f) : Function.Injective f :=
  hf.injective

/-- **Figure: two arrows in a row** — exercise 2.18 of `kalkulus_gyakorlo.pdf`: a
composite of injective maps is injective.  In the bag-and-arrow (Euler) picture, no two
dots merge along the first arrow, and none along the second, hence none along the
composite. -/
theorem injective_comp {α β γ : Type*} {f : β → γ} {g : α → β}
    (hf : Function.Injective f) (hg : Function.Injective g) :
    Function.Injective (f ∘ g) :=
  hf.comp hg

/-- **Figure: the commuting square** — exercise 2.11 of `kalkulus_gyakorlo.pdf`:
`f ∘ g = g ∘ f` for `f(x) = 2x² − 1` and `g(x) = 4x³ − 3x`.  The drawing is a square of
four arrows that closes; the underlying reason is that both composites are the Chebyshev
polynomial `T₆`. -/
theorem chebyshev_square (x : ℝ) :
    (2 * (4 * x ^ 3 - 3 * x) ^ 2 - 1) = (4 * (2 * x ^ 2 - 1) ^ 3 - 3 * (2 * x ^ 2 - 1)) := by
  ring

/-- **Figure: the isomorphism as a pair of arrows** — the linear-algebra half of the
inverse overlap: a square matrix with a nonzero determinant is exactly one whose
associated map is bijective. -/
theorem det_ne_zero_iff_bijective {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    M.det ≠ 0 ↔ Function.Bijective (fun x : Fin n → ℝ => M *ᵥ x) := by
  constructor
  · intro h
    have hu : IsUnit M.det := isUnit_iff_ne_zero.mpr h
    refine ⟨fun x y hxy => ?_, fun y => ⟨M⁻¹ *ᵥ y, ?_⟩⟩
    · have := congrArg (fun z => M⁻¹ *ᵥ z) hxy
      simpa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul M hu] using this
    · simp [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv M hu]
  · intro h
    have hinj : Function.Injective M.mulVec := h.1
    have hu : IsUnit M := Matrix.mulVec_injective_iff_isUnit.mp hinj
    exact isUnit_iff_ne_zero.mp ((Matrix.isUnit_iff_isUnit_det M).mp hu)

/-! ## 3. The bridge drawn in one picture

The length map `‖·‖ : ℝⁿ → ℝ` is short (distance non-increasing): it is the arrow that
carries the linear-algebra triangle picture onto the calculus one.  Diagrammatically it is
the single arrow joining the two halves of the document's final figure. -/

/-- **Figure: the bridge**.  `| ‖u‖ − ‖v‖ | ≤ ‖u − v‖`: taking lengths never increases
distances, so the vector triangle projects onto the absolute-value triangle. -/
theorem length_short {n : ℕ} (u v : EuclideanSpace ℝ (Fin n)) :
    |‖u‖ - ‖v‖| ≤ ‖u - v‖ :=
  abs_norm_sub_norm_le u v

end DiagramProofs
