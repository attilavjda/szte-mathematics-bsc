/-
# CurriculumPatterns — one categorical pattern, four theorems from two BSc courses

A "verification pearl": a single abstract lemma about composition, proved once,
whose instances are standard results from the linear algebra and the
analysis/calculus strands of a mathematics BSc curriculum.

| Module | Curriculum topic | Ordered monoid of costs | Statement recovered |
|--------|------------------|-------------------------|---------------------|
| `LaxCost` | — (the pattern) | any preorder with a monotone `op` | `LaxCost.cost_chain`, `LaxCost.cost_chain_eq` |
| `MetricPearl` | analysis: metric spaces | `(ℝ≥0, +, 0)` | polygon inequality `dist (x 0) (x n) ≤ ∑ dist (x i) (x (i+1))` |
| `OperatorPearl` | linear algebra: operator norm | `(ℝ≥0, ·, 1)` | `‖fⁿ‖ ≤ ‖f‖ⁿ` |
| `LipschitzPearl` | analysis: contractions | `(ℝ≥0, ·, 1)` | `LipschitzWith (Kⁿ) f^[n]` |
| `DeterminantPearl` | linear algebra: determinant | `(ℝ≥0, ·, 1)`, *strict* | `|det (Aⁿ)| = |det A|ⁿ` |
| `Functoriality` | both: maps of spaces | pullback of costs along functors | `LipschitzWith K g` as a comparison of costs |

The point of the table is the middle column: the triangle inequality and
submultiplicativity of the operator norm are *the same axiom* — laxness of a
cost for composition — differing only in which ordered monoid the cost lands
in, and the determinant is the strict (functorial) degeneration of the same
axiom.

Everything is `sorry`-free and uses only Lean's standard axioms.
-/
import CurriculumPatterns.LaxCost
import CurriculumPatterns.MetricPearl
import CurriculumPatterns.OperatorPearl
import CurriculumPatterns.LipschitzPearl
import CurriculumPatterns.DeterminantPearl
import CurriculumPatterns.Functoriality
