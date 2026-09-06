# Summary of changes for run 6b715357-5230-4017-b4ee-fe224024d976
I found a second topic shared by the two `Tárgytematika` documents and formalized it in a new, self-contained Lean file `RequestProject/TriangleOverlap.lean` (the earlier file on the inverse/isomorphism overlap is untouched).

**The shared element: the triangle inequality (distance).**
- *Kalkulus I (MBLK37E)*: "A valós számtest… **nevezetes egyenlőtlenségek**" — the absolute value and `|x + y| ≤ |x| + |y|`, the basic estimate behind every limit in the course.
- *Lineáris algebra I (MBLK15E)*: "Belső szorzat, **vektorok hossza, háromszög-egyenlőtlenség, Cauchy–Schwarz-egyenlőtlenség**" — the Euclidean length and `‖u + v‖ ≤ ‖u‖ + ‖v‖`.

**The category-theoretic reading (Lawvere).** A metric is a category enriched over the poset `([0,∞), ≥, +)`: points are objects, `d x y` is the hom-object, `d x x = 0` is the identity, and the triangle inequality `d x z ≤ d x y + d y z` *is* composition; distance non-increasing (short) maps are the enriched functors.

What the file contains, all building with no `sorry` and using only the standard axioms:
- `LawvereSpace` — the common structure, and `instCategoryLawvereSpace`, a genuine `Category` instance on Lawvere spaces with short maps as morphisms (the category `Met`).
- `dist_chain` — the *one* abstract theorem: composing the `n` morphisms of a chain gives `d (f 0) (f n) ≤ ∑ d (f i) (f (i+1))`. Its two specialisations are the calculus statement `abs_sum_le_of_chain` (`|∑ aᵢ| ≤ ∑ |aᵢ|`) and the linear algebra statement `norm_sum_le_of_chain` (`‖∑ vᵢ‖ ≤ ∑ ‖vᵢ‖`) — same theorem, two courses.
- The two syllabus instances `calcSpace` (ℝ with `|x − y|`) and `linAlgSpace n` (ℝⁿ with the Euclidean distance), together with the named inequalities `abs_add_le'`, `norm_add_le'` and `cauchy_schwarz` (`|∑ uᵢvᵢ| ≤ ‖u‖‖v‖`), each obtained from composition in the corresponding space.
- The bridge `lengthShort`: the length map `‖·‖ : ℝⁿ → ℝ` is a morphism `linAlgSpace n ⟶ calcSpace` in `Met`, i.e. an enriched functor carrying the linear algebra distance onto the calculus distance; and `calcIsoLinAlgOne`, an isomorphism `calcSpace ≅ linAlgSpace 1`, showing the two syllabus items literally coincide in dimension one.
- Equivalence and invariant: `nonempty_iso_equivalence` (being isometric is an equivalence relation) and `iso_isometry` (an isomorphism in `Met` preserves every distance exactly), with `calc_dist_eq_linAlg_dist` as the concrete instance.

The Properties table lists all of these, and the work is committed and pushed.

# Summary of changes for run 9a301132-a458-4546-a0e6-03785df6f766
I read the two course descriptions (Kalkulus I előadás, MBLK37E and Lineáris algebra I., MBLK15E) and picked out one topic that appears in both syllabi:

- Kalkulus I, "Tantárgy tartalma": *"…exponenciális függvények és inverzeik. Értelmezési tartomány, értékkészlet, inverz függvény, összetétel."* — composition of functions and the inverse function.
- Lineáris algebra I, "Tantárgy tartalma": *"Mátrixegyenletek, mátrixok inverze…"*, *"nemelfajuló mátrixok, Cramer-szabály"* — matrix multiplication (composition of linear maps) and the inverse matrix.

The shared content is **inverse with respect to composition**, i.e. *isomorphism in a category*. This is formalized in the new file `RequestProject/InverseOverlap.lean`, which builds cleanly with no `sorry` and uses only the standard axioms:

- `SyllabusOverlap.inverse_unique` — the single abstract theorem, in an arbitrary category: if `f ≫ g = 𝟙` and `g' ≫ f = 𝟙` then `g = g'`.
- Calculus instance: `expMap`/`logMap` and `expIso`, exhibiting `exp : ℝ → (0,∞)` as an isomorphism in the category of sets; `log_eq_of_inverse` and `exp_eq_of_inverse` then say that `log` (resp. `exp`) is the *only* inverse — obtained by applying the abstract theorem, not re-proved.
- Linear algebra instance: `matMap`, `matrixIso`, exhibiting a matrix with invertible determinant as an isomorphism in the category of ℝ-modules; `matrix_inverse_eq_of_inverse` (`M * N = 1 → N = M⁻¹`) is again the same abstract theorem applied in that category.
- The bridge `linearIso_bijective`: the forgetful functor from ℝ-modules to sets carries the linear-algebra isomorphism to a bijection `x ↦ M *ᵥ x`, i.e. exactly the calculus notion of invertible map — because every functor preserves isomorphisms. This is the precise sense in which the two syllabus items coincide.
- Equivalence and invariants: `nonempty_iso_equivalence` (being isomorphic is an equivalence relation in any category), with the matching invariant on each side — `cardinality_invariant` (cardinality of a set) and `dimension_invariant` (isomorphic `ℝⁿ`, `ℝᵐ` force `n = m`).

All results are listed in the Properties table and the work is committed and pushed.