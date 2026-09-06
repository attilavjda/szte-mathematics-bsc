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