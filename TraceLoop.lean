import Mathlib
import RequestProject.DiagramDictionary

/-!
# The trace is a loop, and boxes slide around a loop

This file is the Lean companion of `trace-loop.tex` / `trace-loop.pdf`, the
note about the Mathlib theorem

```
theorem Matrix.trace_units_conj' (M : (Matrix m m R)ˣ) (N : Matrix m m R) :
    trace ((↑M⁻¹ : Matrix _ _ _) * N * (↑M : Matrix _ _ _)) = trace N
```

(the theorem whose only change in the quoted diff was the replacement of
`set_option linter.docPrime false in` by a real docstring).

Everything below is stated for square matrices over a commutative (semi)ring
and proved from the *loop* picture:

* `trace_is_a_loop` — closing a box into a loop sums over the shared index;
* `loop_eq_dim` — a bare loop evaluates to the dimension;
* `two_boxes_on_a_loop` — two boxes on one closed wire is a double sum;
* `slide_box` — sliding a box past the join: `tr (A * B) = tr (B * A)`,
  proved *by hand* from the double sum, so that the diagrammatic move and the
  index bookkeeping sit next to each other;
* `slide_three`, `trace_rotate`, `trace_rotate_iterate` — invariance of the
  trace under arbitrary cyclic rotation of a list of boxes on the loop;
* `trace_units_conj_left`, `trace_units_conj_right` — the two Mathlib
  statements, reproved by sliding;
* `trace_similar`, together with `det_similar` and `charpoly_similar`, which
  are the invariants Szabó László's notes actually record for similar matrices
  (Definition 4.4, Theorem 4.5, Theorem 9.6, Theorem 14.3);
* `trace_basis_independent` — the categorical formulation: the trace of an
  endomorphism is defined without reference to a basis, and conjugation
  invariance is the shadow of that fact.
-/

namespace TraceLoop

open Matrix
open scoped BigOperators

section Loop

variable {R : Type*} [CommSemiring R] {m n : Type*} [Fintype m] [Fintype n]

/-- **The trace is a loop.**  Joining the output leg of the box `A` back to its
input leg forces the two indices to agree and sums over them. -/
theorem trace_is_a_loop (A : Matrix n n R) : trace A = ∑ i, A i i := rfl

/-- **A bare loop counts dimensions.**  A closed wire with no box on it is the
Kronecker delta contracted with itself, `δⁱ_i = n`. -/
theorem loop_eq_dim [DecidableEq n] :
    trace (1 : Matrix n n R) = (Fintype.card n : R) := by
  simp [Matrix.trace_one]

/-- **Two boxes on one loop.**  Putting `A` and `B` in series on a closed wire
contracts *two* indices: the wire between them, and the wire that closes the
loop. -/
theorem two_boxes_on_a_loop (A : Matrix m n R) (B : Matrix n m R) :
    trace (A * B) = ∑ i, ∑ j, A i j * B j i := by
  simp [Matrix.trace, Matrix.diag, Matrix.mul_apply]

/-- **Sliding a box around the loop.**  On a circle there is no first box, only
a cyclic order, so `B` may be slid past the join and become the leading box.

The proof is the diagrammatic move made explicit: read the double sum of
`two_boxes_on_a_loop` the other way round (`Finset.sum_comm` — the picture has
no preferred order in which to contract the two closed indices) and commute the
scalars (the two boxes sit at unrelated places on the wire). -/
theorem slide_box (A : Matrix m n R) (B : Matrix n m R) :
    trace (A * B) = trace (B * A) := by
  rw [two_boxes_on_a_loop, two_boxes_on_a_loop, Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => mul_comm _ _

/-- Sliding with three boxes on the loop: `tr (ABC) = tr (CAB)`. -/
theorem slide_three {p : Type*} [Fintype p]
    (A : Matrix m n R) (B : Matrix n p R) (C : Matrix p m R) :
    trace (A * B * C) = trace (C * (A * B)) :=
  slide_box (A * B) C

/-- **One click of the rotation.**  For a list of square boxes threaded onto the
loop, moving the first box to the end does not change the trace. -/
theorem trace_rotate [DecidableEq n] (l : List (Matrix n n R)) :
    trace l.prod = trace (l.rotate 1).prod := by
  cases l with
  | nil => simp
  | cons A t =>
      rw [List.rotate_cons_succ, List.rotate_zero, List.prod_append, List.prod_cons,
        List.prod_singleton]
      exact slide_box A t.prod

/-- **Full cyclic invariance.**  Any number of clicks leaves the trace alone:
the loop only remembers the cyclic order of the boxes on it. -/
theorem trace_rotate_iterate [DecidableEq n] (l : List (Matrix n n R)) (k : ℕ) :
    trace l.prod = trace (l.rotate k).prod := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [← List.rotate_rotate, ← trace_rotate, ← ih]

end Loop

/-- **Cyclic, but not symmetric.**  Boxes may be rotated on the loop, not
permuted: turning `A B C` into `B A C` would make two wires cross.  A concrete
witness over `ℤ`. -/
theorem trace_cyclic_not_symmetric :
    ∃ A B C : Matrix (Fin 2) (Fin 2) ℤ, trace (A * B * C) ≠ trace (B * A * C) := by
  refine ⟨!![0, 1; 0, 0], !![0, 0; 1, 0], !![1, 0; 0, 0], ?_⟩
  simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_two]

section Conjugation

variable {R : Type*} [CommSemiring R] {m : Type*} [Fintype m] [DecidableEq m]

/-- **The trace is invariant under conjugation by a unit** (`Matrix.trace_units_conj`).
Diagrammatically: `M` and `M⁻¹` sit on the same loop with `N` between them;
slide `M` all the way round until it meets `M⁻¹`, and the pair annihilates. -/
theorem trace_units_conj_left (M : (Matrix m m R)ˣ) (N : Matrix m m R) :
    trace ((M : Matrix m m R) * N * (↑M⁻¹ : Matrix m m R)) = trace N := by
  rw [slide_three, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one,
    Matrix.one_mul]

/-- **The trace is invariant under conjugation by a unit, with the inverse on the
left** (`Matrix.trace_units_conj'`, the theorem in the quoted diff).  It is the
previous statement applied to `M⁻¹`: on a loop the two pictures differ only by
which of the two boxes you call "first". -/
theorem trace_units_conj_right (M : (Matrix m m R)ˣ) (N : Matrix m m R) :
    trace ((↑M⁻¹ : Matrix m m R) * N * (M : Matrix m m R)) = trace N := by
  rw [slide_three, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
    Matrix.one_mul]

/-- The same statement without units: a one-sided inverse suffices, because the
loop is closed by sliding, not by inverting. -/
theorem trace_conj_of_mul_eq_one (A P Q : Matrix m m R) (h : P * Q = 1) :
    trace (Q * A * P) = trace A := by
  rw [slide_three, ← Matrix.mul_assoc, h, Matrix.one_mul]

end Conjugation

section Similar

variable {K : Type*} [CommRing K] {n : Type*} [Fintype n] [DecidableEq n]

/-- Szabó László, *Bevezetés a lineáris algebrába*, Definition 4.4: `A` and `B`
are **similar** (`hasonló`) when `B = X⁻¹ A X` for an invertible `X`. -/
def Similar (A B : Matrix n n K) : Prop :=
  ∃ X : (Matrix n n K)ˣ, B = (↑X⁻¹ : Matrix n n K) * A * (X : Matrix n n K)

/-- Similarity is reflexive (Szabó, Theorem 4.5). -/
theorem Similar.refl (A : Matrix n n K) : Similar A A := ⟨1, by simp⟩

/-- Similarity is symmetric (Szabó, Theorem 4.5). -/
theorem Similar.symm {A B : Matrix n n K} (h : Similar A B) : Similar B A := by
  obtain ⟨X, rfl⟩ := h
  refine ⟨X⁻¹, ?_⟩
  simp [Matrix.mul_assoc, ← Matrix.mul_assoc (↑X : Matrix n n K)]

/-- Similarity is transitive (Szabó, Theorem 4.5). -/
theorem Similar.trans {A B C : Matrix n n K} (h₁ : Similar A B) (h₂ : Similar B C) :
    Similar A C := by
  obtain ⟨X, rfl⟩ := h₁
  obtain ⟨Y, rfl⟩ := h₂
  refine ⟨X * Y, ?_⟩
  simp [_root_.mul_inv_rev, Matrix.mul_assoc]

/-- **Similar matrices have the same trace.**  This is the loop statement; the
textbook records the analogous facts for the determinant (Theorem 4.5), the rank
(Theorem 9.6) and the characteristic polynomial (Theorem 14.3). -/
theorem trace_similar {A B : Matrix n n K} (h : Similar A B) : trace B = trace A := by
  obtain ⟨X, rfl⟩ := h
  exact trace_units_conj_right X A

/-- Szabó, Theorem 4.5: similar matrices have the same determinant. -/
theorem det_similar {A B : Matrix n n K} (h : Similar A B) : B.det = A.det := by
  obtain ⟨X, rfl⟩ := h
  exact Matrix.det_units_conj' X A

/-- Szabó, Theorem 14.3: similar matrices have the same characteristic
polynomial — the single invariant that contains both the trace and the
determinant as coefficients. -/
theorem charpoly_similar {A B : Matrix n n K} (h : Similar A B) : B.charpoly = A.charpoly := by
  obtain ⟨X, rfl⟩ := h
  exact Matrix.charpoly_units_conj' X A

end Similar

section Categorical

variable {K M N : Type*} [CommRing K] [AddCommGroup M] [Module K M] [AddCommGroup N] [Module K N]

/-- **The categorical reading.**  The trace of an endomorphism is defined by the
evaluation/coevaluation pair (cap and cup) of a dualizable object, with no basis
in sight; conjugation invariance is then automatic, because transporting an
endomorphism along an isomorphism `e : M ≃ₗ[K] N` transports the whole loop.
Szabó's Corollary 13.5 is the matrix shadow of this statement: the matrices of
one linear transformation in two bases are similar. -/
theorem trace_basis_independent (f : M →ₗ[K] M) (e : M ≃ₗ[K] N) :
    LinearMap.trace K N (e.conj f) = LinearMap.trace K M f :=
  LinearMap.trace_conj' f e

/-- The trace of an endomorphism is the trace of any of its matrices; this is the
bridge between the loop of wires and the sum of diagonal entries. -/
theorem trace_eq_matrix_trace_of_basis {ι : Type*} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K M) (f : M →ₗ[K] M) :
    LinearMap.trace K M f = trace (LinearMap.toMatrix b b f) :=
  LinearMap.trace_eq_matrix_trace K b f

/-- Cyclicity at the level of maps: `tr (g ∘ f) = tr (f ∘ g)`, the same slide,
now with no indices at all. -/
theorem trace_comp_slide [Module.Free K M] [Module.Finite K M] [Module.Free K N]
    [Module.Finite K N] (f : M →ₗ[K] N) (g : N →ₗ[K] M) :
    LinearMap.trace K M (g ∘ₗ f) = LinearMap.trace K N (f ∘ₗ g) :=
  LinearMap.trace_comp_comm' f g

/-- **A loop through a projection counts the dimension it projects onto.**  With
`f = 1` this is the bare loop counting the whole dimension. -/
theorem trace_isProj_eq_finrank
    {p : Submodule K M} {f : M →ₗ[K] M} (h : LinearMap.IsProj p f)
    [Module.Free K p] [Module.Finite K p] [Module.Free K (LinearMap.ker f)]
    [Module.Finite K (LinearMap.ker f)] :
    LinearMap.trace K M f = (Module.finrank K p : K) :=
  h.trace

end Categorical

end TraceLoop
