import Mathlib
import RequestProject.GraphicalLinearAlgebra
import RequestProject.SzaboMatrices

/-!
# A dictionary: matrices ↔ circuits ↔ Penrose index diagrams

This file is the technical heart of the guide.  It connects the three pictorial
languages used in `guide.tex` with the textbook material of `SzaboMatrices`.

* **Circuits (graphical linear algebra).**  A diagram is a *linear relation*
  `LinearRel R M N = Submodule R (M × N)` (see
  `RequestProject/GraphicalLinearAlgebra.lean`).  A linear map, in particular a
  matrix, becomes the circuit given by its graph (`ofLinearMap`, `ofMatrix`).
  Series composition of circuits is composition of relations, and we prove it
  matches matrix multiplication.

* **Penrose index notation.**  A matrix is a two-legged tensor `Aⁱ_j`; joining
  legs means summing over the shared index.  Matrix multiplication *is*
  contraction (`penrose_contraction`), the identity matrix is the Kronecker
  delta which "absorbs into a wire" (`delta_absorb_left/right`), bending a leg
  transposes (`transpose_is_adjoint`), and a closed loop evaluates to the
  dimension (`loop_eq_dim`), while a loop through two boxes may be slid around
  (`trace_cyclic`).

* **The junctions of graphical linear algebra as matrices.**  Copying,
  adding, discarding and the zero state are the `2 × 1`, `1 × 2`, `0 × 1` and
  `1 × 0` matrices whose entries are all `1` resp. empty
  (`copyMat`, `addMat`); the characteristic equations of the calculus become
  small matrix identities (`add_after_copy`, `copy_addMat_bialgebra`).
-/

namespace Diagram

open Matrix GraphicalLinearAlgebra GraphicalLinearAlgebra.LinearRel

open scoped BigOperators

/-! ## Circuits from linear maps -/

section Maps

variable {R : Type*} [CommSemiring R]
variable {M N P : Type*}
variable [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
variable [AddCommMonoid P] [Module R P]

/-- The circuit denoted by a linear map: its graph. -/
def ofLinearMap (f : M →ₗ[R] N) : LinearRel R M N := f.graph

@[simp] theorem mem_ofLinearMap (f : M →ₗ[R] N) (x : M) (y : N) :
    (x, y) ∈ ofLinearMap f ↔ y = f x := LinearMap.mem_graph_iff f (x, y)

/-- A plain wire is the identity map. -/
@[simp] theorem ofLinearMap_id : ofLinearMap (LinearMap.id : M →ₗ[R] M) = LinearRel.id R M := by
  ext ⟨x, y⟩
  simp [LinearRel.id, eq_comm]

/-- Series composition of circuits is composition of maps. -/
theorem ofLinearMap_comp (f : M →ₗ[R] N) (g : N →ₗ[R] P) :
    LinearRel.comp R M N P (ofLinearMap f) (ofLinearMap g) = ofLinearMap (g ∘ₗ f) := by
  ext ⟨x, z⟩
  constructor
  · rintro ⟨y, hy, hz⟩
    rw [mem_ofLinearMap] at hy hz ⊢
    subst hy
    exact hz
  · intro h
    rw [mem_ofLinearMap] at h
    exact ⟨f x, by simp, by simpa using h⟩

end Maps

/-! ## Circuits from matrices -/

section Matrices

variable {K : Type*} [CommRing K] {l m n : ℕ}

/-- The circuit of a matrix: `n` wires in, `m` wires out. -/
def ofMatrix (A : Szabo.Mat K m n) : LinearRel K (Fin n → K) (Fin m → K) :=
  ofLinearMap A.mulVecLin

@[simp] theorem mem_ofMatrix (A : Szabo.Mat K m n) (x : Fin n → K) (y : Fin m → K) :
    (x, y) ∈ ofMatrix A ↔ ∀ i, y i = ∑ j, A i j * x j := by
  simp [ofMatrix, funext_iff, Matrix.mulVec, dotProduct]

/-- A bundle of `n` plain wires is the identity matrix. -/
@[simp] theorem ofMatrix_one : ofMatrix (1 : Szabo.Mat K n n) = LinearRel.id K (Fin n → K) := by
  rw [ofMatrix, Matrix.mulVecLin_one, ofLinearMap_id]

/-- **Series composition is matrix multiplication.**  Reading circuits left to
right, first `B` and then `A` is the circuit of `A * B`; this is Szabó's
definition 2.4 and the associativity in theorem 2.5 becomes associativity of
plugging circuits together. -/
theorem ofMatrix_mul (A : Szabo.Mat K m n) (B : Szabo.Mat K l m) :
    LinearRel.comp K (Fin n → K) (Fin m → K) (Fin l → K) (ofMatrix A) (ofMatrix B) =
      ofMatrix (B * A) := by
  rw [ofMatrix, ofMatrix, ofMatrix, ofLinearMap_comp, Matrix.mulVecLin_mul]

/-! ## Penrose index notation -/

/-- **Contraction.**  Joining the output legs of `A` to the input legs of `B`
sums over the shared index: this is exactly the definition of the matrix
product. -/
theorem penrose_contraction (A : Szabo.Mat K m n) (B : Szabo.Mat K n l) (i : Fin m) (j : Fin l) :
    (A * B) i j = ∑ k, A i k * B k j := rfl

/-- The Kronecker delta `δⁱ_j` is the identity matrix. -/
theorem delta_eq_one (i j : Fin n) : (1 : Szabo.Mat K n n) i j = if i = j then 1 else 0 := by
  simp [Matrix.one_apply]

/-- A delta joined to a leg is absorbed into the wire (left version). -/
theorem delta_absorb_left (A : Szabo.Mat K n m) (i : Fin n) (j : Fin m) :
    (∑ k, (if i = k then (1 : K) else 0) * A k j) = A i j := by
  simp

/-- A delta joined to a leg is absorbed into the wire (right version). -/
theorem delta_absorb_right (A : Szabo.Mat K m n) (i : Fin m) (j : Fin n) :
    (∑ k, A i k * (if k = j then (1 : K) else 0)) = A i j := by
  simp

/-- **Bending a leg transposes the box**: the transpose is the adjoint of `A`
for the pairing given by cup and cap. -/
theorem transpose_is_adjoint (A : Szabo.Mat K m n) (x : Fin n → K) (y : Fin m → K) :
    (A.mulVec x) ⬝ᵥ y = x ⬝ᵥ (Aᵀ.mulVec y) := by
  simp [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, dotProduct_comm]

/-- **A closed loop counts dimensions**: `δⁱ_i = n`. -/
theorem loop_eq_dim : (1 : Szabo.Mat K n n).trace = (n : K) := by
  simp [Matrix.trace_one]

/-- **A loop can be slid around**: the trace is cyclic. -/
theorem trace_cyclic (A : Szabo.Mat K m n) (B : Szabo.Mat K n m) :
    (A * B).trace = (B * A).trace := Matrix.trace_mul_comm A B

/-! ## The junctions of graphical linear algebra, as matrices -/

/-- The copy junction `—•<`: one wire in, two equal wires out. -/
def copyMat (K : Type*) [CommRing K] : Szabo.Mat K 2 1 := fun _ _ => 1

/-- The add junction `>•—`: two wires in, their sum out. -/
def addMat (K : Type*) [CommRing K] : Szabo.Mat K 1 2 := fun _ _ => 1

/-- The discard junction: the unique `0 × 1` matrix. -/
def discardMat (K : Type*) [CommRing K] : Szabo.Mat K 0 1 := fun i _ => i.elim0

/-- The zero state: the unique `1 × 0` matrix. -/
def zeroMat (K : Type*) [CommRing K] : Szabo.Mat K 1 0 := fun _ j => j.elim0

@[simp] theorem mem_ofMatrix_copy (x : Fin 1 → K) (y : Fin 2 → K) :
    (x, y) ∈ ofMatrix (copyMat K) ↔ ∀ i, y i = x 0 := by
  simp [copyMat]

@[simp] theorem mem_ofMatrix_add (x : Fin 2 → K) (y : Fin 1 → K) :
    (x, y) ∈ ofMatrix (addMat K) ↔ y 0 = x 0 + x 1 := by
  constructor
  · intro h
    have := (mem_ofMatrix _ _ _).1 h 0
    simpa [addMat, Fin.sum_univ_two] using this
  · intro h
    rw [mem_ofMatrix]
    intro i
    fin_cases i
    simpa [addMat, Fin.sum_univ_two] using h

/-- **Copy then add is multiplication by 2** — the elementary "bialgebra"
computation of the calculus: `add ∘ copy = 2`. -/
theorem add_after_copy : addMat K * copyMat K = fun _ _ => (2 : K) := by
  funext i j
  simp [addMat, copyMat, Matrix.mul_apply]

/-- **Copy after add is the `2 × 2` all-ones matrix** — the other side of the
bialgebra law, whose entries record the four ways of routing two inputs into
two outputs. -/
theorem copy_addMat_bialgebra : copyMat K * addMat K = fun _ _ => (1 : K) := by
  funext i j
  simp [addMat, copyMat, Matrix.mul_apply]

/-- Discarding the output of any circuit discards everything: there is only one
`0 × n` matrix. -/
theorem discard_after (A : Szabo.Mat K 1 n) : discardMat K * A = 0 := by
  funext i
  exact i.elim0

/-- The projection onto the first of two wires. -/
def projFst (K : Type*) [CommRing K] : Szabo.Mat K 1 2 := !![1, 0]

/-- **Copy then discard one output is a plain wire** (the counit law of the
copy comonoid). -/
theorem copy_discard_counit : projFst K * copyMat K = 1 := by
  funext i j
  fin_cases i
  fin_cases j
  simp [projFst, copyMat, Matrix.mul_apply, Fin.sum_univ_two]

/-- **Transposing exchanges copy and add**: `copyᵀ = add`.  Diagrammatically,
reflecting the copy junction in a vertical mirror gives the add junction — the
formal reason why the two junctions in graphical linear algebra come in mirror
pairs. -/
theorem copyMat_transpose : (copyMat K)ᵀ = addMat K := rfl

theorem addMat_transpose : (addMat K)ᵀ = copyMat K := rfl

end Matrices

end Diagram
