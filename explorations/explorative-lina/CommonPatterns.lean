import Mathlib

/-!
# The common patterns of graphical linear algebra, a linear algebra course, and category theory

This file isolates, and proves, the handful of *patterns* that the three
subjects share.  Each section is one row of the dictionary table in
`patterns.tex`:

| pattern | picture | textbook | category theory |
| --- | --- | --- | --- |
| composition is associative and unital | plugging wires end to end | `(AB)C = A(BC)`, `IA = A` | a category |
| a functor preserves composition | reading a diagram as a matrix | the matrix of a composite is the product | functoriality of `LinearMap.toMatrix` |
| the interchange law | a diagram has no reading order | `(A ⊗ B)(C ⊗ D) = AC ⊗ BD` | bifunctoriality of `⊗` |
| universal property | a box with a unique filler | extend a map linearly from a basis | free object / left adjoint |
| bending a wire | turn an input into an output | `⟪Ax, y⟫ = ⟪x, Aᵀy⟫` | compact closedness / duality |
| a partition of the identity | cutting a wire into strands | `A = ∑ aᵢⱼ Eᵢⱼ` | a biproduct decomposition |
| change of coordinates | redrawing the same diagram | similar matrices | naturality / conjugation |
| a fibration into parallel slices | a tiling of the domain | solution set = particular + kernel | exactness, cokernels |

Everything here is stated for honest linear algebra (matrices and linear maps
over a commutative ring or a field), so the pictures in the note are backed by
theorems and not by analogy alone.
-/

namespace Patterns

open Matrix
open scoped BigOperators Kronecker

/-! ## Pattern 1: composition is associative and unital (the *category* pattern)

Diagrammatically: wires plug together, and a bare wire changes nothing.  There
are no brackets in a picture, which is exactly why associativity may be left
implicit.  -/

section Category

variable {R : Type*} [CommSemiring R]
variable {M N P Q : Type*}
variable [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
variable [AddCommMonoid P] [Module R P] [AddCommMonoid Q] [Module R Q]

/-- Plugging three diagrams together in series: no brackets are needed. -/
theorem series_assoc (f : M →ₗ[R] N) (g : N →ₗ[R] P) (h : P →ₗ[R] Q) :
    (h ∘ₗ g) ∘ₗ f = h ∘ₗ (g ∘ₗ f) := rfl

/-- A bare wire is a unit for plugging. -/
theorem bare_wire_left (f : M →ₗ[R] N) : LinearMap.id ∘ₗ f = f := rfl

theorem bare_wire_right (f : M →ₗ[R] N) : f ∘ₗ LinearMap.id = f := rfl

/-- The same pattern one level down, for matrices: this is the associativity that a
linear algebra course proves by exchanging two summation signs. -/
theorem matrix_series_assoc {l m n p : Type*} [Fintype m] [Fintype n]
    (A : Matrix l m R) (B : Matrix m n R) (C : Matrix n p R) :
    A * B * C = A * (B * C) := Matrix.mul_assoc A B C

end Category

/-! ## Pattern 2: functoriality (choose a basis, get a matrix)

"The matrix of a composite is the product of the matrices" is the statement
that `toMatrix` is a functor; diagrammatically it says that a picture may be
evaluated box by box. -/

section Functor

variable {R : Type*} [CommRing R]
variable {M N P : Type*}
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable [AddCommGroup P] [Module R P]
variable {ι κ μ : Type*} [Fintype ι] [Fintype κ] [Fintype μ]
variable [DecidableEq ι] [DecidableEq κ]

/-- Functoriality on arrows. -/
theorem toMatrix_series (b : Module.Basis ι R M) (c : Module.Basis κ R N)
    (d : Module.Basis μ R P) (f : M →ₗ[R] N) (g : N →ₗ[R] P) :
    LinearMap.toMatrix b d (g ∘ₗ f)
      = LinearMap.toMatrix c d g * LinearMap.toMatrix b c f :=
  LinearMap.toMatrix_comp b c d g f

/-- Functoriality on identities: a bare wire becomes the identity matrix. -/
theorem toMatrix_bare_wire (b : Module.Basis ι R M) :
    LinearMap.toMatrix b b (LinearMap.id : M →ₗ[R] M) = 1 :=
  LinearMap.toMatrix_id b

end Functor

/-! ## Pattern 3: the interchange law (a diagram has no reading order)

If two boxes are drawn side by side, it does not matter whether one first
composes horizontally or vertically.  In a course this is the mixed product
rule for the Kronecker product; in category theory it is the fact that `⊗` is a
bifunctor; in a picture it is *planar isotopy*. -/

section Interchange

variable {R : Type*} [CommSemiring R]

/-- Interchange for the direct sum ("stack two wires"): first stack, then compose,
equals first compose, then stack. -/
theorem interchange_prod {M M' N N' P P' : Type*}
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    [AddCommMonoid P] [Module R P] [AddCommMonoid M'] [Module R M']
    [AddCommMonoid N'] [Module R N'] [AddCommMonoid P'] [Module R P']
    (f : M →ₗ[R] N) (g : N →ₗ[R] P) (f' : M' →ₗ[R] N') (g' : N' →ₗ[R] P') :
    (g.prodMap g') ∘ₗ (f.prodMap f') = (g ∘ₗ f).prodMap (g' ∘ₗ f') :=
  LinearMap.prodMap_comp f g f' g'

/-- Interchange for the tensor (Kronecker) product of matrices. -/
theorem interchange_kronecker {l m n l' m' n' : Type*} [Fintype m] [Fintype m']
    (A : Matrix l m R) (B : Matrix m n R) (A' : Matrix l' m' R) (B' : Matrix m' n' R) :
    (A * B) ⊗ₖ (A' * B') = (A ⊗ₖ A') * (B ⊗ₖ B') :=
  Matrix.mul_kronecker_mul A B A' B'

/-- Sliding a box past a bare wire: the special case of interchange in which one of
the two columns is empty.  This is the move that makes a picture two-dimensional. -/
theorem slide_past_wire {M M' N N' : Type*}
    [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
    [AddCommMonoid M'] [Module R M'] [AddCommMonoid N'] [Module R N']
    (f : M →ₗ[R] N) (g : M' →ₗ[R] N') :
    (f.prodMap LinearMap.id) ∘ₗ (LinearMap.id.prodMap g)
      = (LinearMap.id.prodMap g) ∘ₗ (f.prodMap LinearMap.id) := by
  ext x <;> simp

end Interchange

/-! ## Pattern 4: universal properties (say it on generators, get it everywhere)

Every "define a linear map by its values on a basis" exercise is the universal
property of a free module: a unique filler for a diagram. -/

section Universal

variable {R : Type*} [CommSemiring R] {M N : Type*}
variable [AddCommMonoid M] [Module R M] [AddCommMonoid N] [Module R N]
variable {ι : Type*}

/-- The free/universal pattern: a family of values on a basis extends to a linear
map in exactly one way. -/
theorem unique_extension_from_basis (b : Module.Basis ι R M) (v : ι → N) :
    ∃! f : M →ₗ[R] N, ∀ i, f (b i) = v i := by
  refine ⟨b.constr R v, fun i => b.constr_basis R v i, ?_⟩
  intro g hg
  refine b.ext fun i => ?_
  rw [hg i, b.constr_basis]

/-- The uniqueness half on its own: two linear maps agreeing on a basis are equal.
This is the reason a diagram may be checked on generators. -/
theorem eq_of_eq_on_basis (b : Module.Basis ι R M) {f g : M →ₗ[R] N}
    (h : ∀ i, f (b i) = g (b i)) : f = g := b.ext h

end Universal

/-! ## Pattern 5: bending a wire (duality, transposes, adjoints)

Turning an input into an output is the same operation as transposing a matrix.
In category theory it is compact closedness; in a course it is the defining
property of the transpose with respect to the dot product. -/

section Duality

variable {R : Type*} [CommRing R] {m n : Type*}

/-- Bending a leg: `⟪Ax, y⟫ = ⟪x, Aᵀy⟫`. -/
theorem bend_wire [Fintype m] [Fintype n] (A : Matrix m n R) (x : n → R) (y : m → R) :
    (A *ᵥ x) ⬝ᵥ y = x ⬝ᵥ (Aᵀ *ᵥ y) := by
  rw [dotProduct_comm, dotProduct_mulVec, dotProduct_comm, mulVec_transpose]

omit [CommRing R] in
/-- Bending twice is the identity: the "snake" / zig-zag equation in its matrix form. -/
theorem bend_twice (A : Matrix m n R) : Aᵀᵀ = A := Matrix.transpose_transpose A

/-- Reversing a series of boxes when all the wires are bent. -/
theorem bend_series {l : Type*} [Fintype m] (A : Matrix l m R) (B : Matrix m n R) :
    (A * B)ᵀ = Bᵀ * Aᵀ := Matrix.transpose_mul A B

end Duality

/-! ## Pattern 6: a partition of the identity (cutting a wire into strands)

`∑ᵢ Eᵢᵢ = 1` is a tiling of the identity matrix by its diagonal cells, and
`A = ∑ᵢⱼ aᵢⱼEᵢⱼ` tiles an arbitrary matrix by rank-one pieces.  This is the
computational content of "choose a basis". -/

section Partition

variable {R : Type*} [CommRing R] {m n : Type*} [Fintype m] [Fintype n]
variable [DecidableEq m] [DecidableEq n]

/-- The diagonal cells tile the identity. -/
theorem identity_is_tiled : ∑ i : m, Matrix.single i i (1 : R) = 1 :=
  Matrix.sum_single_one

/-- Every matrix is tiled by its cells: the picture is a grid, the algebra is a
double sum of rank-one pieces. -/
theorem matrix_is_tiled (A : Matrix m n R) :
    A = ∑ i : m, ∑ j : n, Matrix.single i j (A i j) :=
  Matrix.matrix_eq_sum_single A

/-- Reassembling a vector from its coordinates: the same tiling, one dimension down. -/
theorem vector_is_tiled (x : n → R) : x = ∑ j : n, x j • (Pi.single j (1 : R) : n → R) := by
  funext i
  simp [Finset.sum_apply, Pi.single_apply]

end Partition

/-! ## Pattern 7: a fibration into parallel slices (the tiling of the domain)

The fibres of a linear map are the translates of its kernel: the domain is
*tiled* by parallel copies of one subspace, and the tiles are indexed by the
image.  Every "the solution set of `Ax = b` is a particular solution plus the
homogeneous solutions" exercise is this picture, and rank–nullity is the
statement that the dimensions add up. -/

section Fibres

variable {K : Type*} [Field K] {V W : Type*}
variable [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]

/-- Each fibre is a translate of the kernel: one tile, moved. -/
theorem fibre_eq_kernel_translate (f : V →ₗ[K] W) (a : V) :
    {x : V | f x = f a} = (fun k => a + k) '' (LinearMap.ker f : Set V) := by
  ext x
  constructor
  · intro hx
    refine ⟨x - a, ?_, by simp⟩
    simpa [LinearMap.mem_ker, sub_eq_zero] using hx
  · rintro ⟨k, hk, rfl⟩
    have : f k = 0 := hk
    simp [this]

/-- The tiles are disjoint or equal: two fibres either coincide or do not meet. -/
theorem fibres_disjoint_or_equal (f : V →ₗ[K] W) (a b : V) :
    {x : V | f x = f a} = {x : V | f x = f b} ∨
      Disjoint {x : V | f x = f a} {x : V | f x = f b} := by
  by_cases h : f a = f b
  · left; simp [h]
  · right
    rw [Set.disjoint_left]
    intro x hx hx'
    exact h (hx.symm.trans hx')

/-- The tiles cover the domain. -/
theorem fibres_cover (f : V →ₗ[K] W) (x : V) : x ∈ {y : V | f y = f x} := rfl

/-- Rank–nullity: counting the tiles times the size of a tile.  `dim (image)` counts
the tiles, `dim (kernel)` measures one tile. -/
theorem tiles_times_tile [FiniteDimensional K V] (f : V →ₗ[K] W) :
    Module.finrank K (LinearMap.range f) + Module.finrank K (LinearMap.ker f)
      = Module.finrank K V :=
  LinearMap.finrank_range_add_finrank_ker f

/-- The solution set of an inhomogeneous system is one tile: a particular solution
translated by the kernel. -/
theorem solution_set_is_a_tile (f : V →ₗ[K] W) (b : W) (a : V) (ha : f a = b) :
    {x : V | f x = b} = (fun k => a + k) '' (LinearMap.ker f : Set V) := by
  rw [← ha]; exact fibre_eq_kernel_translate f a

end Fibres

/-! ## Pattern 8: change of coordinates (the same picture, redrawn)

Conjugation by an invertible matrix is what happens to a box when the wires are
relabelled.  The invariants of the picture (trace, determinant, rank,
characteristic polynomial) are exactly the quantities that survive it; see
`RequestProject/TraceLoop.lean` for the trace. -/

section ChangeOfBasis

variable {R : Type*} [CommRing R] {M N : Type*}
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable {ι ι' κ κ' : Type*}
variable [Fintype ι] [Fintype ι'] [Fintype κ] [Fintype κ']
variable [DecidableEq ι] [DecidableEq ι']

/-- Redrawing a diagram with different labels conjugates its matrix. -/
theorem change_of_basis (b : Module.Basis ι R M) (b' : Module.Basis ι' R M)
    (c : Module.Basis κ R N) (c' : Module.Basis κ' R N) (f : M →ₗ[R] N) :
    c.toMatrix c' * LinearMap.toMatrix b' c' f * b'.toMatrix b = LinearMap.toMatrix b c f :=
  basis_toMatrix_mul_linearMap_toMatrix_mul_basis_toMatrix b b' c c' f

end ChangeOfBasis

end Patterns
