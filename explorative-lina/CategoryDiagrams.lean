import Mathlib

/-!
# Commutative diagrams: the categorical side of the dictionary

String diagrams (graphical linear algebra, Penrose notation) and commutative
diagrams are two different pictures of the same algebra: a string diagram is
the *Poincaré dual* of a commutative diagram.  Wires become objects, boxes
become morphisms, and "the diagram commutes" becomes "the two ways of plugging
the boxes together are equal".

This file collects the commutative-diagram proofs used in the guide:

* `Diagram.paste_squares` — the pasting lemma: two commuting squares glued
  along an edge give a commuting rectangle.  This is the diagrammatic form of
  associativity, i.e. of Szabó's theorem 2.5(ii);
* `Diagram.inv_unique` — uniqueness of inverses, the diagrammatic form of
  Szabó §4 (`Inverzmátrix`);
* `Diagram.prod_universal`, `Diagram.diag_eq_prod_id`,
  `Diagram.fst_comp_diag` — the product of modules and its universal property,
  which is exactly the **copy junction** of graphical linear algebra: copying
  is the unique map `x ↦ (x,x)` mediating the pair `(id, id)`;
* `Diagram.ker_universal` — the kernel as an equalizer, the categorical form of
  "solve `Ax = 0`";
* `Diagram.quot_triangle`, `Diagram.quot_triangle_unique` — the homomorphism
  theorem as a commuting triangle.
-/

namespace Diagram

open CategoryTheory

/-! ## Abstract commutative diagrams -/

section Abstract

variable {C : Type*} [Category C]

/-- **Pasting lemma.**  Given
```
A --f--> B --g--> Z
|        |        |
a        b        c
v        v        v
A'--f'-> B'--g'-> Z'
```
if the two squares commute then so does the outer rectangle. -/
theorem paste_squares {A B Z A' B' Z' : C}
    (f : A ⟶ B) (g : B ⟶ Z) (f' : A' ⟶ B') (g' : B' ⟶ Z')
    (a : A ⟶ A') (b : B ⟶ B') (c : Z ⟶ Z')
    (hleft : f ≫ b = a ≫ f') (hright : g ≫ c = b ≫ g') :
    (f ≫ g) ≫ c = a ≫ (f' ≫ g') := by
  rw [Category.assoc, hright, ← Category.assoc, hleft, Category.assoc]

/-- A commuting triangle composed with a further morphism still commutes. -/
theorem paste_triangle {A B Z W : C} (f : A ⟶ B) (g : B ⟶ Z) (h : A ⟶ Z) (k : Z ⟶ W)
    (hcomm : f ≫ g = h) : f ≫ (g ≫ k) = h ≫ k := by
  rw [← Category.assoc, hcomm]

/-- **Inverses are unique**: if `g` and `g'` are both two-sided inverses of `f`
then they are equal.  Drawn as diagrams this is the "yanking" computation
`g = g (f g') = (g f) g' = g'`. -/
theorem inv_unique {A B : C} (f : A ⟶ B) (g g' : B ⟶ A)
    (hg : f ≫ g = 𝟙 A) (hg' : g' ≫ f = 𝟙 B) : g = g' := by
  calc g = 𝟙 B ≫ g := by rw [Category.id_comp]
    _ = (g' ≫ f) ≫ g := by rw [hg']
    _ = g' ≫ (f ≫ g) := by rw [Category.assoc]
    _ = g' ≫ 𝟙 A := by rw [hg]
    _ = g' := by rw [Category.comp_id]

end Abstract

/-! ## Products of modules: the copy junction as a universal property -/

section Products

variable {R M N P : Type*} [CommRing R]
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable [AddCommGroup P] [Module R P]

/-- **Universal property of the product.**  A map into `M × N` is exactly a
pair of maps, and the mediating map is unique: the two projections and
`LinearMap.prod` form a limit cone. -/
theorem prod_universal (f : P →ₗ[R] M) (g : P →ₗ[R] N) :
    ∃! h : P →ₗ[R] M × N,
      (LinearMap.fst R M N).comp h = f ∧ (LinearMap.snd R M N).comp h = g := by
  refine ⟨f.prod g, ⟨rfl, rfl⟩, ?_⟩
  rintro h ⟨hf, hg⟩
  ext x
  · exact congrArg (fun k : P →ₗ[R] M => k x) hf
  · exact congrArg (fun k : P →ₗ[R] N => k x) hg

/-- The **copy junction** `x ↦ (x, x)` is the mediating map of the pair
`(id, id)`. -/
theorem diag_eq_prod_id (x : M) :
    ((LinearMap.id : M →ₗ[R] M).prod (LinearMap.id : M →ₗ[R] M)) x = (x, x) := rfl

/-- **Counit law for copy**: copying and then discarding one output is the
identity wire. -/
theorem fst_comp_diag :
    (LinearMap.fst R M M).comp ((LinearMap.id : M →ₗ[R] M).prod LinearMap.id) =
      LinearMap.id := rfl

/-- **Cocommutativity of copy**: swapping the two outputs of the copy junction
changes nothing. -/
theorem diag_comm (x : M) :
    (Prod.swap (((LinearMap.id : M →ₗ[R] M).prod LinearMap.id) x)) =
      ((LinearMap.id : M →ₗ[R] M).prod LinearMap.id) x := rfl

/-- **Coassociativity of copy**: the two ways of copying a wire three times
agree. -/
theorem diag_assoc (x : M) :
    (((LinearMap.id : M →ₗ[R] M).prod LinearMap.id).prod (LinearMap.id : M →ₗ[R] M)) x
        = ((x, x), x) ∧
      ((LinearMap.id : M →ₗ[R] M).prod
        ((LinearMap.id : M →ₗ[R] M).prod (LinearMap.id : M →ₗ[R] M))) x = (x, (x, x)) :=
  ⟨rfl, rfl⟩

/-- **The add junction** `(x, y) ↦ x + y` is the codiagonal, the mediating map
out of the coproduct for the pair `(id, id)`. -/
theorem coprod_universal (f : M →ₗ[R] P) (g : N →ₗ[R] P) :
    ∃! h : M × N →ₗ[R] P,
      h.comp (LinearMap.inl R M N) = f ∧ h.comp (LinearMap.inr R M N) = g := by
  refine ⟨f.coprod g, ⟨by ext x; simp, by ext x; simp⟩, ?_⟩
  rintro h ⟨hf, hg⟩
  refine LinearMap.ext fun p => ?_
  have hx : h (p.1, 0) = f p.1 := congrArg (fun k : M →ₗ[R] P => k p.1) hf
  have hy : h (0, p.2) = g p.2 := congrArg (fun k : N →ₗ[R] P => k p.2) hg
  have hp : p = ((p.1, 0) + (0, p.2) : M × N) := by simp
  rw [hp, map_add, hx, hy]
  simp

/-- Copy followed by add is multiplication by `2` — the same computation as
`Diagram.add_after_copy` in matrix form. -/
theorem add_after_copy_map (x : M) :
    (LinearMap.id.coprod LinearMap.id : M × M →ₗ[R] M)
      (((LinearMap.id : M →ₗ[R] M).prod LinearMap.id) x) = x + x := rfl

end Products

/-! ## Kernels as equalizers, and the homomorphism theorem as a triangle -/

section Kernels

variable {R M N P : Type*} [CommRing R]
variable [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
variable [AddCommGroup P] [Module R P]

/-- **The kernel is an equalizer.**  Any map killed by `f` factors uniquely
through `ker f`.  This is the categorical statement of "the solution set of
`Ax = 0`". -/
theorem ker_universal (f : M →ₗ[R] N) (u : P →ₗ[R] M) (hu : f.comp u = 0) :
    ∃! v : P →ₗ[R] (LinearMap.ker f), (LinearMap.ker f).subtype.comp v = u := by
  refine ⟨u.codRestrict (LinearMap.ker f) (fun x => ?_), ?_, ?_⟩
  · have : f (u x) = 0 := congrArg (fun k : P →ₗ[R] N => k x) hu
    simpa [LinearMap.mem_ker] using this
  · ext x; rfl
  · intro w hw
    ext x
    have := congrArg (fun k : P →ₗ[R] M => k x) hw
    simpa [Subtype.ext_iff] using this

/-- **The homomorphism theorem as a commuting triangle.**  The map induced on
the quotient by the kernel makes the triangle
`M → M ⧸ ker f → N` commute. -/
theorem quot_triangle (f : M →ₗ[R] N) :
    ((LinearMap.ker f).liftQ f le_rfl).comp (LinearMap.ker f).mkQ = f :=
  (LinearMap.ker f).liftQ_mkQ f le_rfl

/-- ... and it is the unique such map: the quotient projection is an
epimorphism. -/
theorem quot_triangle_unique (f : M →ₗ[R] N)
    (g : (M ⧸ LinearMap.ker f) →ₗ[R] N) (hg : g.comp (LinearMap.ker f).mkQ = f) :
    g = (LinearMap.ker f).liftQ f le_rfl := by
  refine (LinearMap.ker f).linearMap_qext ?_
  rw [hg, quot_triangle]

end Kernels

end Diagram
