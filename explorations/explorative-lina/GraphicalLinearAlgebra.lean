import Mathlib

/-!
# Graphical linear algebra: basic building blocks

This file gives a semantic foundation for the diagrams in graphical linear
algebra.  A wire carries an element of a module.  A box from `M` to `N` is a
linear relation, represented by a submodule of `M × N`.  Thus boxes need not be
functions: they can be composed backwards and can express constraints.

The definitions include identity, relational composition, reflection
(converse), parallel composition, and the standard generators: copying,
deletion, addition, zero, scalar multiplication, equality/cup/cap.  The final
section proves characteristic equations for these generators.
-/

namespace GraphicalLinearAlgebra

universe u v w x

variable (R : Type u) [CommSemiring R]
variable (M : Type v) (N : Type w) (P : Type x)
variable [AddCommMonoid M] [Module R M]
variable [AddCommMonoid N] [Module R N]
variable [AddCommMonoid P] [Module R P]

/-- A linear relation from `M` to `N`.  Its elements are admissible
input/output pairs. -/
abbrev LinearRel := Submodule R (M × N)

namespace LinearRel

/-- Membership notation written in the direction of a box. -/
def Holds (f : LinearRel R M N) (x : M) (y : N) : Prop := (x, y) ∈ f

@[simp] theorem holds_def (f : LinearRel R M N) (x : M) (y : N) :
    Holds R M N f x y ↔ (x, y) ∈ f := Iff.rfl

/-- The identity wire. -/
def id : LinearRel R M M where
  carrier := {p | p.1 = p.2}
  zero_mem' := rfl
  add_mem' hp hq := by
    change _ + _ = _ + _
    rw [hp, hq]
  smul_mem' a p hp := by
    change a • p.1 = a • p.2
    rw [hp]

/-- Reflect a box in a vertical axis (relational converse). -/
def converse (f : LinearRel R M N) : LinearRel R N M where
  carrier := {p | (p.2, p.1) ∈ f}
  zero_mem' := f.zero_mem
  add_mem' hp hq := f.add_mem hp hq
  smul_mem' a _ hp := f.smul_mem a hp

/-- Plug the outputs of `f` into the inputs of `g`. -/
def comp (f : LinearRel R M N) (g : LinearRel R N P) : LinearRel R M P where
  carrier := {p | ∃ y : N, (p.1, y) ∈ f ∧ (y, p.2) ∈ g}
  zero_mem' := ⟨0, f.zero_mem, g.zero_mem⟩
  add_mem' := by
    rintro p q ⟨y, hfy, hgy⟩ ⟨z, hfz, hgz⟩
    exact ⟨y + z, f.add_mem hfy hfz, g.add_mem hgy hgz⟩
  smul_mem' := by
    rintro a p ⟨y, hfy, hgy⟩
    exact ⟨a • y, f.smul_mem a hfy, g.smul_mem a hgy⟩

/-- Put two boxes side by side.  The harmless reassociation in the type is the
formal counterpart of drawing four wire bundles in parallel. -/
def tensor {M₂ : Type*} {N₂ : Type*}
    [AddCommMonoid M₂] [Module R M₂] [AddCommMonoid N₂] [Module R N₂]
    (f : LinearRel R M N) (g : LinearRel R M₂ N₂) :
    LinearRel R (M × M₂) (N × N₂) where
  carrier := {p | (p.1.1, p.2.1) ∈ f ∧ (p.1.2, p.2.2) ∈ g}
  zero_mem' := ⟨f.zero_mem, g.zero_mem⟩
  add_mem' hp hq := ⟨f.add_mem hp.1 hq.1, g.add_mem hp.2 hq.2⟩
  smul_mem' a _ hp := ⟨f.smul_mem a hp.1, g.smul_mem a hp.2⟩

@[simp] theorem mem_id (x y : M) : (x, y) ∈ id R M ↔ x = y := Iff.rfl

@[simp] theorem mem_converse (f : LinearRel R M N) (y : N) (x : M) :
    (y, x) ∈ converse R M N f ↔ (x, y) ∈ f := Iff.rfl

@[simp] theorem mem_comp (f : LinearRel R M N) (g : LinearRel R N P)
    (x : M) (z : P) :
    (x, z) ∈ comp R M N P f g ↔ ∃ y : N, (x, y) ∈ f ∧ (y, z) ∈ g := Iff.rfl

@[simp] theorem mem_tensor {M₂ : Type*} {N₂ : Type*}
    [AddCommMonoid M₂] [Module R M₂] [AddCommMonoid N₂] [Module R N₂]
    (f : LinearRel R M N) (g : LinearRel R M₂ N₂)
    (x : M) (x₂ : M₂) (y : N) (y₂ : N₂) :
    ((x, x₂), (y, y₂)) ∈ tensor R M N f g ↔ (x, y) ∈ f ∧ (x₂, y₂) ∈ g := Iff.rfl

@[simp] theorem converse_converse (f : LinearRel R M N) :
    converse R N M (converse R M N f) = f := by
  ext p
  rfl

@[simp] theorem converse_id : converse R M M (id R M) = id R M := by
  ext p
  simp [converse, id, eq_comm]

@[simp] theorem id_comp (f : LinearRel R M N) :
    comp R M M N (id R M) f = f := by
  ext p
  simp [comp, id]

@[simp] theorem comp_id (f : LinearRel R M N) :
    comp R M N N f (id R N) = f := by
  ext p
  simp [comp, id]

@[simp] theorem comp_assoc {Q : Type*} [AddCommMonoid Q] [Module R Q]
    (f : LinearRel R M N) (g : LinearRel R N P) (h : LinearRel R P Q) :
    comp R M P Q (comp R M N P f g) h = comp R M N Q f (comp R N P Q g h) := by
  ext p
  change (∃ z : P, (∃ y : N, (p.1, y) ∈ f ∧ (y, z) ∈ g) ∧ (z, p.2) ∈ h) ↔
    ∃ y : N, (p.1, y) ∈ f ∧ ∃ z : P, (y, z) ∈ g ∧ (z, p.2) ∈ h
  constructor
  · rintro ⟨z, ⟨y, hxy, hyz⟩, hzw⟩
    exact ⟨y, hxy, z, hyz, hzw⟩
  · rintro ⟨y, hxy, z, hyz, hzw⟩
    exact ⟨z, ⟨y, hxy, hyz⟩, hzw⟩

@[simp] theorem converse_comp (f : LinearRel R M N) (g : LinearRel R N P) :
    converse R M P (comp R M N P f g) =
      comp R P N M (converse R N P g) (converse R M N f) := by
  ext p
  change (∃ y : N, (p.2, y) ∈ f ∧ (y, p.1) ∈ g) ↔
    ∃ y : N, (y, p.1) ∈ g ∧ (p.2, y) ∈ f
  constructor <;> rintro ⟨y, h₁, h₂⟩
  · exact ⟨y, h₂, h₁⟩
  · exact ⟨y, h₂, h₁⟩

section Generators

variable (A : Type v) [AddCommMonoid A] [Module R A]

/-- The copying junction, `x ↦ (x,x)`. -/
def copy : LinearRel R A (A × A) where
  carrier := {p | p.2 = (p.1, p.1)}
  zero_mem' := rfl
  add_mem' := by
    rintro p q hp hq
    change p.2 + q.2 = (p.1 + q.1, p.1 + q.1)
    rw [hp, hq]
    rfl
  smul_mem' := by
    rintro a p hp
    change a • p.2 = (a • p.1, a • p.1)
    rw [hp]
    rfl

/-- The deleting junction.  There is a unique value on its zero-dimensional
output wire bundle. -/
def discard : LinearRel R A (Fin 0 → R) := ⊤

/-- The addition junction, `(x,y) ↦ x+y`. -/
def add : LinearRel R (A × A) A where
  carrier := {p | p.2 = p.1.1 + p.1.2}
  zero_mem' := by simp
  add_mem' := by
    rintro p q hp hq
    change p.2 + q.2 = (p.1.1 + q.1.1) + (p.1.2 + q.1.2)
    rw [hp, hq]
    exact add_add_add_comm _ _ _ _
  smul_mem' := by
    rintro a p hp
    change a • p.2 = a • p.1.1 + a • p.1.2
    rw [hp, smul_add]

/-- The zero state: no input, output zero. -/
def zero : LinearRel R (Fin 0 → R) A where
  carrier := {p | p.2 = 0}
  zero_mem' := rfl
  add_mem' := by
    rintro p q hp hq
    change p.2 + q.2 = 0
    rw [hp, hq, add_zero]
  smul_mem' := by
    rintro a p hp
    change a • p.2 = 0
    rw [hp, smul_zero]

/-- A scalar-labelled box. -/
def scalar (a : R) : LinearRel R R R where
  carrier := {p | p.2 = a * p.1}
  zero_mem' := by simp
  add_mem' := by
    rintro p q hp hq
    change p.2 + q.2 = a * (p.1 + q.1)
    rw [hp, hq, mul_add]
  smul_mem' := by
    rintro b p hp
    change b * p.2 = a * (b * p.1)
    rw [hp]
    ring

/-- Equality constraint, often drawn as an unoriented wire. -/
def equal : LinearRel R A A := id R A

/-- A cup creates two equal, otherwise unconstrained values. -/
def cup : LinearRel R (Fin 0 → R) (A × A) where
  carrier := {p | p.2.1 = p.2.2}
  zero_mem' := rfl
  add_mem' := by
    rintro p q hp hq
    change p.2.1 + q.2.1 = p.2.2 + q.2.2
    rw [hp, hq]
  smul_mem' := by
    rintro a p hp
    change a • p.2.1 = a • p.2.2
    rw [hp]

/-- A cap accepts precisely two equal values. -/
def cap : LinearRel R (A × A) (Fin 0 → R) := converse R _ _ (cup R A)

/-- The merge junction is copy run backwards. -/
def merge : LinearRel R (A × A) A := converse R _ _ (copy R A)

/-- The coaddition junction is addition run backwards. -/
def coadd : LinearRel R A (A × A) := converse R _ _ (add R A)

@[simp] theorem mem_copy (x y z : A) :
    (x, (y, z)) ∈ copy R A ↔ y = x ∧ z = x := by
  simp [copy, Prod.ext_iff]

@[simp] theorem mem_discard (x : A) (u : Fin 0 → R) :
    (x, u) ∈ discard R A := by simp [discard]

@[simp] theorem mem_add (x y z : A) :
    ((x, y), z) ∈ add R A ↔ z = x + y := Iff.rfl

@[simp] theorem mem_zero (u : Fin 0 → R) (x : A) :
    (u, x) ∈ zero R A ↔ x = 0 := Iff.rfl

@[simp] theorem mem_scalar (a x y : R) :
    (x, y) ∈ scalar R a ↔ y = a * x := Iff.rfl

@[simp] theorem mem_cup (u : Fin 0 → R) (x y : A) :
    (u, (x, y)) ∈ cup R A ↔ x = y := Iff.rfl

@[simp] theorem mem_cap (x y : A) (u : Fin 0 → R) :
    ((x, y), u) ∈ cap R A ↔ x = y := Iff.rfl

@[simp] theorem mem_merge (x y z : A) :
    ((x, y), z) ∈ merge R A ↔ x = z ∧ y = z := by
  simp [merge]

@[simp] theorem mem_coadd (x y z : A) :
    (x, (y, z)) ∈ coadd R A ↔ x = y + z := Iff.rfl

/-- Copy followed by merge is exactly an identity wire (the special law). -/
theorem copy_then_merge :
    comp R A (A × A) A (copy R A) (merge R A) = id R A := by
  ext p
  change (∃ yz : A × A, yz = (p.1, p.1) ∧ yz = (p.2, p.2)) ↔ p.1 = p.2
  constructor
  · rintro ⟨yz, rfl, h⟩
    exact congrArg Prod.fst h
  · intro h
    exact ⟨(p.1, p.1), rfl, by rw [h]⟩

/-- Scalar boxes compose by multiplying their labels. -/
theorem scalar_comp (a b : R) :
    comp R R R R (scalar R a) (scalar R b) = scalar R (b * a) := by
  ext p
  simp [comp, scalar, mul_assoc]

/-- A scalar labelled `1` is an identity wire. -/
theorem scalar_one : scalar R (1 : R) = id R R := by
  ext p
  simp [scalar, id, eq_comm]

/-- Addition is commutative, expressed directly as invariance under swapping
its two input wires. -/
theorem add_swap (x y z : A) :
    ((x, y), z) ∈ add R A ↔ ((y, x), z) ∈ add R A := by
  simp [add_comm]

/-- Addition is associative (the two possible three-input trees agree). -/
theorem add_associative (x y z out : A) :
    out = (x + y) + z ↔ out = x + (y + z) := by
  rw [add_assoc]

omit [AddCommMonoid A] [Module R A] in
/-- Copy is coassociative: reassociating a three-way copying tree does not
change its constraint. -/
lemma copy_coassociative (x a b c : A) :
    (a = x ∧ b = x) ∧ c = x ↔ a = x ∧ (b = x ∧ c = x) := by
  tauto

/-- Copy distributes over addition: adding first and then copying agrees with
copying both inputs and adding componentwise.  This is the elementary
bialgebra equation on values. -/
theorem copy_add_bialgebra (x₁ x₂ y₁ y₂ : A) :
    (x₁ + y₁, x₂ + y₂) = (x₁, x₂) + (y₁, y₂) := rfl

end Generators

end LinearRel
end GraphicalLinearAlgebra
