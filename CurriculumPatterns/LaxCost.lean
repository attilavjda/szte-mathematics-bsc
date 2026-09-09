/-
# One pattern behind two BSc courses: composition carries a cost

This module isolates the single structural fact that the triangle inequality of
*analysis* and the submultiplicativity of the operator norm of *linear algebra*
have in common:

> arrows compose, and a numerical **cost** attached to arrows is *lax*
> for that composition: the cost of a composite is at most the combination of
> the costs.

In categorical language: a lax functor from a category into a one-object
category enriched in an ordered monoid — the situation Lawvere identified when
he read a metric space as a category enriched in `([0, ∞], ≥, +)`.

Nothing here is specific to metrics, norms or determinants; the instances live
in the sibling modules.
-/
import Mathlib

universe u v u' v'

namespace CurriculumPatterns

/-- The raw data underlying a category: objects, arrows, identities and
composition (written in diagrammatic order).  The associativity and unit laws
are deliberately *not* assumed: the cost estimates below never use them, which
is precisely the point of the pearl. -/
structure CompSystem where
  /-- The objects. -/
  Obj : Type u
  /-- The arrows between two objects. -/
  Hom : Obj → Obj → Type v
  /-- The identity arrow at an object. -/
  id : (X : Obj) → Hom X X
  /-- Composition in diagrammatic order: `comp f g` is "first `f`, then `g`". -/
  comp : {X Y Z : Obj} → Hom X Y → Hom Y Z → Hom X Z

namespace CompSystem

/-- The composite `X 0 ⟶ X 1 ⟶ ⋯ ⟶ X n` of a chain of arrows. -/
def chain (C : CompSystem.{u, v}) (X : ℕ → C.Obj)
    (f : (i : ℕ) → C.Hom (X i) (X (i + 1))) :
    (n : ℕ) → C.Hom (X 0) (X n)
  | 0 => C.id (X 0)
  | n + 1 => C.comp (chain C X f n) (f n)

variable (C : CompSystem.{u, v})

@[simp]
theorem chain_zero (X : ℕ → C.Obj) (f : (i : ℕ) → C.Hom (X i) (X (i + 1))) :
    C.chain X f 0 = C.id (X 0) := rfl

@[simp]
theorem chain_succ (X : ℕ → C.Obj) (f : (i : ℕ) → C.Hom (X i) (X (i + 1))) (n : ℕ) :
    C.chain X f (n + 1) = C.comp (C.chain X f n) (f n) := rfl

end CompSystem

/-- The `n`-fold combination `e ⊗ c 0 ⊗ c 1 ⊗ ⋯ ⊗ c (n-1)` of costs, formed with
the same recursion as `CompSystem.chain`. -/
def opChain {M : Type*} (op : M → M → M) (e : M) (c : ℕ → M) : ℕ → M
  | 0 => e
  | n + 1 => op (opChain op e c n) (c n)

@[simp]
theorem opChain_zero {M : Type*} (op : M → M → M) (e : M) (c : ℕ → M) :
    opChain op e c 0 = e := rfl

@[simp]
theorem opChain_succ {M : Type*} (op : M → M → M) (e : M) (c : ℕ → M) (n : ℕ) :
    opChain op e c (n + 1) = op (opChain op e c n) (c n) := rfl

/-- With `op = (+)` and `unit = 0` the combined cost is a finite **sum** — the
shape the estimate takes in analysis. -/
theorem opChain_add {M : Type*} [AddCommMonoid M] (c : ℕ → M) (n : ℕ) :
    opChain (· + ·) 0 c n = ∑ i ∈ Finset.range n, c i := by
  induction n with
  | zero => simp
  | succ n ih => simp [ih, Finset.sum_range_succ]

/-- With `op = (*)` and `unit = 1` the combined cost is a finite **product** — the
shape the estimate takes in linear algebra. -/
theorem opChain_mul {M : Type*} [CommMonoid M] (c : ℕ → M) (n : ℕ) :
    opChain (· * ·) 1 c n = ∏ i ∈ Finset.range n, c i := by
  induction n with
  | zero => simp
  | succ n ih => simp [ih, Finset.prod_range_succ]

/-- A constant multiplicative chain is a power. -/
theorem opChain_mul_const {M : Type*} [CommMonoid M] (a : M) (n : ℕ) :
    opChain (· * ·) 1 (fun _ => a) n = a ^ n := by
  simp [opChain_mul]

/-- A **lax cost** on a composition system `C`: a number `cost f` attached to each
arrow, a monotone combination `op` on the value type, and the two laxness
inequalities.  This is the shared skeleton of

* the triangle inequality (`op = (+)`, `unit = 0`, cost = distance), and
* submultiplicativity of the operator norm (`op = (*)`, `unit = 1`, cost = norm).
-/
structure LaxCost (C : CompSystem.{u, v}) (M : Type*) [Preorder M] where
  /-- How costs of consecutive arrows are combined. -/
  op : M → M → M
  /-- The cost budget of an identity arrow. -/
  unit : M
  /-- `op` is monotone in both arguments. -/
  op_mono : ∀ {a b c d : M}, a ≤ b → c ≤ d → op a c ≤ op b d
  /-- The cost of an arrow. -/
  cost : {X Y : C.Obj} → C.Hom X Y → M
  /-- Identities cost nothing (lax unit). -/
  cost_id : ∀ X : C.Obj, cost (C.id X) ≤ unit
  /-- The cost of a composite is at most the combination of the costs
  (lax composition). -/
  cost_comp : ∀ {X Y Z : C.Obj} (f : C.Hom X Y) (g : C.Hom Y Z),
    cost (C.comp f g) ≤ op (cost f) (cost g)

namespace LaxCost

variable {C : CompSystem.{u, v}} {M : Type*} [Preorder M] (L : LaxCost C M)

/-- **The pearl.**  The cost of a composite chain of arrows is bounded by the
combination of the individual costs.  Proved once, from composition alone; the
triangle-type inequalities of the curriculum are its instances. -/
theorem cost_chain (X : ℕ → C.Obj) (f : (i : ℕ) → C.Hom (X i) (X (i + 1))) (n : ℕ) :
    L.cost (C.chain X f n) ≤ opChain L.op L.unit (fun i => L.cost (f i)) n := by
  induction n with
  | zero => simpa using L.cost_id (X 0)
  | succ n ih =>
      exact le_trans (L.cost_comp _ _) (L.op_mono ih le_rfl)

/-- A cost is **strict** when the two laxness inequalities are equalities, i.e.
when it is an honest functor into the one-object category on `M` rather than a
lax one.  Determinants are strict; distances and operator norms are not. -/
structure IsStrict : Prop where
  /-- Identities cost exactly the unit. -/
  cost_id_eq : ∀ X : C.Obj, L.cost (C.id X) = L.unit
  /-- Composites cost exactly the combination. -/
  cost_comp_eq : ∀ {X Y Z : C.Obj} (f : C.Hom X Y) (g : C.Hom Y Z),
    L.cost (C.comp f g) = L.op (L.cost f) (L.cost g)

/-- For a strict cost the chain estimate is an identity: this is the classical
"multiplicativity" statement (e.g. `det (A₁ ⋯ Aₙ) = det A₁ ⋯ det Aₙ`). -/
theorem cost_chain_eq (h : L.IsStrict) (X : ℕ → C.Obj)
    (f : (i : ℕ) → C.Hom (X i) (X (i + 1))) (n : ℕ) :
    L.cost (C.chain X f n) = opChain L.op L.unit (fun i => L.cost (f i)) n := by
  induction n with
  | zero => simpa using h.cost_id_eq (X 0)
  | succ n ih => rw [CompSystem.chain_succ, h.cost_comp_eq, ih, opChain_succ]

end LaxCost

/-- A morphism of composition systems: the data of a functor (objects, arrows,
preservation of identities and composites). -/
structure CompFunctor (C : CompSystem.{u, v}) (D : CompSystem.{u', v'}) where
  /-- Action on objects. -/
  obj : C.Obj → D.Obj
  /-- Action on arrows. -/
  map : {X Y : C.Obj} → C.Hom X Y → D.Hom (obj X) (obj Y)
  /-- Identities are preserved. -/
  map_id : ∀ X : C.Obj, map (C.id X) = D.id (obj X)
  /-- Composites are preserved. -/
  map_comp : ∀ {X Y Z : C.Obj} (f : C.Hom X Y) (g : C.Hom Y Z),
    map (C.comp f g) = D.comp (map f) (map g)

namespace LaxCost

variable {C : CompSystem.{u, v}} {D : CompSystem.{u', v'}} {M : Type*} [Preorder M]

/-- A lax cost pulls back along a functor: measuring the image of an arrow is
again a lax cost.  This is the sense in which such estimates are *invariants
transported by functors*. -/
def comap (F : CompFunctor C D) (L : LaxCost D M) : LaxCost C M where
  op := L.op
  unit := L.unit
  op_mono := L.op_mono
  cost f := L.cost (F.map f)
  cost_id X := by rw [F.map_id]; exact L.cost_id _
  cost_comp f g := by rw [F.map_comp]; exact L.cost_comp _ _

@[simp]
theorem comap_cost (F : CompFunctor C D) (L : LaxCost D M) {X Y : C.Obj}
    (f : C.Hom X Y) : (L.comap F).cost f = L.cost (F.map f) := rfl

end LaxCost

end CurriculumPatterns
