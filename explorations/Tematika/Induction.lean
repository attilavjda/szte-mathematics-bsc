import Mathlib

/-!
# Tematika 02 — "Teljes indukció" (complete induction)

**Syllabus item.**  *Teljes indukció.*

**Categorical reading.**  Induction is the statement that `ℕ`, with the pair
`(0, succ)`, is the **initial algebra of the endofunctor** `F X = 1 ⊕ X` on
`Type` (Lambek).  "Proof by induction" is the uniqueness half of initiality,
"definition by recursion" is the existence half.

**Where the library uses it.**  Through one concrete initial-algebra morphism:
the *Frobenius tower*.  The algebra is the set of ring endomorphisms of `K`
with `zero := id` and `succ := (frobenius ∘ ·)`, and the induced morphism
`ℕ → (K →+* K)` is `iterateFrobenius`, used throughout the library
(`Genesis/Counting/IteratedFrobeniusAutomorphism.lean`,
`Genesis/Curve/IteratedFrobeniusEndomorphism.lean`) whenever a statement is
propagated from `x ↦ x ^ 2` to `x ↦ x ^ (2 ^ k)`.  That every such propagation
is *the* unique morphism out of the initial algebra is
`Tematika.Induction.iterateFrobenius_unique`.
-/

namespace Tematika.Induction

universe u

/-- An algebra for the endofunctor `F X = 1 ⊕ X` of `Type u`: a carrier with a
point and a self-map. -/
structure NatAlgebra where
  carrier : Type u
  zero : carrier
  succ : carrier → carrier

namespace NatAlgebra

/-- The structure map out of `ℕ`, defined by recursion. -/
def iter (A : NatAlgebra.{u}) : ℕ → A.carrier
  | 0 => A.zero
  | n + 1 => A.succ (A.iter n)

@[simp] theorem iter_zero (A : NatAlgebra.{u}) : A.iter 0 = A.zero := rfl

@[simp] theorem iter_succ (A : NatAlgebra.{u}) (n : ℕ) :
    A.iter (n + 1) = A.succ (A.iter n) := rfl

end NatAlgebra

/-- **Teljes indukció = `ℕ` is the initial `1 ⊕ (−)`-algebra.**  For every
algebra there is one and only one algebra morphism out of `ℕ`: existence is
recursion, uniqueness is induction. -/
theorem nat_isInitialAlgebra (A : NatAlgebra.{u}) :
    ∃! f : ℕ → A.carrier, f 0 = A.zero ∧ ∀ n, f (n + 1) = A.succ (f n) := by
  refine ⟨A.iter, ⟨rfl, fun _ => rfl⟩, ?_⟩
  rintro g ⟨h0, hs⟩
  funext n
  induction n with
  | zero => exact h0
  | succ n ih => rw [hs, ih, NatAlgebra.iter_succ]

section Frobenius

variable (K : Type*) [CommRing K] (p : ℕ) [ExpChar K p]

/-- The Frobenius tower as an `F`-algebra: endomorphisms of `K`, based at the
identity, with successor "postcompose with the Frobenius". -/
def frobeniusAlgebra : NatAlgebra where
  carrier := K →+* K
  zero := RingHom.id K
  succ g := (frobenius K p).comp g

@[simp] theorem iterateFrobenius_zero : iterateFrobenius K p 0 = RingHom.id K := by
  ext x; simp

@[simp] theorem iterateFrobenius_succ (n : ℕ) :
    iterateFrobenius K p (n + 1) = (frobenius K p).comp (iterateFrobenius K p n) := by
  ext x
  simp [iterateFrobenius_def, frobenius_def, pow_succ, pow_mul]

/-- **The library's induction, identified.**  `iterateFrobenius` *is* the unique
morphism from the initial algebra `ℕ` to the Frobenius tower: every proof in the
library that propagates a fact from `x ↦ x ^ p` to `x ↦ x ^ (p ^ k)` is an
instance of the universal property `Tematika.Induction.nat_isInitialAlgebra`. -/
theorem iterateFrobenius_unique (f : ℕ → (K →+* K))
    (hf : f 0 = RingHom.id K ∧ ∀ n, f (n + 1) = (frobenius K p).comp (f n)) :
    f = fun n => iterateFrobenius K p n := by
  obtain ⟨g, -, huniq⟩ := nat_isInitialAlgebra (frobeniusAlgebra K p)
  rw [huniq f hf, ← huniq (fun n => iterateFrobenius K p n)
    ⟨iterateFrobenius_zero K p, iterateFrobenius_succ K p⟩]

end Frobenius

end Tematika.Induction
