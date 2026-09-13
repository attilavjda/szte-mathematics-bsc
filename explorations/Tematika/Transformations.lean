import Mathlib
import Atlas.Count.Transport
import Atlas.Count.Symmetry

/-!
# Tematika 06 — "Grafikonok vázolása, szimmetria tulajdonságok, monotonitás.
Elemi függvénytranszformációk."

**Syllabus item.**  *Grafikonok vázolása, szimmetria tulajdonságok,
monotonitás.  Elemi függvénytranszformációk.*

**Categorical reading.**

* *Grafikon* — the graph of `f : α → β` is the subobject of `α × β` on which the
  first projection is an isomorphism; "a function is its graph" is the statement
  that graphs are exactly the sections of `pr₁`
  (`Tematika.Transformations.graph_proj_bijective`).
* *Elemi függvénytranszformációk* (shift, stretch, reflect) — the action of a
  **group** on the ambient object, hence a functor from the one-object groupoid
  `B G` into `Set`; a quantity attached to a set is "transformation-invariant"
  exactly when it is a *cocone* under that action, i.e. factors through the
  orbit category.  In the library this is one brick,
  `Atlas.tripleCount_transport`, whose instances are scaling, translation and
  ring automorphism; the affine combination of the first two is
  `Tematika.Transformations.tripleCount_affine`: **the count is invariant under
  the elementary transformations of the graph.**
* *Szimmetria tulajdonságok* — a symmetry is an automorphism of the object in
  question, so symmetries form a group acting on all derived invariants.  The
  library has two: the `S₃`-action permuting the three coordinates of the
  relation (`Atlas.tripleCount_swap₁₂`, `Atlas.tripleCount_swap₂₃`) and the
  **anharmonic group** of order six acting on the slope line by `ρ ↦ ρ⁻¹` and
  `ρ ↦ 1 + ρ` (`Atlas.slopeCount_inv`, `Atlas.slopeCount_one_add`) — the same
  cross-ratio group that Calculus I meets as the symmetries of a graph under
  `x ↦ 1/x` and `x ↦ 1 − x`.  The order-three relation of that group is
  `Tematika.Transformations.anharmonic_cube`.
* *Monotonitás* — a monotone map is precisely a **functor between posets**
  viewed as categories.  The library's count is monotone in its set argument,
  so it *is* a functor `Set M ⥤ ℕ`
  (`Tematika.Transformations.tripleCountFunctor`); enlarging `Δ` can only
  enlarge the count, which is the order-theoretic content behind "Δ is as large
  as possible when it is a half set".
-/

namespace Tematika.Transformations

open CategoryTheory

/-! ### Grafikon: functions are sections of the first projection -/

/-- **A function is its graph.**  The first projection restricted to the graph
of `f` is a bijection; this is what makes "grafikon vázolása" a faithful way to
study a function. -/
theorem graph_proj_bijective {α β : Type*} (f : α → β) :
    Function.Bijective (fun p : {p : α × β // p.2 = f p.1} => p.1.1) := by
  constructor
  · rintro ⟨⟨a, b⟩, hb⟩ ⟨⟨a', b'⟩, hb'⟩ h
    simp only at h
    refine Subtype.ext (Prod.ext_iff.mpr ⟨h, ?_⟩)
    simp only at hb hb' ⊢
    rw [hb, hb', h]
  · intro a
    exact ⟨⟨(a, f a), rfl⟩, rfl⟩

/-! ### Elemi függvénytranszformációk: the affine group acts, the count is invariant -/

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]

/-- **Elemi függvénytranszformáció-invariancia.**  Stretching by a unit and
shifting by a vector — the elementary transformations of a graph — leave the
count unchanged, provided the coefficients sum to zero.  Both halves are
instances of the single transport brick `Atlas.tripleCount_transport`. -/
theorem tripleCount_affine (u : Rˣ) (t : M) {a b c : R} (hsum : a + b + c = 0) (Δ : Set M) :
    Atlas.tripleCount ((fun x => (u : R) • x + t) '' Δ) a b c = Atlas.tripleCount Δ a b c := by
  have himg : (fun x => (u : R) • x + t) '' Δ
      = (fun y => y + t) '' ((fun x => (u : R) • x) '' Δ) := by
    rw [Set.image_image]
  rw [himg, Atlas.tripleCount_translate hsum, Atlas.tripleCount_smul_set]

/-! ### Monotonitás: the count is a functor between posets -/

/-- **Monotonitás.**  The count is monotone in the set argument. -/
theorem tripleCount_mono [Finite M] (a b c : R) :
    Monotone fun Δ : Set M => Atlas.tripleCount Δ a b c := by
  intro Δ Γ hΔΓ
  refine Set.ncard_le_ncard ?_ (Set.toFinite _)
  rintro p ⟨⟨h1, h2, h3⟩, hrel⟩
  exact ⟨⟨hΔΓ h1, hΔΓ h2, hΔΓ h3⟩, hrel⟩

/-- **Monotone = functor.**  The count, read as a functor from the poset of
subsets of `M` to the poset `ℕ`. -/
noncomputable def tripleCountFunctor [Finite M] (a b c : R) : Set M ⥤ ℕ :=
  (tripleCount_mono (M := M) a b c).functor

/-! ### Szimmetria: the anharmonic group of the slope line -/

/-- **The anharmonic symmetry has order three.**  In characteristic two the map
`ρ ↦ (1 + ρ)⁻¹` — the composite of the two symmetries `ρ ↦ ρ⁻¹` and
`ρ ↦ 1 + ρ` under which the count is invariant — is a bijection of order three
on the admissible slopes; together with the involution `ρ ↦ ρ⁻¹` it generates
the order-six anharmonic (cross-ratio) group. -/
theorem anharmonic_cube {K : Type*} [Field K] [CharP K 2] (r : K) (h0 : r ≠ 0) (h1 : r ≠ 1) :
    (1 + (1 + (1 + r)⁻¹)⁻¹)⁻¹ = r := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hs : (1 : K) + r ≠ 0 := by
    intro h
    apply h1
    have h3 : (1 : K) + r + r = 0 + r := by rw [h]
    rw [add_assoc, CharTwo.add_self_eq_zero, add_zero, zero_add] at h3
    exact h3.symm
  have e1 : (1 : K) + (1 + r)⁻¹ = r * (1 + r)⁻¹ := by
    field_simp
    linear_combination h2
  have e2 : (r * (1 + r)⁻¹)⁻¹ = (1 + r) * r⁻¹ := by
    rw [mul_inv, inv_inv]
    ring
  have e3 : (1 : K) + (1 + r) * r⁻¹ = r⁻¹ := by
    field_simp
    linear_combination r * h2
  rw [e1, e2, e3, inv_inv]

end Tematika.Transformations
