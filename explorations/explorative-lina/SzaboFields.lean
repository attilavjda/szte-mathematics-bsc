import Mathlib

/-!
# Szabó, §1: scalars ("számtest") and the summation conventions

This file formalises the first section of L. Szabó, *Bevezetés a lineáris
algebrába*.  The text fixes its scalars once and for all: a **számtest**
(number field) is a subset of `ℂ` with at least two elements that is closed
under the four basic operations.

We record

* `Szabo.NumTest`  — the structure of §1.1;
* `Szabo.NumTest.toSubfield` — every number field is a subfield of `ℂ`;
* `Szabo.NumTest.rat_mem` — every number field contains `ℚ` (§1, remark);
* `Szabo.numTestQ`, `Szabo.numTestRatSqrtTwo` — the examples `ℚ` and
  `{a + b√2 : a, b ∈ ℚ}`;
* the two summation facts used throughout the notes: exchanging the order of a
  double sum, and the convention that an empty sum is `0` and an empty product
  is `1`.

Everything below is the *semantic* layer that the diagrammatic guide
(`guide.tex`) draws pictures for: a wire in a string diagram carries an element
of a module over such a scalar field.
-/

namespace Szabo

open scoped BigOperators

/-- §1.1 Definíció.  A *számtest* (number field) is a subset of `ℂ` with at
least two elements which is closed under addition, subtraction, multiplication
and division by nonzero elements. -/
structure NumTest where
  /-- The underlying set of scalars. -/
  carrier : Set ℂ
  /-- It has at least two elements. -/
  nontrivial' : ∃ x ∈ carrier, ∃ y ∈ carrier, x ≠ y
  add_mem' : ∀ ⦃x⦄, x ∈ carrier → ∀ ⦃y⦄, y ∈ carrier → x + y ∈ carrier
  sub_mem' : ∀ ⦃x⦄, x ∈ carrier → ∀ ⦃y⦄, y ∈ carrier → x - y ∈ carrier
  mul_mem' : ∀ ⦃x⦄, x ∈ carrier → ∀ ⦃y⦄, y ∈ carrier → x * y ∈ carrier
  div_mem' : ∀ ⦃x⦄, x ∈ carrier → ∀ ⦃y⦄, y ∈ carrier → y ≠ 0 → x / y ∈ carrier

namespace NumTest

instance : Membership ℂ NumTest := ⟨fun T x => x ∈ T.carrier⟩

@[simp] theorem mem_carrier {T : NumTest} {x : ℂ} : x ∈ T.carrier ↔ x ∈ T := Iff.rfl

variable (T : NumTest)

theorem add_mem {x y : ℂ} (hx : x ∈ T) (hy : y ∈ T) : x + y ∈ T := T.add_mem' hx hy
theorem sub_mem {x y : ℂ} (hx : x ∈ T) (hy : y ∈ T) : x - y ∈ T := T.sub_mem' hx hy
theorem mul_mem {x y : ℂ} (hx : x ∈ T) (hy : y ∈ T) : x * y ∈ T := T.mul_mem' hx hy
theorem div_mem {x y : ℂ} (hx : x ∈ T) (hy : y ∈ T) (hy0 : y ≠ 0) : x / y ∈ T :=
  T.div_mem' hx hy hy0

/-- A number field contains `0`: subtract an element from itself. -/
theorem zero_mem : (0 : ℂ) ∈ T := by
  obtain ⟨x, hx, _⟩ := T.nontrivial'
  simpa using T.sub_mem hx hx

/-- A number field contains a nonzero element (this is the point of asking for
two elements). -/
theorem exists_ne_zero : ∃ x ∈ T, x ≠ (0 : ℂ) := by
  obtain ⟨x, hx, y, hy, hxy⟩ := T.nontrivial'
  by_cases hx0 : x = 0
  · exact ⟨y, hy, by rintro rfl; exact hxy (by simp [hx0])⟩
  · exact ⟨x, hx, hx0⟩

/-- "Minden számtest tartalmaz 0-tól különböző elemet, amit önmagával elosztva
1-et kapunk": a number field contains `1`. -/
theorem one_mem : (1 : ℂ) ∈ T := by
  obtain ⟨x, hx, hx0⟩ := T.exists_ne_zero
  simpa [div_self hx0] using T.div_mem hx hx hx0

theorem neg_mem {x : ℂ} (hx : x ∈ T) : -x ∈ T := by
  simpa using T.sub_mem T.zero_mem hx

theorem inv_mem {x : ℂ} (hx : x ∈ T) (hx0 : x ≠ 0) : x⁻¹ ∈ T := by
  simpa [one_div] using T.div_mem T.one_mem hx hx0

/-- Every number field is a subfield of `ℂ` in the sense of Mathlib. -/
def toSubfield : Subfield ℂ where
  carrier := T.carrier
  mul_mem' := T.mul_mem
  one_mem' := T.one_mem
  add_mem' := T.add_mem
  zero_mem' := T.zero_mem
  neg_mem' := T.neg_mem
  inv_mem' := by
    intro x hx
    by_cases hx0 : x = 0
    · simpa [hx0] using T.zero_mem
    · exact T.inv_mem hx hx0

@[simp] theorem mem_toSubfield {x : ℂ} : x ∈ T.toSubfield ↔ x ∈ T := Iff.rfl

theorem natCast_mem (n : ℕ) : (n : ℂ) ∈ T :=
  _root_.natCast_mem T.toSubfield n

theorem intCast_mem (n : ℤ) : (n : ℂ) ∈ T :=
  _root_.intCast_mem T.toSubfield n

/-- §1: "Tehát minden számtest tartalmazza a racionális számok ℚ halmazát." -/
theorem rat_mem (q : ℚ) : (q : ℂ) ∈ T :=
  SubfieldClass.ratCast_mem T.toSubfield q

/-- A number field is closed under finite sums. -/
theorem sum_mem {ι : Type*} {s : Finset ι} {f : ι → ℂ} (hf : ∀ i ∈ s, f i ∈ T) :
    (∑ i ∈ s, f i) ∈ T := by
  simpa using Subfield.sum_mem T.toSubfield (by simpa using hf)

/-- A number field is closed under finite products. -/
theorem prod_mem {ι : Type*} {s : Finset ι} {f : ι → ℂ} (hf : ∀ i ∈ s, f i ∈ T) :
    (∏ i ∈ s, f i) ∈ T := by
  simpa using Subfield.prod_mem T.toSubfield (by simpa using hf)

end NumTest

/-! ### The examples of §1 -/

/-- The rational numbers form a number field. -/
def numTestQ : NumTest where
  carrier := Set.range ((↑) : ℚ → ℂ)
  nontrivial' := ⟨0, ⟨0, by simp⟩, 1, ⟨1, by simp⟩, by norm_num⟩
  add_mem' := by rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩; exact ⟨a + b, by push_cast; ring⟩
  sub_mem' := by rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩; exact ⟨a - b, by push_cast; ring⟩
  mul_mem' := by rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩; exact ⟨a * b, by push_cast; ring⟩
  div_mem' := by rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ _; exact ⟨a / b, by push_cast; ring⟩

/-- `√2` viewed as a complex number. -/
noncomputable def sqrtTwoC : ℂ := ((Real.sqrt 2 : ℝ) : ℂ)

theorem sqrtTwoC_sq : sqrtTwoC * sqrtTwoC = 2 := by
  have h : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  rw [sqrtTwoC, ← Complex.ofReal_mul, h]
  norm_num

/-- No rational number squares to `2`. -/
theorem rat_sq_ne_two (q : ℚ) : (q : ℝ) ^ 2 ≠ 2 := by
  intro h
  have h1 : Real.sqrt 2 = |(q : ℝ)| := by rw [← h, Real.sqrt_sq_eq_abs]
  exact irrational_sqrt_two ⟨|q|, by simpa using h1.symm⟩

/-- `c² = 2d²` forces `c = d = 0` over `ℚ`. -/
theorem rat_sq_two_eq_zero {c d : ℚ} (h : c ^ 2 - 2 * d ^ 2 = 0) : c = 0 ∧ d = 0 := by
  rcases eq_or_ne d 0 with rfl | hd
  · refine ⟨?_, rfl⟩
    have : c ^ 2 = 0 := by linarith
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
  · exfalso
    have hd' : (d : ℝ) ≠ 0 := by exact_mod_cast hd
    have hr : (c : ℝ) ^ 2 - 2 * (d : ℝ) ^ 2 = 0 := by exact_mod_cast h
    refine rat_sq_ne_two (c / d) ?_
    push_cast
    field_simp
    linarith

/-- The set `{a + b√2 : a, b ∈ ℚ}`, the last example of §1. -/
def qSqrtTwo : Set ℂ := {z : ℂ | ∃ a b : ℚ, z = (a : ℂ) + (b : ℂ) * sqrtTwoC}

/-- An element of `ℚ(√2)` vanishes only if both rational coordinates vanish. -/
theorem qSqrtTwo_eq_zero {a b : ℚ} (h : (a : ℂ) + (b : ℂ) * sqrtTwoC = 0) :
    a = 0 ∧ b = 0 := by
  have hreal : (a : ℝ) + (b : ℝ) * Real.sqrt 2 = 0 := by
    have := congrArg Complex.re h
    simpa [sqrtTwoC] using this
  have hb : b = 0 := by
    by_contra hb
    have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast hb
    have hsqrt : Real.sqrt 2 = ((-a / b : ℚ) : ℝ) := by
      push_cast
      field_simp
      linarith
    have h2 : ((-a / b : ℚ) : ℝ) ^ 2 = 2 := by
      rw [← hsqrt, Real.sq_sqrt (by norm_num : (2 : ℝ) ≥ 0)]
    exact rat_sq_ne_two _ h2
  refine ⟨?_, hb⟩
  subst hb
  have : (a : ℂ) = 0 := by simpa using h
  exact_mod_cast this

theorem qSqrtTwo_mul_mem {x y : ℂ} (hx : x ∈ qSqrtTwo) (hy : y ∈ qSqrtTwo) :
    x * y ∈ qSqrtTwo := by
  obtain ⟨a, b, rfl⟩ := hx
  obtain ⟨c, d, rfl⟩ := hy
  refine ⟨a * c + 2 * (b * d), a * d + b * c, ?_⟩
  push_cast
  linear_combination ((b : ℂ) * d) * sqrtTwoC_sq

theorem qSqrtTwo_inv_mem {x : ℂ} (hx : x ∈ qSqrtTwo) (hx0 : x ≠ 0) : x⁻¹ ∈ qSqrtTwo := by
  obtain ⟨c, d, rfl⟩ := hx
  have hK : (c ^ 2 - 2 * d ^ 2 : ℚ) ≠ 0 := by
    intro h
    obtain ⟨rfl, rfl⟩ := rat_sq_two_eq_zero h
    exact hx0 (by simp)
  have hKC : ((c : ℂ) ^ 2 - 2 * (d : ℂ) ^ 2) ≠ 0 := by
    have : ((c ^ 2 - 2 * d ^ 2 : ℚ) : ℂ) ≠ 0 := by exact_mod_cast hK
    push_cast at this
    exact this
  have hKC' : ((c ^ 2 - 2 * d ^ 2 : ℚ) : ℂ) ≠ 0 := by exact_mod_cast hK
  have hconj : ((c : ℂ) + (d : ℂ) * sqrtTwoC) * ((c : ℂ) - (d : ℂ) * sqrtTwoC)
      = ((c ^ 2 - 2 * d ^ 2 : ℚ) : ℂ) := by
    push_cast
    linear_combination (-(d : ℂ) ^ 2) * sqrtTwoC_sq
  have key : ((c : ℂ) + (d : ℂ) * sqrtTwoC) *
      (((c : ℂ) - (d : ℂ) * sqrtTwoC) / ((c ^ 2 - 2 * d ^ 2 : ℚ) : ℂ)) = 1 := by
    rw [mul_div_assoc', hconj, div_self hKC']
  refine ⟨c / (c ^ 2 - 2 * d ^ 2), -d / (c ^ 2 - 2 * d ^ 2), ?_⟩
  rw [inv_eq_of_mul_eq_one_right key]
  push_cast
  field_simp
  ring

/-- `{a + b√2 : a, b ∈ ℚ}` is a number field. -/
noncomputable def numTestRatSqrtTwo : NumTest where
  carrier := qSqrtTwo
  nontrivial' := ⟨0, ⟨0, 0, by simp⟩, 1, ⟨1, 0, by simp⟩, by norm_num⟩
  add_mem' := by
    rintro _ ⟨a, b, rfl⟩ _ ⟨c, d, rfl⟩
    exact ⟨a + c, b + d, by push_cast; ring⟩
  sub_mem' := by
    rintro _ ⟨a, b, rfl⟩ _ ⟨c, d, rfl⟩
    exact ⟨a - c, b - d, by push_cast; ring⟩
  mul_mem' := fun _ hx _ hy => qSqrtTwo_mul_mem hx hy
  div_mem' := by
    intro x hx y hy hy0
    rw [div_eq_mul_inv]
    exact qSqrtTwo_mul_mem hx (qSqrtTwo_inv_mem hy hy0)

/-! ### The two summation conventions of §1

Both are the diagrammatic content of "a bunch of wires plugged into one
addition node": the order in which a rectangular array is summed is irrelevant,
and an empty bundle of wires carries the unit of the operation. -/

/-- Summing a rectangular array by rows or by columns gives the same result. -/
theorem sum_sum_comm {T : Type*} [AddCommMonoid T] (m n : ℕ) (a : ℕ → ℕ → T) :
    (∑ i ∈ Finset.range m, ∑ j ∈ Finset.range n, a i j) =
      ∑ j ∈ Finset.range n, ∑ i ∈ Finset.range m, a i j :=
  Finset.sum_comm

/-- "A nulla tagú összeg definíció szerint 0." -/
theorem sum_empty_eq_zero {T : Type*} [AddCommMonoid T] (a : ℕ → T) :
    (∑ i ∈ Finset.range 0, a i) = 0 := by simp

/-- "A nulla tényezős szorzat definíció szerint 1." -/
theorem prod_empty_eq_one {T : Type*} [CommMonoid T] (a : ℕ → T) :
    (∏ i ∈ Finset.range 0, a i) = 1 := by simp

end Szabo
