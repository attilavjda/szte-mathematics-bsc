import RequestProject.Gadgets.DarbouxGadget
import RequestProject.Tematika.Kalkulus
import RequestProject.Notes.FreudLinAlg

/-!
# The Darboux gadget in characteristic two: affine convexity

This file instantiates the abstract gadget of `RequestProject/Gadgets/DarbouxGadget.lean`
in the world the Kasami/AB/APN library lives in: a field of characteristic two, where
there is no order (`Tematika.Morita.no_linear_order_of_charTwo`) and hence no interval.

The replacement for "interval" is **affine subset**: a set closed under the ternary
operation `u - v + w` (in characteristic two, `u + v + w`).  This is exactly the ternary
"heap"/torsor operation, and `isAffine_iff_coset` proves the expected classification:

> a nonempty set is affine iff it is a coset of a subgroup

which is the precise analogue of "a nonempty order-connected subset of `ℝ` is an interval".

The main results:

* `affineConvexity` — the convexity structure, and `faithful_affineConvexity` — it is a
  *faithful* structure, so the Darboux statement below has content.
* `darboux_of_constIncrements` — **the gadget**: if the increments of `g` are
  translation-invariant (`g (x + b) - g x` does not depend on `x`, i.e. the second discrete
  derivative of `f` is point-independent, i.e. `f` is *quadratic*), then `range g` is
  affine.  This is the characteristic-two Darboux theorem, and its proof is three lines —
  everything else in the Gold/Kasami analysis is the *verification of the hypothesis*.
* `gold_hasDarboux` — the Gold power map `x ↦ x ^ (2 ^ k + 1)` satisfies the hypothesis, so
  its derivative ranges are affine; with `Tematika.Kalkulus.card_gold_deriv_range` they are
  hyperplane cosets of size `2 ^ (n - 1)`.
* `apn_derivRange_card` — the **measure form** of the gadget: for *any* APN function the
  range of a nonzero derivative has exactly `|F| / 2` elements.  This is the form that
  survives for Kasami functions, which are not quadratic.
* `measure_form_not_affine_form` — the two forms are genuinely different: an explicit
  derivative whose range has the APN size `2 ^ (n - 1)` but is not affine.
* Transport: `isConvex_image_addEquiv` and `gold_darboux_iff_matrix_darboux` verify that the
  field picture and the coordinate/matrix (Morita) picture carry *equivalent* Darboux
  statements.
-/

namespace Gadget

open Papers.FastPoints Tematika Tematika.Kalkulus CollisionAnalysis

/-! ## 1. Affine convexity: the characteristic-two notion of "interval" -/

section AffineConvexity

variable {W W' : Type*} [AddCommGroup W] [AddCommGroup W']

/-- The convexity structure of **affine subsets** of an abelian group: sets closed under
the ternary operation `u - v + w`.  In characteristic two this reads `u + v + w`. -/
def affineConvexity (W : Type*) [AddCommGroup W] : Convexity W where
  IsConvex S := ∀ u ∈ S, ∀ v ∈ S, ∀ w ∈ S, u - v + w ∈ S
  univ_mem := by intro u _ v _ w _; trivial
  sInter_mem := by
    intro 𝒞 h u hu v hv w hw T hT
    exact h T hT u (hu T hT) v (hv T hT) w (hw T hT)

theorem affineConvexity_iff {S : Set W} :
    (affineConvexity W).IsConvex S ↔ ∀ u ∈ S, ∀ v ∈ S, ∀ w ∈ S, u - v + w ∈ S := Iff.rfl

/-- **Classification of affine sets: nonempty affine = coset of a subgroup.**  The exact
analogue of "a nonempty order-connected subset of `ℝ` is an interval". -/
theorem isAffine_iff_coset {S : Set W} (hne : S.Nonempty) :
    (affineConvexity W).IsConvex S ↔
      ∃ (H : AddSubgroup W) (c : W), S = (fun h => c + h) '' (H : Set W) := by
  constructor
  · intro hS
    obtain ⟨c, hc⟩ := hne
    refine ⟨{ carrier := {x | c + x ∈ S}
              zero_mem' := by simpa using hc
              add_mem' := by
                intro x y hx hy
                have hmem := hS (c + x) hx c hc (c + y) hy
                have heq : c + x - c + (c + y) = c + (x + y) := by abel
                rwa [heq] at hmem
              neg_mem' := by
                intro x hx
                have hmem := hS c hc (c + x) hx c hc
                have heq : c - (c + x) + c = c + -x := by abel
                rwa [heq] at hmem },
      c, ?_⟩
    ext y
    simp only [Set.mem_image, AddSubgroup.mem_mk, SetLike.mem_coe]
    constructor
    · intro hy
      exact ⟨y - c, by simpa using hy, by abel⟩
    · rintro ⟨h, hh, rfl⟩
      exact hh
  · rintro ⟨H, c, rfl⟩
    rintro _ ⟨h₁, hh₁, rfl⟩ _ ⟨h₂, hh₂, rfl⟩ _ ⟨h₃, hh₃, rfl⟩
    have heq : c + (h₁ - h₂ + h₃) = c + h₁ - (c + h₂) + (c + h₃) := by
      simp only [sub_eq_add_neg, neg_add_rev]
      abel
    exact ⟨h₁ - h₂ + h₃, H.add_mem (H.sub_mem hh₁ hh₂) hh₃, heq⟩

/-- Every subgroup is affine (it is the coset of itself at `0`). -/
theorem isConvex_addSubgroup (H : AddSubgroup W) :
    (affineConvexity W).IsConvex (H : Set W) := by
  intro u hu v hv w hw
  exact H.add_mem (H.sub_mem hu hv) hw

/-- Every submodule is affine. -/
theorem isConvex_submodule {R : Type*} [Ring R] [Module R W] (M : Submodule R W) :
    (affineConvexity W).IsConvex (M : Set W) := by
  intro u hu v hv w hw
  exact M.add_mem (M.sub_mem hu hv) hw

/-- Affine convexity is a **faithful** structure: not every set is affine, so the Darboux
statement in characteristic two has content (contrast `Convexity.not_faithful_indiscrete`). -/
theorem faithful_affineConvexity : (affineConvexity (Fin 3 → ZMod 2)).Faithful := by
  refine ⟨{0, ![1, 0, 0], ![0, 1, 0]}, fun h => ?_⟩
  have hmem := h ![1,0,0] (by simp) 0 (by simp) ![0,1,0] (by simp)
  have : (![1,0,0] : Fin 3 → ZMod 2) - 0 + ![0,1,0] = ![1,1,0] := by
    funext i; fin_cases i <;> simp
  rw [this] at hmem
  revert hmem
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  intro hc
  rcases hc with hc | hc | hc
  · exact absurd (congrFun hc 0) (by decide)
  · exact absurd (congrFun hc 1) (by decide)
  · exact absurd (congrFun hc 0) (by decide)

/-- Affine convexity transports along an **additive** equivalence: this is the transport
mechanism used for the Morita comparison below. -/
theorem isConvex_image_addEquiv (e : W ≃+ W') (S : Set W) :
    (affineConvexity W').IsConvex (e '' S) ↔ (affineConvexity W).IsConvex S := by
  constructor
  · intro h u hu v hv w hw
    have := h (e u) ⟨u, hu, rfl⟩ (e v) ⟨v, hv, rfl⟩ (e w) ⟨w, hw, rfl⟩
    obtain ⟨t, ht, hte⟩ : ∃ t ∈ S, e t = e u - e v + e w := this
    have : t = u - v + w := by
      apply e.injective
      rw [hte, map_add, map_sub]
    exact this ▸ ht
  · rintro h _ ⟨u, hu, rfl⟩ _ ⟨v, hv, rfl⟩ _ ⟨w, hw, rfl⟩
    exact ⟨u - v + w, h u hu v hv w hw, by rw [map_add, map_sub]⟩

end AffineConvexity

/-! ## 2. The gadget: constant increments imply the Darboux property

The real Darboux theorem needs the mean value theorem.  Its characteristic-two shadow needs
only the following: if the increment `g (x + b) - g x` does not depend on the base point
`x`, then the range of `g` is affine.  For `g = D a f` this hypothesis says precisely that
the **second** discrete derivative `D b (D a f)` is a constant function — the algebraic
avatar of "`f` is quadratic". -/

section Gadget

variable {V W : Type*} [AddCommGroup V] [AddCommGroup W]

/-- `g` has **translation-invariant increments**. -/
def HasConstIncrements (g : V → W) : Prop := ∀ b x y, g (x + b) - g x = g (y + b) - g y

/-- For a discrete derivative, constant increments = point-independent second derivative. -/
theorem hasConstIncrements_deriv_iff {K : Type*} [CommRing K] (a : V) (f : V → K) :
    HasConstIncrements (D a f) ↔ ∀ b x y, D b (D a f) x = D b (D a f) y := Iff.rfl

/-- **The Darboux gadget in characteristic two.**  If the increments of `g` do not depend on
the base point, the range of `g` is an affine set.

The proof is the whole content: given `g x`, `g y`, `g z`, the required witness for
`g x - g y + g z` is the point `z + (x - y)`. -/
theorem darboux_of_constIncrements {g : V → W} (hg : HasConstIncrements g) :
    (affineConvexity W).IsConvex (Set.range g) := by
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ _ ⟨z, rfl⟩
  refine ⟨z + (x - y), ?_⟩
  have h := hg (x - y) z y
  have hy : y + (x - y) = x := by abel
  rw [hy] at h
  have : g (z + (x - y)) = g z + (g x - g y) := by
    rw [sub_eq_iff_eq_add] at h
    rw [h]
    abel
  rw [this]
  abel

/-- The `Adm`-class version: the Darboux property in the sense of the abstract gadget. -/
theorem hasDarbouxOn_constIncrements (Dop : (V → W) → V → W)
    (Adm : (V → W) → Prop) (h : ∀ f, Adm f → HasConstIncrements (Dop f)) :
    HasDarbouxOn (affineConvexity W) Adm Dop :=
  fun f hf => darboux_of_constIncrements (h f hf)

end Gadget

/-! ## 3. Instance: the Gold maps `x ↦ x ^ (2 ^ k + 1)`

`Tematika.Kalkulus.gold_deriv_eq` says `D a (N k) x = Cross k a x + N k a` with `Cross k a`
additive.  Hence the increments are constant, and the abstract gadget applies.  This is a
genuine factoring: `gold_deriv_affine_closed` in `Tematika/Kalkulus.lean` was proved by a
direct computation, whereas here the computation is only used to verify the *hypothesis* of
a context-free lemma. -/

section Gold

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-- The Gold derivative has translation-invariant increments; the constant increment in
direction `b` is `Cross k a b`. -/
theorem gold_constIncrements (k : ℕ) (a : F) : HasConstIncrements (D a (N k)) := by
  have key : ∀ b z : F, D a (N k) (z + b) - D a (N k) z = Cross k a b := by
    intro b z
    rw [gold_deriv_eq, gold_deriv_eq, cross_add]
    ring
  intro b x y
  rw [key b x, key b y]

/-- **Darboux for the Gold maps, via the gadget.**  The range of every derivative of
`x ↦ x ^ (2 ^ k + 1)` is affine. -/
theorem gold_darboux (k : ℕ) (a : F) :
    (affineConvexity F).IsConvex (Set.range (D a (N k))) :=
  darboux_of_constIncrements (gold_constIncrements k a)

/-- The same statement in the packaged form of the abstract gadget. -/
theorem gold_hasDarboux (a : F) :
    HasDarbouxOn (affineConvexity F) (fun f : F → F => ∃ k : ℕ, f = N k) (fun f => D a f) := by
  rintro f ⟨k, rfl⟩
  exact gold_darboux k a

/-- **Darboux image = hyperplane coset.**  Combining the gadget with the classification of
affine sets and the dimension count of `Tematika.Kalkulus.card_gold_deriv_range`: for
`gcd (k, n) = 1` and `a ≠ 0` the range of the Gold derivative is a coset of a subgroup and
has exactly `2 ^ (n - 1)` elements. -/
theorem gold_darboux_coset {n : ℕ} (hcard : Fintype.card F = 2 ^ n) (k : ℕ)
    (hcop : Nat.Coprime k n) {a : F} (ha : a ≠ 0) :
    (∃ (H : AddSubgroup F) (c : F), Set.range (D a (N k)) = (fun h => c + h) '' (H : Set F)) ∧
      (Set.range (D a (N k))).ncard = 2 ^ (n - 1) := by
  refine ⟨?_, card_gold_deriv_range hcard k hcop ha⟩
  exact (isAffine_iff_coset (Set.range_nonempty (D a (N k)))).1 (gold_darboux k a)

end Gold

/-! ## 4. The measure form: what survives for Kasami functions

Kasami functions `x ↦ x ^ (2 ^ (2k) - 2 ^ k + 1)` have algebraic degree `k + 1`, so for
`k ≥ 2` they are *not* quadratic and the hypothesis of the gadget fails: their derivative
images are not affine in general.  What still holds — and this is the form the AB/APN proof
actually uses — is the **measure form**: for an APN function every nonzero derivative is
exactly two-to-one, so its image has `|F| / 2` elements, the same number a hyperplane coset
has.  So the Darboux gadget degenerates from "the image is an interval" to "the image has
the measure of a half-space". -/

section Measure

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-- The range of a discrete derivative, as a `Finset`. -/
theorem range_eq_derivImage (f : F → F) (a : F) :
    Set.range (D a f) = (Papers.Dobbertin.derivImage f a : Set F) := by
  ext y
  simp only [Set.mem_range, Papers.Dobbertin.derivImage, Finset.coe_image, Finset.coe_univ,
    Set.image_univ, Set.mem_range, D, CharTwo.sub_eq_add]

/-- **Measure form of the Darboux gadget.**  For an APN function the image of every nonzero
derivative has exactly half as many elements as the field — the cardinality of a hyperplane
coset, even when the image is not affine. -/
theorem apn_derivRange_card {f : F → F} (hf : KasamiAPN.IsAPN f) {a : F} (ha : a ≠ 0) :
    2 * (Set.range (D a f)).ncard = Fintype.card F := by
  classical
  rw [range_eq_derivImage, Set.ncard_coe_finset]
  exact Papers.Dobbertin.two_mul_card_derivImage hf ha

end Measure

/-! ### The two forms are genuinely different

An explicit function on `F₂³` whose derivative image has the APN size `2 ^ (3 - 1) = 4` but
is not affine.  So "measure form" is strictly weaker than "affine form": quadratic
(Gold-type) behaviour is a real extra hypothesis, not a consequence of APN-ness. -/

section Sharpness

/-- A test function on `F₂³`: `0` on the hyperplane `x₂ = 0` and `(x₀, x₁, x₀x₁)` above it. -/
def testFun : (Fin 3 → ZMod 2) → (Fin 3 → ZMod 2) :=
  fun x => if x 2 = 1 then ![x 0, x 1, x 0 * x 1] else 0

/-- The direction in which we differentiate. -/
def testDir : Fin 3 → ZMod 2 := ![0, 0, 1]

theorem testFun_deriv_card :
    (Finset.image (D testDir testFun) Finset.univ).card = 4 := by decide

theorem testFun_deriv_ne : ∀ x : Fin 3 → ZMod 2, D testDir testFun x ≠ ![1, 1, 0] := by decide

/-- **Measure form does not imply affine form.**  The range of `D testDir testFun` has `4`
elements (`= 2 ^ (3 - 1)`, the APN/two-to-one size) yet is not affine. -/
theorem measure_form_not_affine_form :
    (Set.range (D testDir testFun)).ncard = 4 ∧
      ¬ (affineConvexity (Fin 3 → ZMod 2)).IsConvex (Set.range (D testDir testFun)) := by
  classical
  constructor
  · have : Set.range (D testDir testFun) =
        ((Finset.image (D testDir testFun) Finset.univ : Finset (Fin 3 → ZMod 2)) : Set _) := by
      ext y; simp
    rw [this, Set.ncard_coe_finset, testFun_deriv_card]
  · intro h
    have h1 : (![1, 0, 0] : Fin 3 → ZMod 2) ∈ Set.range (D testDir testFun) := by
      refine ⟨![1, 0, 0], ?_⟩; decide
    have h2 : (0 : Fin 3 → ZMod 2) ∈ Set.range (D testDir testFun) := by
      refine ⟨0, ?_⟩; decide
    have h3 : (![0, 1, 0] : Fin 3 → ZMod 2) ∈ Set.range (D testDir testFun) := by
      refine ⟨![0, 1, 0], ?_⟩; decide
    have hcomb := h _ h1 _ h2 _ h3
    have heq : (![1, 0, 0] : Fin 3 → ZMod 2) - 0 + ![0, 1, 0] = ![1, 1, 0] := by
      funext i; fin_cases i <;> simp
    rw [heq] at hcomb
    obtain ⟨x, hx⟩ := hcomb
    exact testFun_deriv_ne x hx

end Sharpness

/-! ## 5. Occurrences of the gadget elsewhere in the library

The same "the image of a derivative-like operator is convex" pattern already appears in
several modules, in different contexts.  Here it is exhibited uniformly. -/

section Occurrences

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-- **Artin–Schreier / linearized polynomials.**  The image of the additive map
`x ↦ x ^ (2 ^ k) + x` is affine (indeed a subspace), and by
`Tematika.LinAlg.range_LK_eq_ker_trace` it is *exactly* the trace hyperplane when
`gcd (k, n) = 1`.  So the Darboux image of this linear "derivative" is a hyperplane, which
is the geometric content of the solvability criterion `Tr b = 0`. -/
theorem range_LK_darboux (k : ℕ) :
    (affineConvexity F).IsConvex ((LinearMap.range (LinAlg.LK (F := F) k) : Submodule (ZMod 2) F) :
      Set F) :=
  isConvex_submodule _

/-- The sharp form: for `gcd (k, n) = 1` the Darboux image of `x ↦ x ^ (2 ^ k) + x` is the
trace hyperplane, a set of `2 ^ (n - 1)` elements — the same count as for the Gold
derivative and for an APN derivative. -/
theorem range_LK_eq_hyperplane {n : ℕ} (hcard : Fintype.card F = 2 ^ n) (k : ℕ)
    (hcop : Nat.Coprime k n) (hn : 1 ≤ n) :
    ((LinearMap.range (LinAlg.LK (F := F) k) : Submodule (ZMod 2) F) : Set F) =
      {y : F | Algebra.trace (ZMod 2) F y = 0} :=
  LinAlg.range_LK_eq_ker_trace hcard k hcop hn

/-- **Fast points.**  The set of fast points of a Boolean function, together with `0`, is a
subspace (`Notes.Freud.fastPointSubspace`), hence affine: the same gadget one level up, in
the *degree* context rather than the value context. -/
theorem fastPoints_darboux {n : ℕ} (f : (Fin n → ZMod 2) → ZMod 2) :
    (affineConvexity (Fin n → ZMod 2)).IsConvex
      ((Notes.Freud.fastPointSubspace f : Submodule (ZMod 2) (Fin n → ZMod 2)) :
        Set (Fin n → ZMod 2)) :=
  isConvex_submodule _

/-- **Rolle, the dual side.**  The Darboux gadget describes the *image* of a derivative;
`Tematika.Kalkulus.injective_iff_deriv_ne_zero` describes its *kernel*.  Together: a map is
injective iff no nonzero direction has a critical point. -/
theorem rolle_dual {V W : Type*} [AddCommGroup V] [AddCommGroup W] (f : V → W) :
    Function.Injective f ↔ ∀ a : V, a ≠ 0 → ∀ x : V, D a f x ≠ 0 :=
  injective_iff_deriv_ne_zero f

end Occurrences

/-! ## 6. Morita transport: the field picture and the matrix picture

`GF(2ⁿ)` is an `F₂`-progenerator, and `Tematika.Morita.endAlgEquivMatrix` identifies
`End_{F₂}(GF(2ⁿ))` with `M_n(F₂)`.  Under the corresponding coordinate equivalence the Gold
derivative becomes the affine map `v ↦ M *ᵥ v + c` with `M` the matrix of `Cross k a`.  The
theorem `gold_darboux_iff_matrix_darboux` verifies that the Darboux statements on the two
sides are *equivalent* — the same theorem read in two Morita-equivalent contexts. -/

section Morita

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-- The coordinate equivalence `GF(2ⁿ) ≃ F₂ⁿ` attached to the Morita basis. -/
noncomputable def coordEquiv {n : ℕ} (hcard : Fintype.card F = 2 ^ n) :
    F ≃ₗ[ZMod 2] (Fin n → ZMod 2) :=
  (Morita.moritaBasis hcard).equivFun

/-- The matrix of the cross form `Cross k a` in the Morita basis. -/
noncomputable def crossMatrix {n : ℕ} (hcard : Fintype.card F = 2 ^ n) (k : ℕ) (a : F) :
    Matrix (Fin n) (Fin n) (ZMod 2) :=
  Morita.endAlgEquivMatrix hcard (crossLin k a)

/-- **The Gold derivative in coordinates** is the affine map `v ↦ M *ᵥ v + c`. -/
theorem coord_gold_deriv {n : ℕ} (hcard : Fintype.card F = 2 ^ n) (k : ℕ) (a x : F) :
    coordEquiv hcard (D a (N k) x) =
      (crossMatrix hcard k a).mulVec (coordEquiv hcard x) + coordEquiv hcard (N k a) := by
  have hmul : (crossMatrix hcard k a).mulVec ((Morita.moritaBasis hcard).repr x) =
      (Morita.moritaBasis hcard).repr (crossLin k a x) := by
    simpa [crossMatrix, Morita.endAlgEquivMatrix, LinearMap.toMatrixAlgEquiv_apply,
      LinearMap.toMatrix_apply] using
      LinearMap.toMatrix_mulVec_repr (Morita.moritaBasis hcard) (Morita.moritaBasis hcard)
        (crossLin k a) x
  have hgold : D a (N k) x = crossLin k a x + N k a := by
    rw [gold_deriv_eq]; rfl
  have hlin : coordEquiv hcard (crossLin k a x)
      = (crossMatrix hcard k a).mulVec (coordEquiv hcard x) := by
    funext i
    simp only [coordEquiv, Module.Basis.equivFun_apply]
    rw [← hmul]
  rw [hgold, map_add, hlin]

/-- **Morita comparison, verified.**  The Darboux statement for the Gold derivative in the
field `GF(2ⁿ)` and the Darboux statement for the corresponding affine matrix map on `F₂ⁿ`
are equivalent. -/
theorem gold_darboux_iff_matrix_darboux {n : ℕ} (hcard : Fintype.card F = 2 ^ n) (k : ℕ)
    (a : F) :
    (affineConvexity F).IsConvex (Set.range (D a (N k))) ↔
      (affineConvexity (Fin n → ZMod 2)).IsConvex
        (Set.range (fun v => (crossMatrix hcard k a).mulVec v + coordEquiv hcard (N k a))) := by
  have hrange : (coordEquiv hcard : F → (Fin n → ZMod 2)) '' Set.range (D a (N k)) =
      Set.range (fun v => (crossMatrix hcard k a).mulVec v + coordEquiv hcard (N k a)) := by
    ext w
    constructor
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨coordEquiv hcard x, (coord_gold_deriv hcard k a x).symm⟩
    · rintro ⟨v, rfl⟩
      obtain ⟨x, rfl⟩ := (coordEquiv hcard).surjective v
      exact ⟨D a (N k) x, ⟨x, rfl⟩, coord_gold_deriv hcard k a x⟩
  rw [← hrange]
  exact (isConvex_image_addEquiv (coordEquiv hcard).toAddEquiv _).symm

/-- Both sides of the comparison are true; the matrix side is the coordinate form of
`gold_darboux`. -/
theorem matrix_gold_darboux {n : ℕ} (hcard : Fintype.card F = 2 ^ n) (k : ℕ) (a : F) :
    (affineConvexity (Fin n → ZMod 2)).IsConvex
      (Set.range (fun v => (crossMatrix hcard k a).mulVec v + coordEquiv hcard (N k a))) :=
  (gold_darboux_iff_matrix_darboux hcard k a).1 (gold_darboux k a)

end Morita

/-! ## 7. The dual (Walsh) context: the Darboux image as a linear structure

The trace pairing makes `(F, +)` self-dual, and the AB half of the library lives on the
dual side (`RequestProject/Walsh`).  The Darboux statement transports there too, and it
becomes a statement about *character sums*: because the image of the Gold derivative is a
coset of a hyperplane, there is a nonzero `b` — explicitly `b = (N k a)⁻¹` — for which
`Tr (b · D a f x)` does not depend on `x` at all.  The corresponding character sum is
therefore extremal, `± |F|`.  This "linear structure" is exactly the degeneracy that makes
quadratic (Gold) functions so special on the Walsh side. -/

section Dual

variable {F : Type*} [Field F] [Fintype F] [DecidableEq F] [CharP F 2]

/-- **A linear structure of the Gold derivative.**  With `b = (N k a)⁻¹` the composite
`x ↦ Tr (b · D a (N k) x)` is *constant*, equal to `Tr 1`.  Equivalently: the Darboux image
lies inside a coset of a trace hyperplane. -/
theorem gold_deriv_trace_const (k : ℕ) {a : F} (ha : a ≠ 0) (x : F) :
    WalshAB.Tr ((N k a)⁻¹ * D a (N k) x) = WalshAB.Tr (1 : F) := by
  have hNa : N k a ≠ 0 := pow_ne_zero _ ha
  have hcross : Cross k a x = N k a * L k (x / a) := cross_eq_norm_L k a x ha
  have hD : D a (N k) x = Cross k a x + N k a := gold_deriv_eq k a x
  have h0 : WalshAB.Tr (L k (x / a)) = 0 :=
    LinAlg.range_LK_le_ker_trace k (L k (x / a)) ⟨x / a, by simp [LinAlg.LK_apply]⟩
  rw [hD, hcross, mul_add, ← mul_assoc, inv_mul_cancel₀ hNa, one_mul,
    WalshAB.Tr_add, h0, zero_add]

/-- **Extremal character sum.**  Consequently the character sum of the Gold derivative
against the functional `b = (N k a)⁻¹` is `± |F|`: the maximal possible value.  This is the
Darboux statement read in the Pontryagin-dual (Walsh) context. -/
theorem gold_deriv_char_sum (k : ℕ) {a : F} (ha : a ≠ 0) :
    ∑ x : F, WalshAB.χ ((N k a)⁻¹ * D a (N k) x) = (Fintype.card F : ℤ) * WalshAB.χ (1 : F) := by
  have hconst : ∀ x ∈ (Finset.univ : Finset F),
      WalshAB.χ ((N k a)⁻¹ * D a (N k) x) = WalshAB.χ (1 : F) := by
    intro x _
    simp only [WalshAB.χ, gold_deriv_trace_const k ha x]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end Dual

end Gadget
