/-
# Products: the third shared element of *Kalkulus I* and *Lineáris algebra I*

Exercise 1 of Lawvere–Schanuel, *Conceptual Mathematics*, asks the reader to find products
"in life" and in other circumstances.  This file answers that for the two syllabi in this
project by isolating **one** universal property and then instantiating it three times:

* in `Type` — the everyday product, a set of pairs (choices multiply);
* in `TopCat` — the plane `ℝ × ℝ` of *Kalkulus I*, where `⟨f, g⟩` is continuous iff both
  coordinates are;
* in `ModuleCat ℝ` — the direct product `M × N`, and `Fin n → ℝ`, the "valós elem-n-esek"
  of *Lineáris algebra I*, which is the `n`-fold product of `ℝ`.

The second theme is the distinction, invisible in the notation, between

* the **product object** `X × Y` (a *pair*: `Descartes-szorzat`, the domain of two data), and
* a **multiplication map** `m : X × Y → Z` (a *number*: `x · y`, `⟪u, v⟫`, `M · N`),

which is a map *out of* a product.  Every "szorzat" in the two syllabi is one of these two
things, and most exam mistakes come from confusing them.

The companion document `products/Products.tex` (compiled: `products/Products.pdf`) discusses
the examples in words; every mathematical claim it makes is one of the theorems below.
-/

import Mathlib

open CategoryTheory Filter Topology

namespace ProductOverlap

/-! ## 1. The universal property, once and for all

`IsProduct p q` says that the two projections `p : P ⟶ X`, `q : P ⟶ Y` make `P` *the*
product of `X` and `Y`: every pair of maps into `X` and `Y` from a common test object `T`
comes from exactly one map into `P`.  This is Lawvere–Schanuel's definition. -/

/-- `p : P ⟶ X` and `q : P ⟶ Y` exhibit `P` as a product of `X` and `Y`. -/
structure IsProduct {C : Type*} [Category C] {X Y P : C} (p : P ⟶ X) (q : P ⟶ Y) : Prop where
  /-- Existence of the pairing map `⟨f, g⟩`. -/
  pair : ∀ ⦃T : C⦄ (f : T ⟶ X) (g : T ⟶ Y), ∃ h : T ⟶ P, h ≫ p = f ∧ h ≫ q = g
  /-- Two maps into `P` agreeing in both coordinates are equal. -/
  uniq : ∀ ⦃T : C⦄ (h h' : T ⟶ P), h ≫ p = h' ≫ p → h ≫ q = h' ≫ q → h = h'

/-- **The one theorem.**  A product is determined by `X` and `Y` up to an isomorphism
compatible with the projections.  Everything else in this file is an instance of the
definition; this is the invariant content shared by all of them. -/
theorem IsProduct.unique_up_to_iso {C : Type*} [Category C] {X Y P P' : C}
    {p : P ⟶ X} {q : P ⟶ Y} {p' : P' ⟶ X} {q' : P' ⟶ Y}
    (h : IsProduct p q) (h' : IsProduct p' q') :
    ∃ e : P ≅ P', e.hom ≫ p' = p ∧ e.hom ≫ q' = q := by
  obtain ⟨u, hu1, hu2⟩ := h'.pair p q
  obtain ⟨v, hv1, hv2⟩ := h.pair p' q'
  refine ⟨⟨u, v, ?_, ?_⟩, hu1, hu2⟩
  · refine h.uniq _ _ ?_ ?_ <;> simp [Category.assoc, hu1, hu2, hv1, hv2]
  · refine h'.uniq _ _ ?_ ?_ <;> simp [Category.assoc, hu1, hu2, hv1, hv2]

/-! ## 2. Products in life: sets of pairs

The everyday product.  A shirt is a colour *and* a size; a chess square is a file *and* a
rank; an appointment is a day *and* an hour.  In each case "specifying the thing" is the
same as "specifying the two coordinates", which is exactly `type_isProduct`. -/

/-- The set of pairs is the product in the category of sets. -/
theorem type_isProduct (X Y : Type u) :
    IsProduct (C := Type u) (Prod.fst : X × Y → X) (Prod.snd : X × Y → Y) where
  pair := fun _ f g => ⟨fun t => (f t, g t), rfl, rfl⟩
  uniq := fun _ h h' h1 h2 => by
    funext t
    exact Prod.ext (congrFun h1 t) (congrFun h2 t)

/-- Swapping the coordinates also produces a product of `X` and `Y`, so by
`IsProduct.unique_up_to_iso` the two orders of a life-product agree: choosing a colour then
a size is the same as choosing a size then a colour. -/
theorem swap_isProduct (X Y : Type u) :
    IsProduct (C := Type u) (Prod.snd : Y × X → X) (Prod.fst : Y × X → Y) where
  pair := fun _ f g => ⟨fun t => (g t, f t), rfl, rfl⟩
  uniq := fun _ h h' h1 h2 => by
    funext t
    exact Prod.ext (congrFun h2 t) (congrFun h1 t)

/-- `X × Y ≅ Y × X`, obtained from the abstract theorem, not re-proved by hand. -/
theorem prod_comm_iso (X Y : Type u) : Nonempty ((X × Y : Type u) ≅ (Y × X : Type u)) := by
  obtain ⟨e, _, _⟩ := (type_isProduct X Y).unique_up_to_iso (swap_isProduct X Y)
  exact ⟨e⟩

/-- The counting principle: the number of ways to make two independent choices is the
*product* of the numbers of ways.  This is why the word "product" is used at all. -/
theorem card_prod_eq_mul (α β : Type) [Fintype α] [Fintype β] :
    Fintype.card (α × β) = Fintype.card α * Fintype.card β := Fintype.card_prod α β

/-- Colours available in the shop. -/
inductive Colour | red | green | blue
deriving DecidableEq, Fintype

/-- Sizes available in the shop. -/
inductive Size | small | large
deriving DecidableEq, Fintype

/-- A life-sized instance: 3 colours and 2 sizes give 6 shirts. -/
theorem shirts_card : Fintype.card (Colour × Size) = 6 := by decide

/-- Exercise 1.4 d) of `kalkulus_gyakorlo.pdf`: the set `{p/q : p ∈ {1,2,3,4}, q ∈
{101,102,103,104}}` is indexed by a product of two 4-element sets, hence has at most
`4 * 4 = 16` elements. -/
theorem exercise_1_4d_card_le :
    (Finset.image (fun z : ℕ × ℕ => (z.1 : ℚ) / z.2)
      (({1, 2, 3, 4} : Finset ℕ) ×ˢ ({101, 102, 103, 104} : Finset ℕ))).card ≤ 16 := by
  refine le_trans (Finset.card_image_le) ?_
  rw [Finset.card_product]
  decide

/-! ## 3. Products in *Kalkulus I*: the plane, and pairs of continuous functions

`ℝ × ℝ` is the product in the category of spaces and continuous maps.  Concretely: a curve
`t ↦ (f t, g t)` is continuous exactly when its two coordinate functions are.  This is the
reason every "two-variable" construction of the calculus course — graphs, the plane, pairs
of sequences — behaves coordinatewise. -/

/-- The plane is the product of two copies of the line, in the category of topological
spaces. -/
theorem top_isProduct (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] :
    IsProduct (TopCat.ofHom (⟨Prod.fst, continuous_fst⟩ : C(X × Y, X)))
      (TopCat.ofHom (⟨Prod.snd, continuous_snd⟩ : C(X × Y, Y))) where
  pair := fun _ f g => ⟨TopCat.ofHom ⟨fun t => (f t, g t),
      f.hom.continuous.prodMk g.hom.continuous⟩, rfl, rfl⟩
  uniq := fun _ h h' h1 h2 => by
    apply TopCat.hom_ext
    ext t
    · exact congrArg (fun k => (TopCat.Hom.hom k) t) h1
    · exact congrArg (fun k => (TopCat.Hom.hom k) t) h2

/-! ## 4. Products in *Lineáris algebra I*: direct products and `ℝⁿ` -/

/-- The direct product `M × N` with its two projections is the product in the category of
`ℝ`-modules: a linear map into `M × N` is a pair of linear maps. -/
theorem module_isProduct (M N : Type) [AddCommGroup M] [Module ℝ M]
    [AddCommGroup N] [Module ℝ N] :
    IsProduct (ModuleCat.ofHom (LinearMap.fst ℝ M N)) (ModuleCat.ofHom (LinearMap.snd ℝ M N)) where
  pair := fun _ f g => ⟨ModuleCat.ofHom (f.hom.prod g.hom), rfl, rfl⟩
  uniq := fun _ h h' h1 h2 => by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro t
    apply Prod.ext
    · exact congrArg (fun k => (ModuleCat.Hom.hom k) t) h1
    · exact congrArg (fun k => (ModuleCat.Hom.hom k) t) h2

/-- The "valós elem-`n`-esek" `ℝⁿ` of the linear algebra syllabus are the `n`-fold product
of `ℝ`: giving a linear map `T →ₗ ℝⁿ` is the same as giving its `n` coordinate functionals.
This is the `n`-ary form of the same universal property. -/
theorem pi_isProduct {n : ℕ} (T : Type) [AddCommGroup T] [Module ℝ T]
    (f : Fin n → (T →ₗ[ℝ] ℝ)) :
    ∃! h : T →ₗ[ℝ] (Fin n → ℝ), ∀ i, (LinearMap.proj i).comp h = f i := by
  refine ⟨LinearMap.pi f, fun _ => rfl, ?_⟩
  intro h hh
  ext t i
  exact congrArg (fun k : T →ₗ[ℝ] ℝ => k t) (hh i)

/-! ## 5. Multiplication maps: arrows *out of* a product

`x · y`, `⟪u, v⟫`, `M · N` and `f · g` are not product objects; they are maps defined *on* a
product.  Their shared feature is bilinearity, and — on the calculus side — continuity. -/

/-- The multiplication map of the real numbers, `m : ℝ × ℝ → ℝ`. -/
noncomputable def mulMap : ℝ × ℝ → ℝ := fun z => z.1 * z.2

/-- `m` is continuous.  This single fact is what makes the product limit law work. -/
theorem mulMap_continuous : Continuous mulMap := continuous_mul

/-- **The product limit law, read categorically.**  `f · g` is the composite
`m ∘ ⟨f, g⟩`: pair the two functions using the universal property, then multiply.  The
limit passes through because `⟨f, g⟩` converges coordinatewise and `m` is continuous. -/
theorem tendsto_mul_via_product (f g : ℝ → ℝ) (a A B : ℝ)
    (hf : Tendsto f (𝓝 a) (𝓝 A)) (hg : Tendsto g (𝓝 a) (𝓝 B)) :
    Tendsto (fun x => f x * g x) (𝓝 a) (𝓝 (A * B)) :=
  (mulMap_continuous.tendsto (A, B)).comp (hf.prodMk_nhds hg)

/-- **The product rule (Leibniz), read categorically.**  Differentiating `m ∘ ⟨f, g⟩` by the
chain rule, with the derivative of the *bilinear* `m` at `(f x, g x)` being
`(u, v) ↦ u · g x + f x · v`. -/
theorem product_rule_via_product (f g : ℝ → ℝ) (x f' g' : ℝ)
    (hf : HasDerivAt f f' x) (hg : HasDerivAt g g' x) :
    HasDerivAt (fun t => f t * g t) (f' * g x + f x * g') x := hf.mul hg

/-- Multiplication is *not* a linear map on `ℝ × ℝ`, so it is not a morphism in the category
where the linear algebra product lives.  (Scaling both factors by `2` multiplies the value by
`4`, not by `2`.)  This is the precise reason `(f · g)' ≠ f' · g'`. -/
theorem mulMap_not_linear : ¬ ∃ L : (ℝ × ℝ) →ₗ[ℝ] ℝ, ∀ z, L z = mulMap z := by
  rintro ⟨L, hL⟩
  have h1 : L (1, 1) = 1 := by simpa [mulMap] using hL (1, 1)
  have h2 : L (2, 2) = 4 := by rw [hL (2, 2)]; norm_num [mulMap]
  have h3 : ((2 : ℝ) • (1, 1) : ℝ × ℝ) = (2, 2) := by
    simp [Prod.smul_mk]
  have : L (2, 2) = 2 * L (1, 1) := by
    rw [← h3, map_smul]; simp
  rw [h1, h2] at this
  norm_num at this

/-- Multiplication *is* bilinear: linear in each variable separately.  This is the correct
categorical home of a "szorzás" — a bilinear map out of a product. -/
theorem mulMap_bilinear :
    ∃ B : ℝ →ₗ[ℝ] ℝ →ₗ[ℝ] ℝ, ∀ x y : ℝ, B x y = mulMap (x, y) :=
  ⟨LinearMap.mul ℝ ℝ, fun _ _ => rfl⟩

/-- The inner product (`belső szorzat`) of the linear algebra syllabus is a multiplication
map `ℝⁿ × ℝⁿ → ℝ` assembled coordinatewise out of `mulMap`. -/
theorem inner_eq_sum_mulMap {n : ℕ} (u v : EuclideanSpace ℝ (Fin n)) :
    (inner ℝ u v : ℝ) = ∑ i, mulMap (u i, v i) := by
  simp [PiLp.inner_apply, mulMap, mul_comm]

/-- The matrix product is composition of linear maps: another multiplication map, defined on
the product of two matrix spaces. -/
theorem toLin_matrix_mul {n : ℕ} (M N : Matrix (Fin n) (Fin n) ℝ) :
    Matrix.toLin' (M * N) = (Matrix.toLin' M).comp (Matrix.toLin' N) := by
  simp [Matrix.toLin'_mul]

/-- `determinánsok szorzástétele`: the determinant carries the matrix multiplication map to
the multiplication map of `ℝ`, i.e. it is a homomorphism of the two "szorzás" structures. -/
theorem det_mul_map {n : ℕ} (M N : Matrix (Fin n) (Fin n) ℝ) :
    (M * N).det = mulMap (M.det, N.det) := Matrix.det_mul M N

/-- `log` converts the multiplication map into addition; this is exactly what makes the
logarithmic differentiation of exercise 4.3 work. -/
theorem log_mulMap {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Real.log (mulMap (x, y)) = Real.log x + Real.log y := Real.log_mul hx.ne' hy.ne'

/-! ## 6. The products of `kalkulus_gyakorlo.pdf` -/

/-- Exercise 2.17 b): the pointwise product of two injective functions need not be
injective — `id · id = x²`.  A pointwise product is `m ∘ ⟨f, g⟩`, and `m` is not injective,
so no property of `f` and `g` alone can save it. -/
theorem exercise_2_17b :
    ¬ ∀ f g : ℝ → ℝ, Function.Injective f → Function.Injective g →
      Function.Injective (fun x => f x * g x) := by
  intro h
  have := h id id Function.injective_id Function.injective_id
    (a₁ := (1 : ℝ)) (a₂ := -1) (by norm_num)
  norm_num at this

/-- Exercise 2.17 a): the same for the sum — `id + (-id) = 0`. -/
theorem exercise_2_17a :
    ¬ ∀ f g : ℝ → ℝ, Function.Injective f → Function.Injective g →
      Function.Injective (fun x => f x + g x) := by
  intro h
  have := h id (fun x => -x) Function.injective_id neg_injective
    (a₁ := (0 : ℝ)) (a₂ := 1) (by norm_num)
  norm_num at this

/-- Exercise 4.11 a): of all splittings of `20` into two terms, the product is largest for
`10 + 10`.  An optimisation problem *about* the multiplication map. -/
theorem exercise_4_11a (x y : ℝ) (h : x + y = 20) : mulMap (x, y) ≤ 100 := by
  have hy : y = 20 - x := by linarith
  subst hy
  simp only [mulMap]
  nlinarith [sq_nonneg (x - 10)]

/-- Exercise 4.11 a), the maximum is attained: `10 · 10 = 100`. -/
theorem exercise_4_11a_attained : mulMap (10, 10) = 100 := by norm_num [mulMap]

/-- Exercise 2.13 a): `f (x) = x · sin x` is a pointwise product, so it is differentiated by
`product_rule_via_product`. -/
theorem exercise_2_13a_deriv (x : ℝ) :
    HasDerivAt (fun t : ℝ => t * Real.sin t) (1 * Real.sin x + x * Real.cos x) x :=
  product_rule_via_product _ _ x 1 (Real.cos x) (hasDerivAt_id x) (Real.hasDerivAt_sin x)

/-- Exercise 2.10 / 2.12: composition, in contrast, is *not* a product construction — it is
the categorical composition, associative and unital, whereas the pointwise product is
`m ∘ ⟨f, g⟩`.  Keeping them apart is the point of the exercise. -/
theorem comp_ne_pointwise_mul :
    ∃ f g : ℝ → ℝ, (fun x => f (g x)) ≠ (fun x => f x * g x) := by
  refine ⟨fun _ => 1, fun _ => 0, ?_⟩
  intro h
  have := congrFun h 0
  norm_num at this

/-! ## 7. The bridge between the two courses

The single multiplication map `m : ℝ × ℝ → ℝ` is at once a morphism of spaces (calculus: it
is continuous, hence limits and derivatives of products behave) and the bilinear map that
generates every "szorzat" of linear algebra (inner product, matrix product, determinant
multiplicativity).  The product *object* is the shared domain on which all of them live. -/

/-- The two roles of `m` at once: continuous, and bilinear. -/
theorem mulMap_continuous_and_bilinear :
    Continuous mulMap ∧ ∃ B : ℝ →ₗ[ℝ] ℝ →ₗ[ℝ] ℝ, ∀ x y : ℝ, B x y = mulMap (x, y) :=
  ⟨mulMap_continuous, mulMap_bilinear⟩

end ProductOverlap
