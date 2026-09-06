import Mathlib

/-!
# A second syllabus element shared by *Kalkulus I* and *Lineáris algebra I*

Reading the two course descriptions (`Tantárgy tartalma`) again:

* **Kalkulus I (MBLK37E)**: *"A valós számtest. Teljes indukció. **Nevezetes
  egyenlőtlenségek**."* — the absolute value and the triangle inequality
  `|x + y| ≤ |x| + |y|`, the basic tool for every limit estimate in the course.
* **Lineáris algebra I (MBLK15E)**: *"Belső szorzat, **vektorok hossza,
  háromszög-egyenlőtlenség, Cauchy--Schwarz-egyenlőtlenség**, vektorok
  merőlegessége…"* — the Euclidean length of a vector and its triangle inequality
  `‖u + v‖ ≤ ‖u‖ + ‖v‖`.

The shared element is the **triangle inequality for a distance**, i.e. the notion of a
*metric*.  Category theory makes the overlap exact, following Lawvere: a metric space
*is* a category enriched over the monoidal poset `([0, ∞), ≥, +)`.  Under that
dictionary

* the objects of the enriched category are the points,
* `d x y` is the hom-object from `x` to `y`,
* `d x x = 0` is the **identity** morphism,
* `d x z ≤ d x y + d y z`, the **triangle inequality**, is exactly **composition**,
* a distance–non-increasing (short) map is exactly an **enriched functor**.

So "nevezetes egyenlőtlenségek" on the calculus side and "háromszög-egyenlőtlenség" on
the linear algebra side are the *same* structure: composition in a `LawvereSpace`.

The file is organised as follows.

* `TriangleOverlap.LawvereSpace` — the common structure (identities + composition).
* `TriangleOverlap.instCategoryLawvereSpace` — short maps make these into a genuine
  `CategoryTheory.Category` (the category `Met`).
* `TriangleOverlap.dist_chain` — the *one* abstract theorem: composing `n` morphisms.
  Its two specialisations are the calculus statement `|∑ aᵢ| ≤ ∑ |aᵢ|`
  (`TriangleOverlap.abs_sum_le_of_chain`) and the linear algebra statement
  `‖∑ vᵢ‖ ≤ ∑ ‖vᵢ‖` (`TriangleOverlap.norm_sum_le_of_chain`).
* `TriangleOverlap.calcSpace`, `TriangleOverlap.linAlgSpace` — the two syllabus
  instances, with the two named inequalities `abs_add_le'` and
  `cauchy_schwarz`/`norm_add_le'`.
* `TriangleOverlap.lengthShort` — the bridge: the length function
  `‖·‖ : ℝⁿ → ℝ` is a morphism `linAlgSpace n ⟶ calcSpace` in `Met`, i.e. the linear
  algebra distance is carried onto the calculus distance by an enriched functor.
* `TriangleOverlap.calcIsoLinAlgOne` — the two syllabus items literally agree in
  dimension one: `calcSpace ≅ linAlgSpace 1` in `Met`.
* `TriangleOverlap.iso_isometry`, `TriangleOverlap.nonempty_iso_equivalence` —
  the common notion of equivalence (isometry) and the invariance of all distances.
-/

open CategoryTheory

noncomputable section

namespace TriangleOverlap

/-! ## The common structure: a Lawvere space (= category enriched in `([0,∞), ≥, +)`) -/

/-- A **Lawvere space**: a type with a distance whose `d x x = 0` is the identity
morphism and whose triangle inequality is composition.  Both courses study exactly
this structure — `|x - y|` in Kalkulus I, `‖u - v‖` in Lineáris algebra I. -/
structure LawvereSpace where
  /-- The points, i.e. the objects of the enriched category. -/
  carrier : Type
  /-- The hom-object `d x y ∈ [0, ∞)`. -/
  d : carrier → carrier → ℝ
  /-- Hom-objects live in `[0, ∞)`. -/
  d_nonneg : ∀ x y, 0 ≤ d x y
  /-- **Identity**: `𝟙 x` is the witness `d x x ≤ 0`. -/
  d_self : ∀ x, d x x = 0
  /-- **Composition** = the triangle inequality. -/
  d_triangle : ∀ x y z, d x z ≤ d x y + d y z

attribute [simp] LawvereSpace.d_self

instance : CoeSort LawvereSpace Type := ⟨LawvereSpace.carrier⟩

/-- Every Mathlib metric space is a Lawvere space; this is how both syllabus examples
enter. -/
@[reducible] def ofMetric (X : Type) [MetricSpace X] : LawvereSpace where
  carrier := X
  d := dist
  d_nonneg := fun _ _ => dist_nonneg
  d_self := dist_self
  d_triangle := dist_triangle

@[simp] theorem ofMetric_d (X : Type) [MetricSpace X] (x y : X) :
    (ofMetric X).d x y = dist x y := rfl

/-! ## The category `Met`: enriched functors = short maps -/

/-- A **short map** (distance non-increasing map): an enriched functor between Lawvere
spaces. -/
@[ext]
structure ShortMap (X Y : LawvereSpace) where
  /-- The underlying map of points. -/
  toFun : X.carrier → Y.carrier
  /-- Functoriality: the map does not increase distances. -/
  short : ∀ a b, Y.d (toFun a) (toFun b) ≤ X.d a b

instance {X Y : LawvereSpace} : CoeFun (ShortMap X Y) (fun _ => X.carrier → Y.carrier) :=
  ⟨ShortMap.toFun⟩

/-- Lawvere spaces and short maps form a category, `Met`. -/
instance instCategoryLawvereSpace : Category LawvereSpace where
  Hom X Y := ShortMap X Y
  id _ := ⟨id, fun _ _ => le_refl _⟩
  comp f g := ⟨fun a => g.toFun (f.toFun a), fun a b => (g.short _ _).trans (f.short a b)⟩
  id_comp _ := rfl
  comp_id _ := rfl
  assoc _ _ _ := rfl

@[simp] theorem id_toFun (X : LawvereSpace) : (𝟙 X : ShortMap X X).toFun = id := rfl

@[simp] theorem comp_toFun {X Y Z : LawvereSpace} (f : X ⟶ Y) (g : Y ⟶ Z) (a : X.carrier) :
    (f ≫ g).toFun a = g.toFun (f.toFun a) := rfl

/-! ## The one abstract theorem: composing a chain of morphisms -/

/-- **The shared theorem.**  In any Lawvere space, composing the `n` morphisms of a chain
`f 0 → f 1 → ⋯ → f n` gives `d (f 0) (f n) ≤ ∑ d (f i) (f (i+1))`.  This single statement
(proved by `teljes indukció`, also on the Kalkulus I syllabus) is the source of both
courses' "nevezetes egyenlőtlenség". -/
theorem dist_chain (X : LawvereSpace) (f : ℕ → X.carrier) :
    ∀ n : ℕ, X.d (f 0) (f n) ≤ ∑ i ∈ Finset.range n, X.d (f i) (f (i + 1))
  | 0 => by simp
  | (n + 1) => by
      calc X.d (f 0) (f (n + 1))
          ≤ X.d (f 0) (f n) + X.d (f n) (f (n + 1)) := X.d_triangle _ _ _
        _ ≤ (∑ i ∈ Finset.range n, X.d (f i) (f (i + 1))) + X.d (f n) (f (n + 1)) := by
              gcongr
              exact dist_chain X f n
        _ = ∑ i ∈ Finset.range (n + 1), X.d (f i) (f (i + 1)) :=
              (Finset.sum_range_succ _ n).symm

/-! ## The Kalkulus I instance: the absolute value -/

/-- "A valós számtest": the reals with `d x y = |x - y|`. -/
@[reducible] def calcSpace : LawvereSpace := ofMetric ℝ

@[simp] theorem calcSpace_d (x y : ℝ) : calcSpace.d x y = |x - y| := Real.dist_eq x y

/-- "Nevezetes egyenlőtlenségek" (Kalkulus I): the triangle inequality for the absolute
value is precisely composition in `calcSpace`. -/
theorem abs_add_le' (x y : ℝ) : |x + y| ≤ |x| + |y| := by
  have := calcSpace.d_triangle x 0 (-y)
  simpa [Real.dist_eq, sub_neg_eq_add, abs_sub_comm] using this

/-- **Calculus corollary of the abstract chain theorem**: `|∑ aᵢ| ≤ ∑ |aᵢ|`. -/
theorem abs_sum_le_of_chain (a : ℕ → ℝ) (n : ℕ) :
    |∑ i ∈ Finset.range n, a i| ≤ ∑ i ∈ Finset.range n, |a i| := by
  have h := dist_chain calcSpace (fun k => ∑ i ∈ Finset.range k, a i) n
  simpa [Finset.sum_range_succ, abs_sub_comm] using h

/-! ## The Lineáris algebra I instance: the Euclidean length -/

/-- "A valós elem-`n`-esek köre" with `d u v = ‖u - v‖`, the Euclidean distance coming
from the inner product ("belső szorzat, vektorok hossza"). -/
@[reducible] def linAlgSpace (n : ℕ) : LawvereSpace := ofMetric (EuclideanSpace ℝ (Fin n))

@[simp] theorem linAlgSpace_d {n : ℕ} (u v : EuclideanSpace ℝ (Fin n)) :
    (linAlgSpace n).d u v = ‖u - v‖ := dist_eq_norm u v

/-- "Cauchy--Schwarz-egyenlőtlenség" (Lineáris algebra I). -/
theorem cauchy_schwarz {n : ℕ} (u v : EuclideanSpace ℝ (Fin n)) :
    |∑ i, u i * v i| ≤ ‖u‖ * ‖v‖ := by
  have h := abs_real_inner_le_norm u v
  simpa [real_inner_eq_re_inner, PiLp.inner_apply, RCLike.inner_apply, mul_comm] using h

/-- "Háromszög-egyenlőtlenség" (Lineáris algebra I): again exactly composition, now in
`linAlgSpace n`. -/
theorem norm_add_le' {n : ℕ} (u v : EuclideanSpace ℝ (Fin n)) : ‖u + v‖ ≤ ‖u‖ + ‖v‖ := by
  have := (linAlgSpace n).d_triangle u 0 (-v)
  simpa [dist_eq_norm, sub_neg_eq_add, norm_sub_rev] using this

/-- **Linear algebra corollary of the abstract chain theorem**: `‖∑ vᵢ‖ ≤ ∑ ‖vᵢ‖`.
Same proof, same theorem, different course. -/
theorem norm_sum_le_of_chain {n : ℕ} (v : ℕ → EuclideanSpace ℝ (Fin n)) (m : ℕ) :
    ‖∑ i ∈ Finset.range m, v i‖ ≤ ∑ i ∈ Finset.range m, ‖v i‖ := by
  have h := dist_chain (linAlgSpace n) (fun k => ∑ i ∈ Finset.range k, v i) m
  simpa [Finset.sum_range_succ, norm_sub_rev] using h

/-! ## The bridge: one notion, two courses -/

/-- **The overlap, formally.**  The length function `‖·‖ : ℝⁿ → ℝ` of the linear algebra
course is a morphism `linAlgSpace n ⟶ calcSpace` of the category `Met`, i.e. an enriched
functor: it carries the linear algebra distance to the calculus distance.  (Its
shortness, `| ‖u‖ - ‖v‖ | ≤ ‖u - v‖`, is again the triangle inequality.) -/
def lengthShort (n : ℕ) : linAlgSpace n ⟶ calcSpace where
  toFun u := ‖u‖
  short u v := by
    simpa using abs_norm_sub_norm_le u v

/-- On `ℝ¹` the Euclidean distance is the absolute value of the coordinate difference. -/
theorem euclid_one_dist (u v : EuclideanSpace ℝ (Fin 1)) : dist u v = |u 0 - v 0| := by
  rw [EuclideanSpace.dist_eq]
  simp [Real.dist_eq, Real.sqrt_sq_eq_abs]

/-- In dimension one the two syllabus items are literally the same: `calcSpace` and
`linAlgSpace 1` are isomorphic in `Met`, i.e. `|x - y|` *is* the Euclidean distance on
`ℝ¹`. -/
def calcIsoLinAlgOne : calcSpace ≅ linAlgSpace 1 where
  hom :=
    { toFun := fun x => WithLp.toLp 2 (fun _ => x)
      short := fun a b => by simp [euclid_one_dist, Real.dist_eq] }
  inv :=
    { toFun := fun u => u 0
      short := fun u v => by simp [euclid_one_dist, Real.dist_eq] }
  hom_inv_id := ShortMap.ext (funext fun _ => rfl)
  inv_hom_id := ShortMap.ext (funext fun u => by ext i; fin_cases i; rfl)

/-! ## Equivalence and invariance -/

/-- Isomorphism in `Met` is exactly *isometry*: an isomorphism preserves every distance
on the nose, so the distance function is the invariant of the common structure. -/
theorem iso_isometry {X Y : LawvereSpace} (e : X ≅ Y) (a b : X.carrier) :
    Y.d (e.hom.toFun a) (e.hom.toFun b) = X.d a b := by
  refine le_antisymm (e.hom.short a b) ?_
  have h := e.inv.short (e.hom.toFun a) (e.hom.toFun b)
  have ha : e.inv.toFun (e.hom.toFun a) = a := congrFun (congrArg ShortMap.toFun e.hom_inv_id) a
  have hb : e.inv.toFun (e.hom.toFun b) = b := congrFun (congrArg ShortMap.toFun e.hom_inv_id) b
  rwa [ha, hb] at h

/-- "Being isometric" is an equivalence relation — the common notion of equivalence for
the shared structure. -/
theorem nonempty_iso_equivalence :
    Equivalence (fun X Y : LawvereSpace => Nonempty (X ≅ Y)) :=
  ⟨fun X => ⟨Iso.refl X⟩, fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e⟩ ⟨f⟩ => ⟨e.trans f⟩⟩

/-- A concrete instance of the invariance: under the dimension-one identification the
calculus distance and the linear algebra distance agree. -/
theorem calc_dist_eq_linAlg_dist (x y : ℝ) :
    (linAlgSpace 1).d (calcIsoLinAlgOne.hom.toFun x) (calcIsoLinAlgOne.hom.toFun y)
      = |x - y| := by
  simpa using iso_isometry calcIsoLinAlgOne x y

end TriangleOverlap

end
