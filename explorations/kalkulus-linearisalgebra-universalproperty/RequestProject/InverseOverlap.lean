import Mathlib

/-!
# One syllabus element shared by *Kalkulus I* and *Lineáris algebra I*

Reading the two course descriptions (`Tantárgy tartalma`):

* **Kalkulus I (MBLK37E)** lists, among the topics,
  *"…exponenciális függvények és inverzeik. Értelmezési tartomány, értékkészlet,
  inverz függvény, összetétel."* — i.e. **composition of functions and the inverse
  function**.
* **Lineáris algebra I (MBLK15E)** lists
  *"Mátrixegyenletek, mátrixok inverze…"* and *"nemelfajuló mátrixok, Cramer-szabály"*
  — i.e. **matrix multiplication (= composition of linear maps) and the inverse matrix**.

The common element is therefore: *an inverse with respect to composition*.
Category theory makes the overlap precise: both courses study **isomorphisms in a
category**, the calculus course in the category of sets (`Type`), the linear algebra
course in the category of `ℝ`-modules (`ModuleCat ℝ`).

The file is organised as follows.

* `SyllabusOverlap.inverse_unique` — the *one* abstract theorem, valid in **any** category:
  a two-sided inverse of a morphism is unique.
* `SyllabusOverlap.expIso` / `SyllabusOverlap.log_eq_of_inverse` — the calculus instance:
  `Real.exp : ℝ → (0, ∞)` is an isomorphism in `Type`, and `Real.log` is its *only*
  two-sided inverse (obtained from the abstract theorem, not re-proved).
* `SyllabusOverlap.matrixIso` / `SyllabusOverlap.matrix_inverse_eq_of_inverse` — the
  linear algebra instance: a nondegenerate matrix gives an isomorphism in `ModuleCat ℝ`
  and `M⁻¹` is its *only* two-sided inverse (again obtained from the abstract theorem).
* `SyllabusOverlap.linearIso_bijective` — the bridge: the forgetful functor
  `ModuleCat ℝ ⥤ Type` carries the linear algebra notion of invertibility to the
  calculus notion (a bijection of underlying sets), because *every* functor preserves
  isomorphisms.  This is the sense in which the two syllabus items are the same item.
* `SyllabusOverlap.nonempty_iso_equivalence`, `SyllabusOverlap.cardinality_invariant`,
  `SyllabusOverlap.dimension_invariant` — isomorphism is the common notion of
  *equivalence*, and each course has its *invariant* for it (cardinality of a set,
  dimension of `ℝⁿ`).
-/

open CategoryTheory Matrix

noncomputable section

namespace SyllabusOverlap

/-! ## The common abstract content -/

/-- **The shared theorem.**  In an arbitrary category, a two-sided inverse of a morphism
is unique.  Both "az inverz függvény egyértelmű" (Kalkulus I) and "a mátrix inverze
egyértelmű" (Lineáris algebra I) are instances of this single statement. -/
theorem inverse_unique {C : Type*} [Category C] {X Y : C} (f : X ⟶ Y) (g g' : Y ⟶ X)
    (hg : f ≫ g = 𝟙 X) (hg' : g' ≫ f = 𝟙 Y) : g = g' := by
  calc g = 𝟙 Y ≫ g := (Category.id_comp g).symm
    _ = (g' ≫ f) ≫ g := by rw [hg']
    _ = g' ≫ (f ≫ g) := by rw [Category.assoc]
    _ = g' ≫ 𝟙 X := by rw [hg]
    _ = g' := Category.comp_id g'

/-! ## The Kalkulus I instance: `exp` and `log` -/

/-- The exponential function viewed as a map of sets `ℝ → (0, ∞)`. -/
def expMap : ℝ → Set.Ioi (0 : ℝ) := fun x => ⟨Real.exp x, Real.exp_pos x⟩

/-- The logarithm viewed as a map of sets `(0, ∞) → ℝ`. -/
def logMap : Set.Ioi (0 : ℝ) → ℝ := fun y => Real.log y

/-- "Exponenciális függvény és inverze": `exp` is an isomorphism in the category of sets. -/
def expIso : (ℝ : Type) ≅ (Set.Ioi (0 : ℝ) : Type) where
  hom := expMap
  inv := logMap
  hom_inv_id := by
    funext x
    simp [expMap, logMap]
  inv_hom_id := by
    funext y
    have hy : (0 : ℝ) < (y : ℝ) := y.2
    ext
    simp [expMap, logMap, Real.exp_log hy]

/-- **Calculus instance of `inverse_unique`.**  Any left inverse of the exponential
function is the logarithm (a two-sided inverse is in particular a left inverse). -/
theorem log_eq_of_inverse (g : Set.Ioi (0 : ℝ) → ℝ)
    (h₁ : ∀ x : ℝ, g (expMap x) = x) :
    g = logMap := by
  have hg : expIso.hom ≫ (g : (Set.Ioi (0 : ℝ) : Type) ⟶ (ℝ : Type)) = 𝟙 (ℝ : Type) := by
    funext x; exact h₁ x
  have hg' : expIso.inv ≫ expIso.hom = 𝟙 (Set.Ioi (0 : ℝ) : Type) := expIso.inv_hom_id
  -- the abstract theorem, applied in `Type`
  have := inverse_unique expIso.hom g expIso.inv hg hg'
  simpa [expIso] using this

/-- Symmetrically: `exp` is the unique left inverse of `log`. -/
theorem exp_eq_of_inverse (f : ℝ → Set.Ioi (0 : ℝ))
    (h₁ : ∀ y : Set.Ioi (0 : ℝ), f (logMap y) = y) :
    f = expMap := by
  have hg : expIso.inv ≫ (f : (ℝ : Type) ⟶ (Set.Ioi (0 : ℝ) : Type))
      = 𝟙 (Set.Ioi (0 : ℝ) : Type) := by
    funext y; exact h₁ y
  have hg' : expIso.hom ≫ expIso.inv = 𝟙 (ℝ : Type) := expIso.hom_inv_id
  have := inverse_unique expIso.inv f expIso.hom hg hg'
  simpa [expIso] using this

/-! ## The Lineáris algebra I instance: nondegenerate matrices -/

variable {n : ℕ}

/-- The `ℝ`-module `ℝⁿ` ("a valós elem-`n`-esek köre") as an object of `ModuleCat ℝ`. -/
abbrev Rn (n : ℕ) : ModuleCat ℝ := ModuleCat.of ℝ (Fin n → ℝ)

/-- A matrix, viewed as a morphism of `ℝ`-modules `ℝⁿ ⟶ ℝⁿ`. -/
def matMap (M : Matrix (Fin n) (Fin n) ℝ) : Rn n ⟶ Rn n := ModuleCat.ofHom (Matrix.toLin' M)

@[simp] theorem matMap_comp (M N : Matrix (Fin n) (Fin n) ℝ) :
    matMap M ≫ matMap N = matMap (N * M) := by
  ext x
  simp [matMap, Matrix.toLin'_mul]

@[simp] theorem matMap_one : matMap (1 : Matrix (Fin n) (Fin n) ℝ) = 𝟙 (Rn n) := by
  ext x
  simp [matMap]

theorem matMap_injective {M N : Matrix (Fin n) (Fin n) ℝ} (h : matMap M = matMap N) : M = N := by
  have : Matrix.toLin' M = Matrix.toLin' N := congrArg ModuleCat.Hom.hom h
  exact Matrix.toLin'.injective this

/-- "Nemelfajuló mátrix": a matrix with invertible determinant is an isomorphism in
`ModuleCat ℝ`. -/
def matrixIso (M : Matrix (Fin n) (Fin n) ℝ) (hM : IsUnit M.det) : Rn n ≅ Rn n where
  hom := matMap M
  inv := matMap M⁻¹
  hom_inv_id := by rw [matMap_comp, Matrix.nonsing_inv_mul M hM, matMap_one]
  inv_hom_id := by rw [matMap_comp, Matrix.mul_nonsing_inv M hM, matMap_one]

/-- **Linear algebra instance of `inverse_unique`.**  A two-sided inverse matrix of a
nondegenerate matrix is `M⁻¹`.  The proof is the abstract categorical theorem, applied in
`ModuleCat ℝ`. -/
theorem matrix_inverse_eq_of_inverse (M N : Matrix (Fin n) (Fin n) ℝ) (hM : IsUnit M.det)
    (h : M * N = 1) : N = M⁻¹ := by
  have hNM : N * M = 1 := mul_eq_one_comm.mp h
  have hg : matMap M ≫ matMap N = 𝟙 (Rn n) := by
    rw [matMap_comp, hNM, matMap_one]
  have hg' : matMap M⁻¹ ≫ matMap M = 𝟙 (Rn n) := by
    rw [matMap_comp, Matrix.mul_nonsing_inv M hM, matMap_one]
  exact matMap_injective (inverse_unique (matMap M) (matMap N) (matMap M⁻¹) hg hg')

/-! ## The bridge: one notion, two courses -/

/-- **The overlap, formally.**  Applying the forgetful functor `ModuleCat ℝ ⥤ Type` to the
linear algebra isomorphism produces exactly the calculus notion of an invertible map:
a bijection of the underlying sets.  Every functor preserves isomorphisms, so the linear
algebra syllabus item is carried onto the calculus syllabus item. -/
theorem linearIso_bijective (M : Matrix (Fin n) (Fin n) ℝ) (hM : IsUnit M.det) :
    Function.Bijective (fun x : Fin n → ℝ => M *ᵥ x) := by
  have h : IsIso ((CategoryTheory.forget (ModuleCat ℝ)).map (matrixIso M hM).hom) :=
    ((CategoryTheory.forget (ModuleCat ℝ)).mapIso (matrixIso M hM)).isIso_hom
  have hb : Function.Bijective ((CategoryTheory.forget (ModuleCat ℝ)).map (matrixIso M hM).hom) :=
    (CategoryTheory.isIso_iff_bijective _).mp h
  simpa [matrixIso, matMap, Matrix.toLin'_apply] using hb

/-- Conversely, in the category of sets a morphism is an isomorphism exactly when it is a
bijective function; this is the calculus course's characterisation of invertibility, and it
is what `inverse_unique` specialises to there. -/
theorem type_isIso_iff_bijective {X Y : Type} (f : X ⟶ Y) :
    IsIso f ↔ Function.Bijective f := CategoryTheory.isIso_iff_bijective f

/-! ## Isomorphism as the common notion of equivalence, and its invariants -/

/-- "Being isomorphic" is an equivalence relation in every category: this single statement
covers both "a két halmaz kölcsönösen egyértelműen megfeleltethető" (Kalkulus I) and
"a két vektortér izomorf" (Lineáris algebra I). -/
theorem nonempty_iso_equivalence {C : Type*} [Category C] :
    Equivalence (fun X Y : C => Nonempty (X ≅ Y)) :=
  ⟨fun X => ⟨Iso.refl X⟩, fun ⟨e⟩ => ⟨e.symm⟩, fun ⟨e⟩ ⟨f⟩ => ⟨e.trans f⟩⟩

/-- An invariant on the calculus side: isomorphic objects of `Type` (i.e. sets in bijection,
"kölcsönösen egyértelmű megfeleltetés") have the same cardinality. -/
theorem cardinality_invariant {X Y : Type} (h : X ≅ Y) : Cardinal.mk X = Cardinal.mk Y :=
  Cardinal.mk_congr h.toEquiv

/-- The matching invariant on the linear algebra side: isomorphic objects of `ModuleCat ℝ`
of the form `ℝⁿ` have the same dimension `n` ("a dimenzió izomorfia-invariáns"). -/
theorem dimension_invariant {n m : ℕ} (h : Rn n ≅ Rn m) : n = m := by
  have e : (Fin n → ℝ) ≃ₗ[ℝ] (Fin m → ℝ) := h.toLinearEquiv
  simpa using e.finrank_eq

end SyllabusOverlap

end

