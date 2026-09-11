import Mathlib

/-!
# The Darboux gadget: an abstract convexity structure and the intermediate-value pattern

Mathlib's Darboux theorem (`Set.OrdConnected.image_deriv`) says:

> the image of a derivative is order-connected — a derivative has the intermediate value
> property even when it is not continuous.

The Kasami/AB/APN part of this library contains a statement that *looks* completely
different but is proved by the same move:

> the image of the discrete derivative `D a f x = f (x + a) - f x` of a Gold-type power
> map is an affine subspace (a coset of an `F₂`-subspace) — a "discrete interval".

This file **factors out the common gadget**.  The abstraction is a *convexity structure*
(a closure system) `C` on the codomain, and the property

  `HasDarbouxOn C Adm D  :=  ∀ f, Adm f → C.IsConvex (Set.range (D f))`

"the range of every admissible derivative is convex".  Instantiating `C` at
order-connected subsets of `ℝ` gives back Mathlib's Darboux theorem; instantiating it at
affine subsets of a characteristic-two group gives the Kasami/Gold statement
(`RequestProject/Gadgets/DarbouxCharTwo.lean`).

Two further structural questions are answered here, and this is what makes the gadget
useful rather than decorative:

* **Transport (functoriality).**  A convexity structure can be pushed along an equivalence
  of codomains (`Convexity.map`), and the Darboux property transports *both ways*
  (`hasDarbouxOn_conj_iff`).  This is the mechanism behind the Morita-style comparison in
  `DarbouxCharTwo.lean`: the field picture `GF(2ⁿ)` and the coordinate picture
  `(ZMod 2)ⁿ` (equivalently, the matrix algebra picture) satisfy *equivalent* Darboux
  statements, and the equivalence is machine-checked, not asserted.
* **Faithfulness.**  A convexity structure carries information only if some set fails to
  be convex (`Convexity.Faithful`).  The *indiscrete* structure, in which every set is
  convex, makes the Darboux property vacuously true for every operator
  (`hasDarbouxOn_indiscrete`) — the exact shape of a non-faithful functor: it maps a
  sharp theorem to a true but empty one.
-/

namespace Gadget

universe u v w

/-! ## 1. Convexity structures -/

/-- A **convexity structure** (a closure system) on `β`: a family of "convex" sets that
contains the whole space and is closed under arbitrary intersections.

This is the least structure needed to state a Darboux-type theorem: it gives a notion of
"connected/convex subset" and hence a hull operator, without any order, topology or
linearity. -/
structure Convexity (β : Type u) where
  /-- The distinguished family of convex subsets. -/
  IsConvex : Set β → Prop
  /-- The whole space is convex. -/
  univ_mem : IsConvex Set.univ
  /-- Convex sets are closed under arbitrary intersections. -/
  sInter_mem : ∀ 𝒞 : Set (Set β), (∀ S ∈ 𝒞, IsConvex S) → IsConvex (⋂₀ 𝒞)

namespace Convexity

variable {β : Type u} {γ : Type v}

/-- The convex hull of a set: the intersection of all convex sets containing it. -/
def hull (C : Convexity β) (S : Set β) : Set β := ⋂₀ {T | C.IsConvex T ∧ S ⊆ T}

theorem subset_hull (C : Convexity β) (S : Set β) : S ⊆ C.hull S := by
  intro x hx T hT
  exact hT.2 hx

theorem isConvex_hull (C : Convexity β) (S : Set β) : C.IsConvex (C.hull S) :=
  C.sInter_mem _ fun _ hT => hT.1

theorem hull_minimal (C : Convexity β) {S T : Set β} (hT : C.IsConvex T) (hST : S ⊆ T) :
    C.hull S ⊆ T := fun _ hx => hx T ⟨hT, hST⟩

theorem hull_eq_self_iff (C : Convexity β) (S : Set β) : C.hull S = S ↔ C.IsConvex S := by
  constructor
  · intro h; rw [← h]; exact C.isConvex_hull S
  · intro h
    exact subset_antisymm (C.hull_minimal h subset_rfl) (C.subset_hull S)

/-! ### Faithfulness: does the structure carry information? -/

/-- A convexity structure is **faithful** if convexity is a nontrivial condition, i.e. some
set is not convex.  A non-faithful structure turns every Darboux-type statement into a
tautology. -/
def Faithful (C : Convexity β) : Prop := ∃ S : Set β, ¬ C.IsConvex S

/-- The **indiscrete** convexity structure: every set counts as convex.  This is the image
of any convexity structure under the "forget everything" functor. -/
def indiscrete (β : Type u) : Convexity β where
  IsConvex := fun _ => True
  univ_mem := trivial
  sInter_mem := fun _ _ => trivial

@[simp] theorem indiscrete_isConvex (S : Set β) : (indiscrete β).IsConvex S := trivial

/-- The indiscrete structure is not faithful. -/
theorem not_faithful_indiscrete : ¬ (indiscrete β).Faithful := by
  rintro ⟨S, hS⟩
  exact hS trivial

/-! ### Transport along an equivalence -/

/-- Push a convexity structure forward along an equivalence of the ambient type. -/
def map (C : Convexity β) (e : β ≃ γ) : Convexity γ where
  IsConvex S := C.IsConvex (e ⁻¹' S)
  univ_mem := by simpa using C.univ_mem
  sInter_mem := by
    intro 𝒞 h
    have hpre : e ⁻¹' ⋂₀ 𝒞 = ⋂₀ ((fun S => e ⁻¹' S) '' 𝒞) := by
      rw [Set.sInter_image]
      exact Set.preimage_sInter
    rw [hpre]
    refine C.sInter_mem _ ?_
    rintro T ⟨S, hS, rfl⟩
    exact h S hS

@[simp] theorem map_isConvex (C : Convexity β) (e : β ≃ γ) (S : Set γ) :
    (C.map e).IsConvex S ↔ C.IsConvex (e ⁻¹' S) := Iff.rfl

/-- Convexity transports along an equivalence: `S` is convex iff its image is convex in the
transported structure. -/
theorem isConvex_image_iff (C : Convexity β) (e : β ≃ γ) (S : Set β) :
    (C.map e).IsConvex (e '' S) ↔ C.IsConvex S := by
  simp [Equiv.preimage_image]

/-- Transporting along an equivalence preserves faithfulness in both directions. -/
theorem faithful_map_iff (C : Convexity β) (e : β ≃ γ) : (C.map e).Faithful ↔ C.Faithful := by
  constructor
  · rintro ⟨S, hS⟩
    exact ⟨e ⁻¹' S, hS⟩
  · rintro ⟨S, hS⟩
    exact ⟨e '' S, by rwa [isConvex_image_iff]⟩

end Convexity

/-! ## 2. The Darboux property -/

variable {α α' : Type w} {β : Type u} {γ : Type v}

/-- **The Darboux gadget.**  A "derivative operator" `D`, defined on a class `Adm` of
admissible functions, has the *Darboux property* relative to a convexity structure `C` if
the range of every admissible derivative is convex.

* `C = ordConvexity`, `Adm = differentiable`, `D = deriv` — Mathlib's Darboux theorem.
* `C = affineConvexity`, `Adm = quadratic`, `D = D a` — the Gold/Kasami statement. -/
def HasDarbouxOn (C : Convexity β) (Adm : (α → β) → Prop) (D : (α → β) → α → β) : Prop :=
  ∀ f, Adm f → C.IsConvex (Set.range (D f))

/-- In an indiscrete (non-faithful) context every operator has the Darboux property: the
theorem survives the functor, but with no content left. -/
theorem hasDarbouxOn_indiscrete (Adm : (α → β) → Prop) (D : (α → β) → α → β) :
    HasDarbouxOn (Convexity.indiscrete β) Adm D := fun _ _ => trivial

/-! ### Transport of the Darboux property

Conjugating the operator by an equivalence `e` of codomains and an equivalence `u` of
domains, and transporting the convexity structure along `e`, gives an *equivalent*
statement.  This is the precise sense in which the Darboux gadget is functorial. -/

/-- The conjugated operator `g ↦ e ∘ D (e⁻¹ ∘ g ∘ u⁻¹) ∘ u`. -/
def conjOp (e : β ≃ γ) (u : α' ≃ α) (D : (α → β) → α → β) : (α' → γ) → α' → γ :=
  fun g x => e (D (fun y => e.symm (g (u.symm y))) (u x))

/-- The conjugated admissibility class. -/
def conjAdm (e : β ≃ γ) (u : α' ≃ α) (Adm : (α → β) → Prop) : (α' → γ) → Prop :=
  fun g => Adm (fun y => e.symm (g (u.symm y)))

theorem range_conjOp (e : β ≃ γ) (u : α' ≃ α) (D : (α → β) → α → β) (g : α' → γ) :
    Set.range (conjOp e u D g) = e '' Set.range (D (fun y => e.symm (g (u.symm y)))) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨_, ⟨u x, rfl⟩, rfl⟩
  · rintro ⟨z, ⟨x, rfl⟩, rfl⟩
    exact ⟨u.symm x, by simp [conjOp]⟩

/-- **Transport theorem.**  The Darboux property holds in the original context iff it holds
in the transported one.  Nothing is gained or lost by moving the statement along an
equivalence of contexts — the two formalisations are provably the same theorem. -/
theorem hasDarbouxOn_conj_iff (C : Convexity β) (Adm : (α → β) → Prop)
    (D : (α → β) → α → β) (e : β ≃ γ) (u : α' ≃ α) :
    HasDarbouxOn (C.map e) (conjAdm e u Adm) (conjOp e u D) ↔ HasDarbouxOn C Adm D := by
  constructor
  · intro h f hf
    have hg : conjAdm e u Adm (fun x => e (f (u x))) := by
      simpa [conjAdm] using hf
    have h2 := h (fun x => e (f (u x))) hg
    rw [range_conjOp] at h2
    rw [Convexity.isConvex_image_iff] at h2
    simpa using h2
  · intro h g hg
    rw [range_conjOp, Convexity.isConvex_image_iff]
    exact h _ hg

/-! ## 3. Instance 1: Mathlib's Darboux theorem over `ℝ` -/

/-- The convexity structure of **order-connected** subsets of a preorder: the classical
notion of "interval" behind the intermediate value property. -/
def ordConvexity (β : Type u) [Preorder β] : Convexity β where
  IsConvex := Set.OrdConnected
  univ_mem := Set.ordConnected_univ
  sInter_mem := fun _ h => Set.ordConnected_sInter h

/-- The order convexity structure on `ℝ` **is** faithful: `{0, 1}` is not an interval.
Contrast with `Convexity.not_faithful_indiscrete`. -/
theorem faithful_ordConvexity_real : (ordConvexity ℝ).Faithful := by
  refine ⟨{0, 1}, fun h => ?_⟩
  have hmem : (2⁻¹ : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> norm_num
  have hin := h.out (by simp : (0 : ℝ) ∈ ({0, 1} : Set ℝ))
    (by simp : (1 : ℝ) ∈ ({0, 1} : Set ℝ)) hmem
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hin
  rcases hin with h0 | h0 <;> norm_num at h0

/-- **Mathlib's Darboux theorem as an instance of the gadget.**  For everywhere
differentiable `f : ℝ → ℝ`, the range of `deriv f` is order-connected. -/
theorem real_hasDarboux :
    HasDarbouxOn (ordConvexity ℝ) (fun f : ℝ → ℝ => ∀ x, DifferentiableAt ℝ f x) deriv := by
  intro f hf
  have h : Set.OrdConnected (deriv f '' Set.univ) :=
    Set.ordConnected_univ.image_deriv fun x _ => hf x
  simpa [Set.image_univ] using h

/-- Darboux is a genuine theorem in the real context: an arbitrary function need **not**
have order-connected range, so the conclusion is not automatic.  (Witness: the sign-like
function `fun x => if x < 0 then 0 else 1`.) -/
theorem exists_range_not_ordConnected :
    ∃ f : ℝ → ℝ, ¬ (ordConvexity ℝ).IsConvex (Set.range f) := by
  refine ⟨fun x => if x < 0 then 0 else 1, fun h => ?_⟩
  have h0 : (0 : ℝ) ∈ Set.range (fun x : ℝ => if x < 0 then (0 : ℝ) else 1) :=
    ⟨-1, by norm_num⟩
  have h1 : (1 : ℝ) ∈ Set.range (fun x : ℝ => if x < 0 then (0 : ℝ) else 1) :=
    ⟨1, by norm_num⟩
  have hmem : (2⁻¹ : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> norm_num
  obtain ⟨x, hx⟩ := h.out h0 h1 hmem
  by_cases hxlt : x < 0 <;> simp [hxlt] at hx

/-! ## 4. The non-faithful image of Darboux

Forgetting the order (which is exactly what happens when the ambient field is replaced by
a field of characteristic two, cf. `Morita.no_linear_order_of_charTwo`) sends the order
convexity structure to a structure in which the theorem is empty.  The following statement
makes the loss precise. -/

/-- The forgetful passage `ordConvexity ℝ ↝ indiscrete ℝ` destroys the content: a set that
witnesses faithfulness of the order structure becomes convex downstairs, and *every*
operator has the Darboux property there. -/
theorem darboux_collapses_in_indiscrete :
    (∃ S : Set ℝ, ¬ (ordConvexity ℝ).IsConvex S ∧ (Convexity.indiscrete ℝ).IsConvex S) ∧
      ∀ (Adm : (ℝ → ℝ) → Prop) (D : (ℝ → ℝ) → ℝ → ℝ),
        HasDarbouxOn (Convexity.indiscrete ℝ) Adm D := by
  refine ⟨?_, fun Adm D => hasDarbouxOn_indiscrete Adm D⟩
  obtain ⟨S, hS⟩ := faithful_ordConvexity_real
  exact ⟨S, hS, trivial⟩

end Gadget
