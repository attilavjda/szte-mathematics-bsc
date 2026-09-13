import Mathlib
import Atlas.Relation.SlopeFibre
import Genesis.Statement.Defs

/-!
# Tematika 05 — "Értelmezési tartomány, értékkészlet, inverz függvény, összetétel"

**Syllabus item.**  *Értelmezési tartomány, értékkészlet, inverz függvény,
összetétel.*

**Categorical reading.**  These four notions are the four primitives of a
category, read in **Set**:

* *értelmezési tartomány / értékkészlet* — the source and target of a
  morphism, together with its **(epi, mono) factorisation** `α ↠ im f ↪ β`.
  The image is not a set one describes by hand but the object through which the
  morphism factors, unique up to a unique isomorphism
  (`Tematika.DomainRange.exists_image_factorisation`,
  `Tematika.DomainRange.image_factorisation_unique`);
* *összetétel* — composition of morphisms;
* *inverz függvény* — an **isomorphism** in **Set**, i.e. a morphism with a
  two-sided inverse (`Tematika.DomainRange.iso_iff_bijective`).

**Where the library uses it.**  The object the whole proof is about, `Δ`, is
the image object of the epi–mono factorisation of the derivative map
(`Tematika.DomainRange.derivativeImage_is_image`): the counting argument never
mentions the derivative itself, only the image object and its cardinality —
"az értékkészlet" is the datum that matters.  The slope map is a *partial*
function, whose domain of definition (`y ≠ z`) is exactly Calculus I's
értelmezési tartomány of a rational function, and its **fibres** are the level
sets used to fibre the count
(`Atlas.mem_solutions_slope_iff_of_ne`, `Atlas/Count/Fibration.lean`).
-/

namespace Tematika.DomainRange

variable {α β : Type*}

/-- **Epi–mono factorisation in `Set`.**  Every function factors as a
surjection onto its image followed by an injection: this is the categorical
content of "értelmezési tartomány / értékkészlet". -/
theorem exists_image_factorisation (f : α → β) :
    ∃ (e : α → Set.range f) (m : Set.range f → β),
      Function.Surjective e ∧ Function.Injective m ∧ ∀ a, m (e a) = f a := by
  refine ⟨fun a => ⟨f a, ⟨a, rfl⟩⟩, Subtype.val, ?_, Subtype.val_injective, fun _ => rfl⟩
  rintro ⟨b, a, rfl⟩
  exact ⟨a, rfl⟩

/-- **The image object is unique up to a unique isomorphism.**  Any other
factorisation of `f` into a surjection followed by an injection is comparable
with the canonical one by exactly one bijection over `β`. -/
theorem image_factorisation_unique (f : α → β) {C : Type*} (e : α → C) (m : C → β)
    (he : Function.Surjective e) (hm : Function.Injective m) (hcomp : ∀ a, m (e a) = f a) :
    ∃! i : C ≃ Set.range f, ∀ c, ((i c : β)) = m c := by
  have hmem : ∀ c : C, m c ∈ Set.range f := by
    intro c
    obtain ⟨a, rfl⟩ := he c
    exact ⟨a, (hcomp a).symm⟩
  have hbij : Function.Bijective (fun c : C => (⟨m c, hmem c⟩ : Set.range f)) := by
    constructor
    · intro c c' h
      exact hm (Subtype.ext_iff.mp h)
    · rintro ⟨b, a, rfl⟩
      exact ⟨e a, by simpa using hcomp a⟩
  refine ⟨Equiv.ofBijective _ hbij, fun _ => rfl, ?_⟩
  intro j hj
  exact Equiv.ext fun c => Subtype.ext (by simpa using hj c)

/-- **Inverz függvény = isomorphism in `Set`.** -/
theorem iso_iff_bijective (f : α → β) :
    Function.Bijective f ↔ ∃ g : β → α, (∀ a, g (f a) = a) ∧ ∀ b, f (g b) = b := by
  constructor
  · intro h
    obtain ⟨g, h₁, h₂⟩ := Function.bijective_iff_has_inverse.mp h
    exact ⟨g, h₁, h₂⟩
  · rintro ⟨g, h₁, h₂⟩
    exact Function.bijective_iff_has_inverse.mpr ⟨g, h₁, h₂⟩

section Library

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

/-- **`Δ` is the image object.**  The set the counting argument runs on is the
image of the derivative map, i.e. the middle object of its epi–mono
factorisation. -/
theorem derivativeImage_is_image (k : ℕ) :
    ((Genesis.Kasami.derivativeImage k K : Finset K) : Set K)
      = Set.range (Genesis.Kasami.kasamiDerivative k) := by
  simp [Genesis.Kasami.derivativeImage]

omit [Fintype K] [DecidableEq K] in
/-- **Értelmezési tartomány of the slope.**  Off the locus `y = z` the slope map
is defined and inverts the relation; the excluded locus is exactly the pole of
the rational function `(x + z)/(y + z)`. -/
theorem slope_defined_off_diagonal (h2 : Atlas.IsTwoTorsion K) {x y z : K} (hyz : y ≠ z)
    (ρ : K) :
    ((x, y, z) : K × K × K) ∈ Atlas.solutions (M := K) 1 ρ (1 + ρ)
      ↔ ρ = Atlas.slopeOfTriple x y z :=
  Atlas.mem_solutions_slope_iff_of_ne h2 hyz ρ

end Library

end Tematika.DomainRange
