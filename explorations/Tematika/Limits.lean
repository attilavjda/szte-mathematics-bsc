import Mathlib
import Atlas.Duality.Convolution
import Atlas.Moment.Parseval

/-!
# Tematika 07 — "Függvények határértéke.  A határérték formális tulajdonságai,
műveletek."

**Syllabus item.**  *Függvények határértéke.  A határérték formális
tulajdonságai, műveletek.  Elemi határérték-számítási technikák.*

**Categorical reading.**  A limit is a **colimit over a filter**: `lim_{x→a} f`
is the value the diagram of restrictions of `f` to neighbourhoods of `a`
converges to, i.e. a universal cocone.  Two structural facts organise the whole
chapter, and both survive the passage to a finite ground object:

1. *Uniqueness of the limit* — a universal object is unique.  Over a finite
   group the corresponding universal gadget is the **invariant functional**
   ("integration"), and uniqueness of the limit becomes *uniqueness of the Haar
   functional*: every translation-invariant linear functional on `K → ℂ` is a
   scalar multiple of the total sum
   (`Tematika.Limits.invariant_functional_eq_smul_sum`).  Translation
   invariance itself, `∑ f (x + a) = ∑ f x`, is
   `Tematika.Limits.sum_translate`.
2. *Műveletek: a limit of a product is the product of the limits* — the
   universal construction is **monoidal**.  This is exactly the property the
   library's duality layer is built on: the Fourier transform takes convolution
   to the pointwise product (`Tematika.Limits.transform_conv_eq_mul`, from
   `Atlas.transform_conv`) and sums to sums (it is a `ℂ`-linear map), i.e. it
   is a monoidal functor from `(ℂ[K], ⋆)` to `(ℂ^K, ·)` sending the unit `δ₀`
   to the unit `1` (`Tematika.Limits.transform_delta`).  Every "elemi
   határérték-számítási technika" of Calculus I — split the expression into
   pieces whose limits are known and multiply — is used in the library in this
   form: the count is a triple convolution, so its transform is a triple
   product, so the count is computed frequency by frequency
   (`Atlas.tripleConv_zero_eq_transform_average`).

The dual statement, "the limit of a sum of squares controls the pieces", is
Parseval (`Atlas.parseval`), the isometry property of the same functor.
-/

namespace Tematika.Limits

open Finset

variable {K : Type*} [Field K] [Fintype K] [DecidableEq K]

omit [DecidableEq K] in
/-- **Translation invariance of the total sum**: the finite analogue of "the
integral does not see a shift", and the reason the limit-like functional
`f ↦ ∑ f` is well behaved. -/
theorem sum_translate (f : K → ℂ) (a : K) : ∑ x : K, f (x + a) = ∑ x : K, f x :=
  Fintype.sum_equiv (Equiv.addRight a) _ _ fun _ => rfl

/-- **Uniqueness of the limit, in the finite context: uniqueness of the Haar
functional.**  Any translation-invariant linear functional is the total sum,
scaled by its value on the unit mass `δ₀`.  (Over `ℝ` the corresponding
statement is that the limit along a filter, if it exists, is unique.) -/
theorem invariant_functional_eq_smul_sum (L : (K → ℂ) →ₗ[ℂ] ℂ)
    (hinv : ∀ (f : K → ℂ) (a : K), L (fun x => f (x + a)) = L f) (f : K → ℂ) :
    L f = L (fun x => if x = 0 then 1 else 0) * ∑ x : K, f x := by
  classical
  have hd : ∀ y : K, L (fun x => if x = y then (1 : ℂ) else 0)
      = L (fun x => if x = 0 then (1 : ℂ) else 0) := by
    intro y
    have h := hinv (fun x => if x = 0 then (1 : ℂ) else 0) (-y)
    simpa [add_neg_eq_zero] using h
  have hf : (∑ y : K, f y • (fun x => if x = y then (1 : ℂ) else 0)) = f := by
    funext x
    rw [Finset.sum_apply]
    simp
  calc L f = L (∑ y : K, f y • (fun x => if x = y then (1 : ℂ) else 0)) := by rw [hf]
    _ = ∑ y : K, f y * L (fun x => if x = 0 then (1 : ℂ) else 0) := by
        rw [map_sum]
        exact Finset.sum_congr rfl fun y _ => by rw [map_smul, hd y, smul_eq_mul]
    _ = L (fun x => if x = 0 then (1 : ℂ) else 0) * ∑ x : K, f x := by
        rw [← Finset.sum_mul]; ring

omit [DecidableEq K] in
/-- **Műveletek: the transform is multiplicative.**  Convolution goes to the
pointwise product — the finite avatar of "the limit of a product is the product
of the limits", and the monoidality of the duality functor. -/
theorem transform_conv_eq_mul (ψ : AddChar K ℂ) (f g : K → ℂ) :
    Atlas.transform ψ (Atlas.conv f g) = fun a => Atlas.transform ψ f a * Atlas.transform ψ g a :=
  funext fun a => Atlas.transform_conv ψ f g a

/-- **The unit goes to the unit.**  The transform of the point mass at `0` is
the constant function `1`; with `Tematika.Limits.transform_conv_eq_mul` this
says the transform is a *monoidal* functor. -/
theorem transform_delta (ψ : AddChar K ℂ) :
    Atlas.transform ψ (fun x => if x = 0 then 1 else 0) = fun _ => 1 := by
  funext a
  simp [Atlas.transform_apply, Atlas.pairing]

/-- **The unit of convolution.**  `δ₀ ⋆ f = f`. -/
theorem conv_delta (f : K → ℂ) :
    Atlas.conv (fun x => if x = 0 then 1 else 0) f = f := by
  funext x
  simp [Atlas.conv]

/-- **Pontryagin duality: the dualising functor is an involution.**  For a
finite abelian group the canonical map into the double dual is bijective.  This
is the structural reason Fourier inversion exists — the categorical form of
"inverz függvény" for the duality functor, and the fact behind
`Atlas.inversion_at_zero`, the one inversion instance the library needs. -/
theorem doubleDual_bijective {A : Type*} [AddCommGroup A] [Finite A] :
    Function.Bijective (AddChar.doubleDualEmb (A := A) (M := ℂ)) :=
  AddChar.doubleDualEmb_bijective

omit [DecidableEq K] in
/-- **Additivity ("the limit of a sum is the sum of the limits").**  The
transform is a linear map, so this is `map_add`. -/
theorem transform_add (ψ : AddChar K ℂ) (f g : K → ℂ) :
    Atlas.transform ψ (f + g) = Atlas.transform ψ f + Atlas.transform ψ g :=
  map_add _ _ _

end Tematika.Limits
