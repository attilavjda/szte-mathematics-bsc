import Mathlib
import Analizis.Ch06a_Differencialhatosag

/-!
# Leindler László: Analízis — 6. fejezet (folytatás)

## 6.3–6.9. Néhány elemi függvény differenciálása
## 6.11. Határozatlan kifejezések (l'Hospital-szabály)

A tankönyv a differenciálhányadosokat a definícióból, a különbségi hányados
határértékeként számolja ki; itt a megfelelő állításokat a `Derivalt` fogalommal
mondjuk ki, és a Mathlib megfelelő deriválási tételeire vezetjük vissza.
-/

namespace Leindler.Ch06

open Set Filter Leindler Leindler.Ch05

/-! ## 6.3. Néhány elemi függvény differenciálása -/

/-- **6.3.3. Tétel.** `(xⁿ)' = n·xⁿ⁻¹` bármely `n ≥ 1` természetes számra.

*Bizonyítás (a könyv gondolatmenete).* A különbségi hányadosban
`xⁿ - x₀ⁿ = (x - x₀)(xⁿ⁻¹ + xⁿ⁻²x₀ + ⋯ + x₀ⁿ⁻¹)`, s a jobb oldali `n` tagú összeg
`x → x₀` esetén `n·x₀ⁿ⁻¹`-hez tart. -/
theorem derivalt_pow (n : ℕ) (x₀ : ℝ) :
    Derivalt (fun x => x ^ n) x₀ (n * x₀ ^ (n - 1)) :=
  (derivalt_iff_hasDerivAt _ _ _).2 (hasDerivAt_pow n x₀)

/-- **6.3.4. Tétel.** `(sin x)' = cos x`. -/
theorem derivalt_sin (x₀ : ℝ) : Derivalt Real.sin x₀ (Real.cos x₀) :=
  (derivalt_iff_hasDerivAt _ _ _).2 (Real.hasDerivAt_sin x₀)

/-- **6.3.4. Tétel.** `(cos x)' = -sin x`. -/
theorem derivalt_cos (x₀ : ℝ) : Derivalt Real.cos x₀ (-Real.sin x₀) :=
  (derivalt_iff_hasDerivAt _ _ _).2 (Real.hasDerivAt_cos x₀)

/-- **6.3.5. Tétel.** `(tg x)' = 1/cos²x`, ha `cos x ≠ 0`. -/
theorem derivalt_tan {x₀ : ℝ} (h : Real.cos x₀ ≠ 0) :
    Derivalt Real.tan x₀ (1 / Real.cos x₀ ^ 2) :=
  (derivalt_iff_hasDerivAt _ _ _).2 (Real.hasDerivAt_tan h)

/-! ## 6.5. Inverz függvény differenciálhányadosa -/

/-- **6.5.1. Tétel.** Ha a szigorúan monoton `f` függvény differenciálható az `x₀`
helyen, `f'(x₀) ≠ 0`, továbbá `g` az `f` (lokális) inverze és folytonos az
`y₀ = f(x₀)` helyen, akkor `g` differenciálható `y₀`-ban, és `g'(y₀) = 1/f'(x₀)`.

*Bizonyítás (a könyv gondolatmenete).* Az inverz függvény különbségi hányadosa a
függvény különbségi hányadosának reciproka:
`(g(y) - g(y₀))/(y - y₀) = 1/((f(x) - f(x₀))/(x - x₀))`, ahol `x = g(y)`; `y → y₀`
esetén `g` folytonossága miatt `x → x₀`, tehát a jobb oldal `1/f'(x₀)`-hoz tart. -/
theorem derivalt_inverz {f g : ℝ → ℝ} {y₀ c : ℝ} (hg : CauchyFolytonos g y₀)
    (hf : Derivalt f (g y₀) c) (hc : c ≠ 0) (hinv : ∀ᶠ y in nhds y₀, f (g y) = y) :
    Derivalt g y₀ c⁻¹ :=
  (derivalt_iff_hasDerivAt _ _ _).2
    (HasDerivAt.of_local_left_inverse ((cauchyFolytonos_iff_continuousAt g y₀).1 hg)
      ((derivalt_iff_hasDerivAt f (g y₀) c).1 hf) hc hinv)

/-! ## 6.6. A ciklometrikus függvények differenciálhányadosai -/

/-- **6.6.1. Tétel.** `(arcsin x)' = 1/√(1 - x²)`, ha `|x| < 1`. -/
theorem derivalt_arcsin {x₀ : ℝ} (h₁ : x₀ ≠ -1) (h₂ : x₀ ≠ 1) :
    Derivalt Real.arcsin x₀ (1 / Real.sqrt (1 - x₀ ^ 2)) :=
  (derivalt_iff_hasDerivAt _ _ _).2 (Real.hasDerivAt_arcsin h₁ h₂)

/-- **6.6.2. Tétel.** `(arccos x)' = -1/√(1 - x²)`, ha `|x| < 1`. -/
theorem derivalt_arccos {x₀ : ℝ} (h₁ : x₀ ≠ -1) (h₂ : x₀ ≠ 1) :
    Derivalt Real.arccos x₀ (-(1 / Real.sqrt (1 - x₀ ^ 2))) :=
  (derivalt_iff_hasDerivAt _ _ _).2 (Real.hasDerivAt_arccos h₁ h₂)

/-- **6.6.3. Tétel.** `(arctg x)' = 1/(1 + x²)`. -/
theorem derivalt_arctan (x₀ : ℝ) : Derivalt Real.arctan x₀ (1 / (1 + x₀ ^ 2)) :=
  (derivalt_iff_hasDerivAt _ _ _).2 (Real.hasDerivAt_arctan x₀)

/-! ## 6.7–6.8. Logaritmus- és exponenciális függvény -/

/-- **6.7. Tétel.** `(ln x)' = 1/x`, ha `x ≠ 0`. -/
theorem derivalt_log {x₀ : ℝ} (h : x₀ ≠ 0) : Derivalt Real.log x₀ x₀⁻¹ :=
  (derivalt_iff_hasDerivAt _ _ _).2 (Real.hasDerivAt_log h)

/-- **6.8.1. Tétel.** `(eˣ)' = eˣ` minden `x` helyen. -/
theorem derivalt_exp (x₀ : ℝ) : Derivalt Real.exp x₀ (Real.exp x₀) :=
  (derivalt_iff_hasDerivAt _ _ _).2 (Real.hasDerivAt_exp x₀)

/-- **6.8. Tétel.** `(aˣ)' = aˣ·ln a` pozitív `a` esetén. -/
theorem derivalt_rpow_const {a : ℝ} (ha : 0 < a) (x₀ : ℝ) :
    Derivalt (fun x => a ^ x) x₀ (a ^ x₀ * Real.log a) := by
  rw [derivalt_iff_hasDerivAt]
  have h : (fun x : ℝ => a ^ x) = fun x : ℝ => Real.exp (Real.log a * x) := by
    funext x
    rw [Real.rpow_def_of_pos ha]
  rw [h]
  have := (Real.hasDerivAt_exp (Real.log a * x₀)).comp x₀
    ((hasDerivAt_id x₀).const_mul (Real.log a))
  convert this using 1
  rw [Real.rpow_def_of_pos ha]
  ring

/-- **6.8.2. Tétel.** `(xᵃ)' = a·xᵃ⁻¹` pozitív `x` és tetszőleges valós `a` esetén. -/
theorem derivalt_rpow {x₀ : ℝ} (hx : 0 < x₀) (a : ℝ) :
    Derivalt (fun x => x ^ a) x₀ (a * x₀ ^ (a - 1)) :=
  (derivalt_iff_hasDerivAt _ _ _).2 (Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hx)))

/-! ## 6.9. A hiperbolikus függvények differenciálása -/

/-- **6.9.1. Tétel.** `(sh x)' = ch x`. -/
theorem derivalt_sinh (x₀ : ℝ) : Derivalt Real.sinh x₀ (Real.cosh x₀) :=
  (derivalt_iff_hasDerivAt _ _ _).2 (Real.hasDerivAt_sinh x₀)

/-- **6.9.1. Tétel.** `(ch x)' = sh x`. -/
theorem derivalt_cosh (x₀ : ℝ) : Derivalt Real.cosh x₀ (Real.sinh x₀) :=
  (derivalt_iff_hasDerivAt _ _ _).2 (Real.hasDerivAt_cosh x₀)

/-! ## 6.11. Határozatlan kifejezések: a l'Hospital-szabály -/

/-- **6.11.1. Tétel (l'Hospital-szabály, jobb oldali határérték, `0/0` eset).**
Ha `f` és `g` differenciálható `(a, b)`-n, `g'` ott nem nulla,
`lim_{x→a+} f(x) = lim_{x→a+} g(x) = 0`, és `lim_{x→a+} f'(x)/g'(x)` létezik, akkor
`lim_{x→a+} f(x)/g(x)` is létezik, és a két határérték egyenlő.

*Bizonyítás (a könyv gondolatmenete).* A Cauchy-féle középértéktétel (6.10.6) szerint
minden `x ∈ (a, b)`-hez van olyan `ξ ∈ (a, x)`, amelyre
`(f(x) - f(a))/(g(x) - g(a)) = f'(ξ)/g'(ξ)`; mivel `f(a) = g(a) = 0`, a bal oldal
`f(x)/g(x)`, és `x → a+` esetén `ξ → a+`. -/
theorem lhospital_jobb {f g f' g' : ℝ → ℝ} {a b L : ℝ} (hab : a < b)
    (hf : ∀ x ∈ Ioo a b, HasDerivAt f (f' x) x) (hg : ∀ x ∈ Ioo a b, HasDerivAt g (g' x) x)
    (hg0 : ∀ x ∈ Ioo a b, g' x ≠ 0)
    (hfa : Tendsto f (nhdsWithin a (Ioi a)) (nhds 0))
    (hga : Tendsto g (nhdsWithin a (Ioi a)) (nhds 0))
    (hlim : Tendsto (fun x => f' x / g' x) (nhdsWithin a (Ioi a)) (nhds L)) :
    Tendsto (fun x => f x / g x) (nhdsWithin a (Ioi a)) (nhds L) :=
  HasDerivAt.lhopital_zero_right_on_Ioo hab hf hg hg0 hfa hga hlim

/-- **6.11.2. Tétel (l'Hospital-szabály kétoldali határértékre, `0/0` eset).** -/
theorem lhospital_ketoldali {f g f' g' : ℝ → ℝ} {a L : ℝ}
    (hf : ∀ᶠ x in nhds a, HasDerivAt f (f' x) x)
    (hg : ∀ᶠ x in nhds a, HasDerivAt g (g' x) x)
    (hg0 : ∀ᶠ x in nhds a, g' x ≠ 0)
    (hfa : Tendsto f (nhds a) (nhds 0)) (hga : Tendsto g (nhds a) (nhds 0))
    (hlim : Tendsto (fun x => f' x / g' x) (nhds a) (nhds L)) :
    Tendsto (fun x => f x / g x) (nhdsWithin a {a}ᶜ) (nhds L) :=
  HasDerivAt.lhopital_zero_nhds hf hg hg0 hfa hga hlim

/-- A l'Hospital-szabály a könyv határérték-fogalmával kimondva (kétoldali,
`0/0` eset): ha a feltételek teljesülnek, akkor `lim_{x→a} f(x)/g(x) = L`. -/
theorem lhospital_hatarertek {f g f' g' : ℝ → ℝ} {a L : ℝ}
    (hf : ∀ᶠ x in nhds a, HasDerivAt f (f' x) x)
    (hg : ∀ᶠ x in nhds a, HasDerivAt g (g' x) x)
    (hg0 : ∀ᶠ x in nhds a, g' x ≠ 0)
    (hfa : Tendsto f (nhds a) (nhds 0)) (hga : Tendsto g (nhds a) (nhds 0))
    (hlim : Tendsto (fun x => f' x / g' x) (nhds a) (nhds L)) :
    CauchyHatarErtek (fun x => f x / g x) a L :=
  (cauchyHatarErtek_iff_tendsto _ _ _).2 (lhospital_ketoldali hf hg hg0 hfa hga hlim)

end Leindler.Ch06
