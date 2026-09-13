import Mathlib
import Analizis.Ch05d_FuggvenyHatarertek
import Analizis.Ch05h_VegtelenbenVettHatarertek
import Analizis.Ch08a_MonotonitasSzelsoertek
import Analizis.Ch08b_KonvexsegInflexio

/-!
# Leindler László: Analízis — 8.8. Függvénydiszkusszió: kidolgozott példa

Ez a modul a jegyzet **8.8. pontjában** megadott függvénydiszkussziós sémát hajtja végre
egyetlen konkrét függvényre, az

`f(x) = x³ - 3x`

harmadfokú polinomra. Minden lépés a *könyv saját tételeire* hivatkozik (8.1.2., 8.4.1.,
8.5.1., 8.6.1., 8.7.2. Tétel), és a könyv saját fogalmaival van kimondva
(`SzigNovekedo`, `SzigoruHelyiMaximum`, `KonvexGorbe`, `InflexiosPont`, …).

A séma lépései (8.8.):

**I.** értelmezési tartomány, folytonosság, értékkészlet, zérushelyek, szimmetria;
**II.** monotonitási intervallumok, szélső értékek;
**III.** konvex és konkáv szakaszok, inflexiós pont;
**IV.** a görbe menete a `±∞`-ben.
-/

namespace Leindler.Ch08

open Set Leindler Leindler.Ch05 Leindler.Ch06

/-! ## A vizsgált függvény és deriváltjai -/

/-- A vizsgált függvény: `f(x) = x³ - 3x`. -/
def fD (x : ℝ) : ℝ := x ^ 3 - 3 * x

/-- Az első derivált: `f'(x) = 3x² - 3`. -/
def fD' (x : ℝ) : ℝ := 3 * x ^ 2 - 3

/-- A második derivált: `f''(x) = 6x`. -/
def fD'' (x : ℝ) : ℝ := 6 * x

/-- `f` differenciálható mindenütt, és `f'(x) = 3x² - 3` (6.3. pont). -/
theorem fD_derivalt (x : ℝ) : Derivalt fD x (fD' x) := by
  rw [derivalt_iff_hasDerivAt]
  have h : HasDerivAt (fun y : ℝ => y ^ 3 - 3 * y)
      (((3 : ℕ) : ℝ) * x ^ (3 - 1) - 3 * 1) x :=
    (hasDerivAt_pow 3 x).sub ((hasDerivAt_id x).const_mul 3)
  have he : ((3 : ℕ) : ℝ) * x ^ (3 - 1) - 3 * 1 = fD' x := by
    simp [fD']
  rw [he] at h
  exact h

/-- `f'` differenciálható mindenütt, és `f''(x) = 6x`. -/
theorem fD'_derivalt (x : ℝ) : Derivalt fD' x (fD'' x) := by
  rw [derivalt_iff_hasDerivAt]
  have h : HasDerivAt (fun y : ℝ => 3 * y ^ 2 - 3)
      (3 * (((2 : ℕ) : ℝ) * x ^ (2 - 1))) x :=
    ((hasDerivAt_pow 2 x).const_mul 3).sub_const 3
  have he : (3 : ℝ) * (((2 : ℕ) : ℝ) * x ^ (2 - 1)) = fD'' x := by
    simp [fD'']; ring
  rw [he] at h
  exact h

/-- `f''` differenciálható, `f'''(x) = 6`. -/
theorem fD''_derivalt (x : ℝ) : Derivalt fD'' x 6 := by
  rw [derivalt_iff_hasDerivAt]
  simpa [fD''] using (hasDerivAt_id x).const_mul (6 : ℝ)

/-! ## I. Értelmezési tartomány, folytonosság, szimmetria, zérushelyek -/

/-- **I.1.** Az `f(x) = x³ - 3x` polinom az egész számegyenesen értelmezve van, és a
Mathlib értelmében folytonos. -/
theorem fD_continuous : Continuous fD := by
  unfold fD; fun_prop

/-- **I.2.** `f` a könyv Cauchy-féle definíciója szerint minden pontban folytonos
(5.2.2. Definíció), tehát nincs szakadási pontja. -/
theorem fD_folytonos (x₀ : ℝ) : CauchyFolytonos fD x₀ :=
  (cauchyFolytonos_iff_continuousAt fD x₀).2 fD_continuous.continuousAt

/-- **I.5.** `f` páratlan függvény (5.1.11. Definíció): a görbe az origóra
szimmetrikus. -/
theorem fD_paratlan : ParatlanFv fD := by
  intro x; simp [fD]; ring

/-- **I.4.** A zérushelyek: `f(x) = 0` pontosan akkor, ha `x = 0`, `x = √3` vagy
`x = -√3` (a `x(x² - 3)` szorzattá alakításból). -/
theorem fD_zerushelyek (x : ℝ) :
    fD x = 0 ↔ x = 0 ∨ x = Real.sqrt 3 ∨ x = -Real.sqrt 3 := by
  have hs : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  constructor
  · intro h
    have hfac : x * (x - Real.sqrt 3) * (x + Real.sqrt 3) = 0 := by
      have h' : x ^ 3 - 3 * x = 0 := h
      linear_combination h' - x * hs
    rcases mul_eq_zero.1 hfac with h1 | h2
    · rcases mul_eq_zero.1 h1 with h3 | h4
      · exact Or.inl h3
      · exact Or.inr (Or.inl (by linarith [sub_eq_zero.1 h4]))
    · exact Or.inr (Or.inr (by linarith))
  · rintro (rfl | rfl | rfl)
    · norm_num [fD]
    · show Real.sqrt 3 ^ 3 - 3 * Real.sqrt 3 = 0
      linear_combination Real.sqrt 3 * hs
    · show (-Real.sqrt 3) ^ 3 - 3 * -Real.sqrt 3 = 0
      linear_combination (-Real.sqrt 3) * hs

/-! ## IV. A görbe menete a végtelenben (5.19. Definíció) -/

/-- **IV.1.** `lim_{x→+∞} f(x) = +∞`: ha `x ≥ 2`, akkor `x² - 3 ≥ 1`, tehát
`f(x) = x(x² - 3) ≥ x`. -/
theorem fD_vegtelenben : VegtelenHatarErtekVegtelenben fD := by
  intro M
  refine ⟨max 2 |M|, fun x hx => ?_⟩
  have h2 : (2 : ℝ) < x := lt_of_le_of_lt (le_max_left _ _) hx
  have hM : |M| < x := lt_of_le_of_lt (le_max_right _ _) hx
  have hMle : M ≤ |M| := le_abs_self M
  have : x ≤ fD x := by
    have hpos : (0 : ℝ) < x * (x - 2) * (x + 2) := by
      apply mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)
    simp only [fD]; nlinarith [hpos]
  linarith

/-- **IV.2.** `lim_{x→-∞} f(x) = -∞`. -/
theorem fD_minusz_vegtelenben : MinuszVegtelenHatarErtekMinuszVegtelenben fD := by
  intro M
  refine ⟨-(max 2 |M|), fun x hx => ?_⟩
  have h2 : x < -2 := lt_of_lt_of_le hx (neg_le_neg (le_max_left _ _))
  have hM : x < -|M| := lt_of_lt_of_le hx (neg_le_neg (le_max_right _ _))
  have hMle : -|M| ≤ M := neg_abs_le M
  have : fD x ≤ x := by
    have hneg : x * (x - 2) * (x + 2) < 0 := by
      have h1 : (0 : ℝ) < (-x) * (2 - x) * (-(x + 2)) := by
        apply mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)
      nlinarith [h1]
    simp only [fD]; nlinarith [hneg]
  linarith

/-- Segédlemma: `f` a `+∞`-ben a Mathlib értelmében is `+∞`-hez tart. -/
theorem fD_tendsto_atTop : Filter.Tendsto fD Filter.atTop Filter.atTop := by
  refine Filter.tendsto_atTop.2 fun b => ?_
  obtain ⟨K, hK⟩ := fD_vegtelenben b
  filter_upwards [Filter.eventually_gt_atTop K] with x hx using hK x hx

/-- Segédlemma: `f` a `-∞`-ben a Mathlib értelmében is `-∞`-hez tart. -/
theorem fD_tendsto_atBot : Filter.Tendsto fD Filter.atBot Filter.atBot := by
  refine Filter.tendsto_atBot.2 fun b => ?_
  obtain ⟨D, hD⟩ := fD_minusz_vegtelenben b
  filter_upwards [Filter.eventually_lt_atBot D] with x hx using (hD x hx).le

/-- **I.3.** Az értékkészlet az egész `ℝ`: a függvény folytonos, a `-∞`-ben `-∞`-hez,
a `+∞`-ben `+∞`-hez tart, tehát a Bolzano-tétel (5.14.) szerint minden értéket
felvesz. -/
theorem fD_ertekkeszlet : Ertekkeszlet fD univ = univ := by
  have hsurj : Function.Surjective fD :=
    fD_continuous.surjective fD_tendsto_atTop fD_tendsto_atBot
  simpa [Ertekkeszlet, image_univ, Set.range_eq_univ] using hsurj

/-! ## II. Monotonitási intervallumok (8.1.2. Tétel) -/

/-- Segédlemma: a `-f` függvény deriváltja `-f'`. -/
private theorem fD_neg_derivalt (x : ℝ) : Derivalt (fun t => -fD t) x (-fD' x) := by
  rw [derivalt_iff_hasDerivAt]
  exact ((derivalt_iff_hasDerivAt fD x (fD' x)).1 (fD_derivalt x)).neg

/-- **II.1.** `f` szigorúan növekedő a `(-∞, -1]` intervallumon, mert ott `f'(x) > 0`
(8.1.2. Tétel). -/
theorem fD_szigNovekedo_bal : SzigNovekedo fD (Iic (-1)) := by
  intro x₁ h₁ x₂ h₂ hlt
  have h₂' : x₂ ≤ -1 := h₂
  refine szigoruan_novekedo_ha_derivalt_pozitiv (f := fD) (f' := fD')
    (a := x₁) (b := x₂) fD_continuous.continuousOn
    (fun x _ => fD_derivalt x) (fun x hx => ?_) x₁ (left_mem_Icc.2 hlt.le)
    x₂ (right_mem_Icc.2 hlt.le) hlt
  have hx1 : x < -1 := lt_of_lt_of_le hx.2 h₂'
  simp only [fD']; nlinarith

/-- **II.2.** `f` szigorúan csökkenő a `[-1, 1]` intervallumon, mert ott `f'(x) < 0`
(8.1.2. Tétel, a `-f` függvényre alkalmazva). -/
theorem fD_szigCsokkeno_kozep : SzigCsokkeno fD (Icc (-1) 1) := by
  intro x₁ h₁ x₂ h₂ hlt
  have hneg := szigoruan_novekedo_ha_derivalt_pozitiv
    (f := fun t => -fD t) (f' := fun t => -fD' t) (a := x₁) (b := x₂)
    (fD_continuous.neg.continuousOn) (fun x _ => fD_neg_derivalt x)
    (fun x hx => by
      have hl : -1 < x := lt_of_le_of_lt h₁.1 hx.1
      have hr : x < 1 := lt_of_lt_of_le hx.2 h₂.2
      simp only [fD']; nlinarith)
    x₁ (left_mem_Icc.2 hlt.le) x₂ (right_mem_Icc.2 hlt.le) hlt
  simp only at hneg
  linarith

/-- **II.3.** `f` szigorúan növekedő az `[1, +∞)` intervallumon (8.1.2. Tétel). -/
theorem fD_szigNovekedo_jobb : SzigNovekedo fD (Ici 1) := by
  intro x₁ h₁ x₂ h₂ hlt
  have h₁' : (1 : ℝ) ≤ x₁ := h₁
  refine szigoruan_novekedo_ha_derivalt_pozitiv (f := fD) (f' := fD')
    (a := x₁) (b := x₂) fD_continuous.continuousOn
    (fun x _ => fD_derivalt x) (fun x hx => ?_) x₁ (left_mem_Icc.2 hlt.le)
    x₂ (right_mem_Icc.2 hlt.le) hlt
  have hx1 : 1 < x := lt_of_le_of_lt h₁' hx.1
  simp only [fD']; nlinarith

/-! ## II. Szélső értékek (8.4.1., 8.5.1. Tétel) -/

/-- A helyi maximum értéke: `f(-1) = 2`. -/
theorem fD_maximum_ertek : fD (-1) = 2 := by norm_num [fD]

/-- A helyi minimum értéke: `f(1) = -2`. -/
theorem fD_minimum_ertek : fD 1 = -2 := by norm_num [fD]

/-- **II.4.** `f`-nek `x₀ = -1`-ben szigorú helyi maximuma van: a derivált `-1` előtt
pozitív, utána negatív (**8.4.1. Tétel**). -/
theorem fD_szigoru_maximum : SzigoruHelyiMaximum fD univ (-1) := by
  refine ⟨1, one_pos, fun x _ hne hx => ?_⟩
  refine szigoru_maximum_ha_derivalt_jelet_valt (f := fD) (f' := fD') (x₀ := -1) (δ := 1)
    (fun y _ => fD_derivalt y) (fun y hy hlt => ?_) (fun y hy hgt => ?_) x hx hne
  · have habs := abs_lt.1 hy
    have : y < -1 := hlt
    simp only [fD']; nlinarith
  · have habs := abs_lt.1 hy
    have h1 : -1 < y := hgt
    have h2 : y < 0 := by linarith [habs.2]
    simp only [fD']; nlinarith

/-- **II.5.** `f`-nek `x₀ = 1`-ben szigorú helyi minimuma van, mert `f'(1) = 0` és
`f''(1) = 6 > 0` (**8.5.1. Tétel**). -/
theorem fD_szigoru_minimum :
    ∃ δ > 0, ∀ x : ℝ, |x - 1| < δ → x ≠ 1 → fD 1 < fD x :=
  szigoru_minimum_masodik_derivalttal (f := fD) (f' := fD') (x₀ := 1) (M := 6) (δ := 1)
    one_pos (fun x _ => fD_derivalt x) (by norm_num [fD'])
    (by simpa [fD''] using fD'_derivalt 1) (by norm_num)

/-- A `-1` pontbeli szigorú helyi maximumból a (tágabb értelemben vett) helyi maximum is
következik. -/
theorem fD_helyi_maximum : HelyiMaximum fD univ (-1) :=
  szigoruHelyiMaximum_helyiMaximum fD_szigoru_maximum

/-! ## III. Konvexség, konkávság, inflexiós pont (8.6.1., 8.7.2. Tétel) -/

/-- **III.1.** `f` konvex minden olyan `(a, b)` intervallumon, amelyre `0 ≤ a`, hiszen ott
`f''(x) = 6x ≥ 0` (**8.6.1. Tétel**). -/
theorem fD_konvex {a b : ℝ} (ha : 0 ≤ a) : KonvexGorbe fD (Ioo a b) :=
  konvex_ha_masodik_derivalt_nemnegativ (f := fD) (f' := fD') (f'' := fD'')
    (fun x _ => fD_derivalt x) (fun x _ => fD'_derivalt x)
    (fun x hx => by simp only [fD'']; nlinarith [hx.1])

/-- **III.2.** `f` konkáv minden olyan `(a, b)` intervallumon, amelyre `b ≤ 0`, hiszen ott
`f''(x) = 6x ≤ 0` (**8.6.1. Tétel**). -/
theorem fD_konkav {a b : ℝ} (hb : b ≤ 0) : KonkavGorbe fD (Ioo a b) :=
  (konkav_iff_masodik_derivalt_nempozitiv (f := fD) (f' := fD') (f'' := fD'')
    (fun x _ => fD_derivalt x) (fun x _ => fD'_derivalt x)).2
    (fun x hx => by simp only [fD'']; nlinarith [hx.2])

/-- **III.3.** A `0` pont inflexiós pont, mert `f''(0) = 0` és `f'''(0) = 6 ≠ 0`
(**8.7.2. Tétel**). -/
theorem fD_inflexio : InflexiosPont fD 0 :=
  inflexios_pont_ha_harmadik_derivalt_nem_nulla (f := fD) (f' := fD') (f'' := fD'')
    (x₀ := 0) (δ₀ := 1) (M := 6) one_pos (fun x _ => fD_derivalt x)
    (fun x _ => fD'_derivalt x) (by norm_num [fD'']) (fD''_derivalt 0) (by norm_num)

/-! ## IV. Összefoglalás

A fenti tételek együtt a 8.8. séma teljes végrehajtását adják az `f(x) = x³ - 3x`
függvényre:

* értelmezési tartomány: az egész `ℝ`, szakadási pont nincs (`fD_folytonos`);
* értékkészlet: az egész `ℝ` (`fD_ertekkeszlet`);
* zérushelyek: `-√3`, `0`, `√3` (`fD_zerushelyek`);
* a görbe az origóra szimmetrikus (`fD_paratlan`);
* szigorúan növekedő a `(-∞, -1]` és az `[1, ∞)` intervallumon, szigorúan csökkenő a
  `[-1, 1]`-en (`fD_szigNovekedo_bal`, `fD_szigCsokkeno_kozep`, `fD_szigNovekedo_jobb`);
* szigorú helyi maximum: `f(-1) = 2`, szigorú helyi minimum: `f(1) = -2`
  (`fD_szigoru_maximum`, `fD_szigoru_minimum`);
* konkáv a negatív, konvex a pozitív féltengelyen, `0`-ban inflexiós pont
  (`fD_konkav`, `fD_konvex`, `fD_inflexio`);
* `lim_{x→-∞} f = -∞`, `lim_{x→+∞} f = +∞` (`fD_minusz_vegtelenben`, `fD_vegtelenben`).
-/

end Leindler.Ch08
