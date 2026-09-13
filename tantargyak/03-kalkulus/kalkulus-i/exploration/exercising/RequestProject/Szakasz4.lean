/-
# 4. feladatsor — Differenciálszámítás és alkalmazásai

A `kalkulus_gyakorlo.pdf` 4. feladatsorának formalizálása.
-/
import Mathlib

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace Kalkulus1.Szakasz4

open Filter Topology Set Real

/-! ## 4.1. gyakorlat — derivált a definíció alapján -/

/-- 4.1 a) `f(x) = (x-1)² + 1`, `f'(x) = 2(x-1)`; a definíció (differenciahányados) alapján. -/
theorem gyak_4_1_a_def (x : ℝ) :
    Tendsto (fun h : ℝ => (((x + h - 1) ^ 2 + 1) - ((x - 1) ^ 2 + 1)) / h) (nhdsWithin 0 {0}ᶜ)
      (𝓝 (2 * (x - 1))) := by
  have hd : HasDerivAt (fun x : ℝ => (x - 1) ^ 2 + 1) (2 * (x - 1)) x := by
    have h := (((hasDerivAt_id x).sub_const 1).pow 2).add_const 1
    simp only [id] at h
    convert h using 1
    push_cast
    ring
  refine (hasDerivAt_iff_tendsto_slope_zero.mp hd).congr ?_
  intro t
  simp [smul_eq_mul, div_eq_inv_mul]

/-- 4.1 a) ugyanez `HasDerivAt` alakban. -/
theorem gyak_4_1_a (x : ℝ) : HasDerivAt (fun x : ℝ => (x - 1) ^ 2 + 1) (2 * (x - 1)) x := by
  have h := (((hasDerivAt_id x).sub_const 1).pow 2).add_const 1
  simp only [id] at h
  convert h using 1
  push_cast
  ring

/-- 4.1 b) `f(x) = 1/(x-1)²`, `f'(x) = -2/(x-1)³`. -/
theorem gyak_4_1_b (x : ℝ) (hx : x ≠ 1) :
    HasDerivAt (fun x : ℝ => 1 / (x - 1) ^ 2) (-2 / (x - 1) ^ 3) x := by
  have h1 : HasDerivAt (fun x : ℝ => (x - 1) ^ 2) (2 * (x - 1)) x := by
    have h := ((hasDerivAt_id x).sub_const 1).pow 2
    simp only [id] at h
    convert h using 1
    push_cast
    ring
  have hne : (x - 1) ^ 2 ≠ 0 := pow_ne_zero 2 (sub_ne_zero.mpr hx)
  have h2 := h1.inv hne
  have h3 : (fun x : ℝ => 1 / (x - 1) ^ 2) = fun x : ℝ => ((x - 1) ^ 2)⁻¹ := by
    funext y
    rw [one_div]
  rw [h3]
  convert h2 using 1
  field_simp

/-! ## 4.2. gyakorlat — deriválási szabályok -/

/-- 4.2 `(-3x⁸ + 2)' = -24x⁷`. -/
theorem gyak_4_2_polinom (x : ℝ) :
    HasDerivAt (fun x : ℝ => -3 * x ^ 8 + 2) (-24 * x ^ 7) x := by
  have h := ((hasDerivAt_pow 8 x).const_mul (-3 : ℝ)).add_const 2
  convert h using 1
  push_cast
  ring

/-- 4.2 Láncszabály `cos(x³)`-re: `(cos(x³))' = -3x² sin(x³)`. -/
theorem gyak_4_2_lanc (x : ℝ) :
    HasDerivAt (fun x : ℝ => Real.cos (x ^ 3)) (-(3 * x ^ 2) * Real.sin (x ^ 3)) x := by
  have h := (Real.hasDerivAt_cos (x ^ 3)).comp x (hasDerivAt_pow 3 x)
  convert h using 1
  push_cast
  ring

/-- 4.2 `(x⁵·5ˣ)' = 5x⁴·5ˣ + x⁵·5ˣ·ln 5`. -/
theorem gyak_4_2_szorzat (x : ℝ) :
    HasDerivAt (fun x : ℝ => x ^ 5 * Real.exp (x * Real.log 5))
      (5 * x ^ 4 * Real.exp (x * Real.log 5) +
        x ^ 5 * (Real.exp (x * Real.log 5) * Real.log 5)) x := by
  have h1 : HasDerivAt (fun x : ℝ => x * Real.log 5) (Real.log 5) x := by
    simpa using (hasDerivAt_id x).mul_const (Real.log 5)
  have h2 : HasDerivAt (fun x : ℝ => Real.exp (x * Real.log 5))
      (Real.exp (x * Real.log 5) * Real.log 5) x := by
    simpa using (Real.hasDerivAt_exp (x * Real.log 5)).comp x h1
  have h3 := (hasDerivAt_pow 5 x).mul h2
  convert h3 using 1

/-- 4.3 Logaritmikus deriválás: `(x^x)' = x^x (ln x + 1)` az `x > 0` helyeken. -/
theorem gyak_4_3_xx (x : ℝ) (hx : 0 < x) :
    HasDerivAt (fun x : ℝ => Real.exp (x * Real.log x))
      (Real.exp (x * Real.log x) * (Real.log x + 1)) x := by
  have h1 : HasDerivAt (fun x : ℝ => x * Real.log x) (Real.log x + 1) x := by
    have h := (hasDerivAt_id x).mul (Real.hasDerivAt_log (ne_of_gt hx))
    simp only [id] at h
    convert h using 1
    field_simp
  simpa using (Real.hasDerivAt_exp (x * Real.log x)).comp x h1

/-! ## 4.4-4.5. gyakorlat — differenciálhatóság -/

/-- 4.5 c) `|x - 2|` nem differenciálható a `2` pontban. -/
theorem gyak_4_5_c : ¬ DifferentiableAt ℝ (fun x : ℝ => |x - 2|) 2 := by
  intro h
  have h' : DifferentiableAt ℝ (fun x : ℝ => |x - 2|) ((0 : ℝ) + 2) := by
    norm_num
    exact h
  have hf : DifferentiableAt ℝ (fun y : ℝ => y + 2) 0 := by fun_prop
  have hc : DifferentiableAt ℝ ((fun x : ℝ => |x - 2|) ∘ fun y : ℝ => y + 2) 0 := h'.comp 0 hf
  have heq : ((fun x : ℝ => |x - 2|) ∘ fun y : ℝ => y + 2) = fun y : ℝ => |y| := by
    funext y
    simp
  rw [heq] at hc
  exact not_differentiableAt_abs_zero hc

/-- 4.5 e) `j(x) = x² sin(1/x)` (`x ≠ 0`), `j(0) = 0` differenciálható `0`-ban, `j'(0) = 0`.
A differenciahányados `x·sin(1/x)`, amit a rendőrelv nyom `0`-ba. -/
theorem gyak_4_5_e :
    HasDerivAt (fun x : ℝ => if x = 0 then 0 else x ^ 2 * Real.sin (1 / x)) 0 0 := by
  rw [hasDerivAt_iff_tendsto_slope]
  have hbound : Tendsto (fun x : ℝ => |x|) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (𝓝 0) := by
    have h : Tendsto (fun x : ℝ => |x|) (𝓝 0) (𝓝 |(0 : ℝ)|) := continuous_abs.tendsto 0
    simpa using h.mono_left nhdsWithin_le_nhds
  refine squeeze_zero_norm' ?_ hbound
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : x ≠ 0 := hx
  have hsl : slope (fun x : ℝ => if x = 0 then 0 else x ^ 2 * Real.sin (1 / x)) 0 x
      = x * Real.sin (1 / x) := by
    rw [slope_def_field]
    simp [hx0]
    field_simp
  rw [hsl, Real.norm_eq_abs, abs_mul]
  have h1 := Real.abs_sin_le_one (1 / x)
  nlinarith [abs_nonneg x, abs_nonneg (Real.sin (1 / x))]

/-- 4.5 a) `x^(1/3)` nem differenciálható `0`-ban (a differenciahányados `+∞`-hez tart). -/
theorem gyak_4_5_a :
    Tendsto (fun h : ℝ => (h ^ ((1 : ℝ) / 3)) / h) (nhdsWithin 0 (Set.Ioi 0)) atTop := by
  have h := tendsto_rpow_neg_nhdsGT_zero (y := -(2 / 3 : ℝ)) (by norm_num)
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : (0 : ℝ) < x := hx
  rw [show -(2 / 3 : ℝ) = 1 / 3 - 1 by norm_num, Real.rpow_sub hx0, Real.rpow_one]

/-! ## 4.7. gyakorlat — paraméterek illesztése -/

/-- 4.7 a) Az `f(x) = ax` (`x<2`), `ax² - bx + 3` (`x≥2`) függvény pontosan akkor
differenciálható a `2` helyen, ha a folytonossági (`2a = 4a - 2b + 3`) és a
deriválási (`a = 4a - b`) feltétel is teljesül; ez pontosan `a = 3/4`, `b = 9/4`. -/
theorem gyak_4_7_a (a b : ℝ) :
    (2 * a = 4 * a - 2 * b + 3 ∧ a = 4 * a - b) ↔ (a = 3 / 4 ∧ b = 3 * a) := by
  constructor
  · rintro ⟨h1, h2⟩
    constructor <;> linarith
  · rintro ⟨h1, h2⟩
    constructor <;> linarith

/-! ## 4.8-4.9. gyakorlat — menetvizsgálat, szélsőértékek -/

/-- 4.8/18. `f(x) = x·eˣ` minimuma `x = -1`-ben van: `x eˣ ≥ -e⁻¹` minden `x`-re. -/
theorem gyak_4_8_18_min (x : ℝ) : (-1 : ℝ) * Real.exp (-1) ≤ x * Real.exp x := by
  have h := Real.add_one_le_exp (-(x + 1))
  have hexp : (0 : ℝ) < Real.exp x := Real.exp_pos x
  have key : -x ≤ Real.exp (-(x + 1)) := by linarith
  have h2 : Real.exp (-(x + 1)) * Real.exp x = Real.exp (-1) := by
    rw [← Real.exp_add]
    ring_nf
  nlinarith [mul_le_mul_of_nonneg_right key hexp.le]

/-- 4.8/18. `f(x) = x·eˣ` konvex a `[-2,∞)` intervallumon (`f''(x) = (x+2)eˣ ≥ 0`). -/
theorem gyak_4_8_18_konvex (x : ℝ) (hx : -2 ≤ x) : 0 ≤ (x + 2) * Real.exp x := by
  have : 0 < Real.exp x := Real.exp_pos x
  nlinarith

/-- 4.9 a) `f(x) = x²` abszolút maximuma `[-2,1]`-en `4`, minimuma `0`. -/
theorem gyak_4_9_a :
    IsGreatest ((fun x : ℝ => x ^ 2) '' Set.Icc (-2 : ℝ) 1) 4 ∧
    IsLeast ((fun x : ℝ => x ^ 2) '' Set.Icc (-2 : ℝ) 1) 0 := by
  constructor
  · constructor
    · exact ⟨-2, by norm_num⟩
    · rintro y ⟨x, ⟨hx1, hx2⟩, rfl⟩
      nlinarith
  · constructor
    · exact ⟨0, by norm_num⟩
    · rintro y ⟨x, _, rfl⟩
      positivity

/-- 4.9 f) `f(x) = 2 - |x|` abszolút maximuma `[-1,3]`-on `2`, minimuma `-1`. -/
theorem gyak_4_9_f :
    IsGreatest ((fun x : ℝ => 2 - |x|) '' Set.Icc (-1 : ℝ) 3) 2 ∧
    IsLeast ((fun x : ℝ => 2 - |x|) '' Set.Icc (-1 : ℝ) 3) (-1) := by
  constructor
  · refine ⟨⟨0, by norm_num⟩, ?_⟩
    rintro y ⟨x, _, rfl⟩
    have : 0 ≤ |x| := abs_nonneg x
    simp only
    linarith
  · refine ⟨⟨3, by norm_num⟩, ?_⟩
    rintro y ⟨x, ⟨hx1, hx2⟩, rfl⟩
    have : |x| ≤ 3 := abs_le.mpr ⟨by linarith, by linarith⟩
    simp only
    linarith

/-! ## 4.10. gyakorlat — L'Hospital-szabály -/

/-- 4.10 e) `lim_{x→0} (eˣ - (1+x))/x² = 1/2` (L'Hospital-szabály). -/
theorem gyak_4_10_e :
    Tendsto (fun x : ℝ => (Real.exp x - (1 + x)) / x ^ 2) (nhdsWithin 0 {0}ᶜ) (𝓝 (1 / 2)) := by
  have hf : ∀ᶠ x : ℝ in nhdsWithin 0 {(0 : ℝ)}ᶜ,
      HasDerivAt (fun x : ℝ => Real.exp x - (1 + x)) (Real.exp x - 1) x := by
    filter_upwards with x
    have h1 : HasDerivAt (fun x : ℝ => Real.exp x) (Real.exp x) x := Real.hasDerivAt_exp x
    have h2 : HasDerivAt (fun x : ℝ => 1 + x) 1 x := by simpa using (hasDerivAt_id x).const_add 1
    simpa using h1.sub h2
  have hg : ∀ᶠ x : ℝ in nhdsWithin 0 {(0 : ℝ)}ᶜ, HasDerivAt (fun x : ℝ => x ^ 2) (2 * x) x := by
    filter_upwards with x
    simpa using hasDerivAt_pow 2 x
  have hg' : ∀ᶠ x : ℝ in nhdsWithin 0 {(0 : ℝ)}ᶜ, 2 * x ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : x ≠ 0 := hx
    simpa using hx0
  have hfa : Tendsto (fun x : ℝ => Real.exp x - (1 + x)) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (𝓝 0) := by
    have h : Tendsto (fun x : ℝ => Real.exp x - (1 + x)) (𝓝 0) (𝓝 (Real.exp 0 - (1 + 0))) :=
      (Real.continuous_exp.sub (continuous_const.add continuous_id)).tendsto 0
    norm_num at h
    exact h.mono_left nhdsWithin_le_nhds
  have hga : Tendsto (fun x : ℝ => x ^ 2) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (𝓝 0) := by
    have h : Tendsto (fun x : ℝ => x ^ 2) (𝓝 0) (𝓝 ((0 : ℝ) ^ 2)) := (continuous_pow 2).tendsto 0
    norm_num at h
    exact h.mono_left nhdsWithin_le_nhds
  have hdiv : Tendsto (fun x : ℝ => (Real.exp x - 1) / (2 * x)) (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (𝓝 (1 / 2)) := by
    have hslope : Tendsto (fun x : ℝ => (Real.exp x - 1) / x) (nhdsWithin 0 {(0 : ℝ)}ᶜ) (𝓝 1) := by
      have hd : HasDerivAt (fun x : ℝ => Real.exp x) 1 0 := by simpa using Real.hasDerivAt_exp 0
      refine (hasDerivAt_iff_tendsto_slope.mp hd).congr ?_
      intro t
      simp [slope_def_field, div_eq_inv_mul]
    have hc := hslope.const_mul (1 / 2 : ℝ)
    rw [show (1 / 2 : ℝ) * 1 = 1 / 2 by norm_num] at hc
    refine hc.congr ?_
    intro x
    rcases eq_or_ne x 0 with rfl | hx
    · simp
    · field_simp
  exact HasDerivAt.lhopital_zero_nhdsNE hf hg hg' hfa hga hdiv

/-- 4.10 f) `lim_{x→0} (eˣ - e⁻ˣ)/x = 2`. Ez a differenciahányados-trükk:
a keresett határérték az `x ↦ eˣ - e⁻ˣ` függvény deriváltja a `0`-ban. -/
theorem gyak_4_10_f :
    Tendsto (fun x : ℝ => (Real.exp x - Real.exp (-x)) / x) (nhdsWithin 0 {0}ᶜ) (𝓝 2) := by
  have hd : HasDerivAt (fun x : ℝ => Real.exp x - Real.exp (-x)) 2 0 := by
    have h1 : HasDerivAt (fun x : ℝ => Real.exp (-x)) (-1) 0 := by
      simpa using (Real.hasDerivAt_exp (-(0 : ℝ))).comp 0 (hasDerivAt_id (0 : ℝ)).neg
    have h2 : HasDerivAt (fun x : ℝ => Real.exp x) 1 0 := by simpa using Real.hasDerivAt_exp 0
    have h3 := h2.sub h1
    norm_num at h3
    exact h3
  refine (hasDerivAt_iff_tendsto_slope.mp hd).congr ?_
  intro t
  simp [slope_def_field, div_eq_inv_mul]

/-- 4.10 p) `lim_{x→∞} (ln x)/x = 0`. -/
theorem gyak_4_10_p : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) := by
  have h := Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 (by norm_num)
  simpa using h

/-- 4.10 q) `lim_{x→0⁺} x² ln x = 0`. -/
theorem gyak_4_10_q :
    Tendsto (fun x : ℝ => x ^ 2 * Real.log x) (nhdsWithin 0 (Set.Ioi 0)) (𝓝 0) := by
  have h := tendsto_log_mul_rpow_nhdsGT_zero (r := 2) (by norm_num)
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : (0 : ℝ) < x := hx
  rw [show ((2 : ℝ)) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
  ring

/-- 4.10 t) `lim_{x→∞} x² e⁻ˣ = 0`. -/
theorem gyak_4_10_t : Tendsto (fun x : ℝ => x ^ 2 * Real.exp (-x)) atTop (𝓝 0) :=
  Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero 2

/-! ## 4.11-4.13. gyakorlat — szélsőérték-feladatok -/

/-- 4.11 a) A `20`-at két tagra bontva a szorzat maximuma `100`, `10 + 10` esetén. -/
theorem gyak_4_11_a (x : ℝ) : x * (20 - x) ≤ 100 := by nlinarith [sq_nonneg (x - 10)]

/-- 4.11 b) A négyzetösszeg a végpontokon maximális: `[0,20]`-on `x² + (20-x)² ≤ 400`. -/
theorem gyak_4_11_b (x : ℝ) (hx : x ∈ Set.Icc (0 : ℝ) 20) :
    x ^ 2 + (20 - x) ^ 2 ≤ 400 := by
  obtain ⟨h0, h20⟩ := hx
  nlinarith

/-- Segédállítás a 4.13-hoz: ha `F` folytonos a `[0,1]` kompakt intervallumon,
teljesíti a középpontos egyenlőtlenséget, és a végpontokban nempozitív, akkor
mindenhol nempozitív.  A bizonyítás a maximumhely legnagyobb pontját tolja tovább. -/
theorem kozeppontos_nonpos_of_endpoints (F : ℝ → ℝ) (hc : ContinuousOn F (Icc 0 1))
    (hmid : ∀ s ∈ Icc (0:ℝ) 1, ∀ t ∈ Icc (0:ℝ) 1, F ((s + t) / 2) ≤ (F s + F t) / 2)
    (h0 : F 0 ≤ 0) (h1 : F 1 ≤ 0) : ∀ t ∈ Icc (0:ℝ) 1, F t ≤ 0 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨t₀, ht₀, ht₀pos⟩ := hcon
  obtain ⟨c₀, hc₀, hmax⟩ := (isCompact_Icc (a := (0:ℝ)) (b := 1)).exists_isMaxOn
    (nonempty_Icc.2 zero_le_one) hc
  set M := F c₀ with hM
  have hMpos : 0 < M := lt_of_lt_of_le ht₀pos (hmax ht₀)
  set S : Set ℝ := {t | t ∈ Icc (0:ℝ) 1 ∧ F t = M} with hS
  have hSsub : S ⊆ Icc (0:ℝ) 1 := fun t ht => ht.1
  have hSclosed : IsClosed S := by
    have hSeq : S = (Icc (0:ℝ) 1) ∩ F ⁻¹' {M} := by
      ext t; simp [hS, and_comm]
    rw [hSeq]
    exact hc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_singleton
  have hSne : S.Nonempty := ⟨c₀, hc₀, rfl⟩
  have hSbdd : BddAbove S := ⟨1, fun t ht => (hSsub ht).2⟩
  have hmem : sSup S ∈ S := hSclosed.csSup_mem hSne hSbdd
  set c := sSup S with hcdef
  obtain ⟨hcI, hcF⟩ := hmem
  have hc0 : 0 < c := by
    rcases lt_or_eq_of_le hcI.1 with h | h
    · exact h
    · exfalso; rw [← h] at hcF; linarith
  have hc1 : c < 1 := by
    rcases lt_or_eq_of_le hcI.2 with h | h
    · exact h
    · exfalso; rw [h] at hcF; linarith
  set h := min c (1 - c) / 2 with hh
  have hhpos : 0 < h := by
    have : 0 < min c (1 - c) := lt_min hc0 (by linarith)
    simpa [hh] using half_pos this
  have hhc : h ≤ c / 2 := by
    have : min c (1 - c) ≤ c := min_le_left _ _
    simp only [hh]; linarith
  have hh1 : h ≤ (1 - c) / 2 := by
    have : min c (1 - c) ≤ 1 - c := min_le_right _ _
    simp only [hh]; linarith
  have hm1 : c - h ∈ Icc (0:ℝ) 1 := ⟨by linarith, by linarith⟩
  have hp1 : c + h ∈ Icc (0:ℝ) 1 := ⟨by linarith, by linarith⟩
  have key := hmid _ hm1 _ hp1
  have harg : (c - h + (c + h)) / 2 = c := by ring
  rw [harg, hcF] at key
  have hle : F (c + h) ≤ M := hmax hp1
  have hle' : F (c - h) ≤ M := hmax hm1
  have heq : F (c + h) = M := by linarith
  have : c + h ≤ c := le_csSup hSbdd ⟨hp1, heq⟩
  linarith

/-- 4.13 (*) Középpontosan konvex + folytonos ⟹ konvex. -/
theorem gyak_4_13 {a b : ℝ} (f : ℝ → ℝ) (hcont : ContinuousOn f (Set.Ioo a b))
    (hmid : ∀ x ∈ Set.Ioo a b, ∀ y ∈ Set.Ioo a b, f ((x + y) / 2) ≤ (f x + f y) / 2) :
    ConvexOn ℝ (Set.Ioo a b) f := by
  refine ⟨convex_Ioo a b, ?_⟩
  intro x hx y hy p q hp hq hpq
  set P : ℝ → ℝ := fun t => (1 - t) * x + t * y with hP
  have hPmem : ∀ t ∈ Icc (0:ℝ) 1, P t ∈ Ioo a b := by
    intro t ht
    have := (convex_Ioo a b) hx hy (by linarith [ht.2] : (0:ℝ) ≤ 1 - t) ht.1 (by ring)
    simpa [hP, smul_eq_mul, mul_comm] using this
  set F : ℝ → ℝ := fun t => f (P t) - ((1 - t) * f x + t * f y) with hF
  have hPc : Continuous P := by fun_prop
  have hFc : ContinuousOn F (Icc 0 1) := by
    apply ContinuousOn.sub
    · exact hcont.comp hPc.continuousOn hPmem
    · fun_prop
  have hFmid : ∀ s ∈ Icc (0:ℝ) 1, ∀ t ∈ Icc (0:ℝ) 1, F ((s + t) / 2) ≤ (F s + F t) / 2 := by
    intro s hs t ht
    have h1 := hmid _ (hPmem s hs) _ (hPmem t ht)
    have harg : (P s + P t) / 2 = P ((s + t) / 2) := by simp [hP]; ring
    rw [harg] at h1
    simp only [hF]
    have haff : (1 - (s + t) / 2) * f x + (s + t) / 2 * f y
        = (((1 - s) * f x + s * f y) + ((1 - t) * f x + t * f y)) / 2 := by ring
    rw [haff]
    linarith
  have h0 : F 0 ≤ 0 := by simp [hF, hP]
  have h1 : F 1 ≤ 0 := by simp [hF, hP]
  have hmain := kozeppontos_nonpos_of_endpoints F hFc hFmid h0 h1 q ⟨hq, by linarith⟩
  simp only [hF, hP] at hmain
  have hpq' : p = 1 - q := by linarith
  simp only [smul_eq_mul, hpq']
  linarith

end Kalkulus1.Szakasz4
