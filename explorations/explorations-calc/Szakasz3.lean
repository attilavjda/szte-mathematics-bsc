/-
# 3. feladatsor — Határérték, folytonosság

A `kalkulus_gyakorlo.pdf` 3. feladatsorának formalizálása.
A határértékeket a Mathlib `Filter.Tendsto` fogalmával fejezzük ki:
`Tendsto f (punktalt a) (𝓝 L)` a klasszikus `lim_{x→a} f(x) = L`.
-/
import Mathlib

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace Kalkulus1.Szakasz3

open Filter Topology Set

/-- A „pontbeli (lyukas) határérték” szűrője: `x → a`, `x ≠ a`. -/
abbrev punktalt (a : ℝ) : Filter ℝ := nhdsWithin a {a}ᶜ

/-! ## Segédeszközök

Ezek a lemmák a „gépezet”, amelyre a feladatsor nagy része visszavezethető. -/

/-- `c/xᵏ → 0` a végtelenben (`k ≥ 1`). Ez a „legmagasabb fokú taggal osztunk” technika magja. -/
theorem tendsto_const_div_pow_atTop (c : ℝ) {k : ℕ} (hk : k ≠ 0) :
    Tendsto (fun x : ℝ => c / x ^ k) atTop (𝓝 0) :=
  tendsto_const_nhds.div_atTop (tendsto_pow_atTop hk)

/-- Helyettesítés lyukas környezetben: `x ↦ c·x` a `punktalt a` szűrőt a `punktalt (c·a)`
szűrőbe viszi, ha `c ≠ 0`. Ez teszi lehetővé a `lim_{x→0} sin(3x)/x` típusú átírásokat. -/
theorem tendsto_punktalt_const_mul {c : ℝ} (hc : c ≠ 0) (a : ℝ) :
    Tendsto (fun x : ℝ => c * x) (punktalt a) (punktalt (c * a)) := by
  rw [tendsto_nhdsWithin_iff]
  constructor
  · exact ((continuous_const.mul continuous_id).tendsto a).mono_left nhdsWithin_le_nhds
  · filter_upwards [self_mem_nhdsWithin] with x hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    intro h
    exact hx (mul_left_cancel₀ hc h)

/-! ## 3.1. gyakorlat — határérték a definíció szerint -/

/-- 3.1 a) `lim_{x→1} 1/(x³+2) = 1/3`, epszilon-delta alakban.
(A `Metric.tendsto_nhdsWithin_nhds` átírás pontosan a tankönyvi definíció.) -/
theorem gyak_3_1_a_epsdelta :
    ∀ eps > (0 : ℝ), ∃ delta > (0 : ℝ), ∀ x : ℝ,
      x ≠ 1 → |x - 1| < delta → |1 / (x ^ 3 + 2) - 1 / 3| < eps := by
  have h : Tendsto (fun x : ℝ => 1 / (x ^ 3 + 2)) (punktalt 1) (𝓝 (1 / 3)) := by
    have hc : Tendsto (fun x : ℝ => 1 / (x ^ 3 + 2)) (𝓝 1) (𝓝 (1 / ((1 : ℝ) ^ 3 + 2))) :=
      ContinuousAt.div continuousAt_const (by fun_prop) (by norm_num)
    have h3 : (1 : ℝ) / ((1 : ℝ) ^ 3 + 2) = 1 / 3 := by norm_num
    rw [h3] at hc
    exact hc.mono_left nhdsWithin_le_nhds
  rw [Metric.tendsto_nhdsWithin_nhds] at h
  intro eps heps
  obtain ⟨delta, hdelta, hd⟩ := h eps heps
  refine ⟨delta, hdelta, fun x hx hxd => ?_⟩
  have := hd (x := x) hx (by simpa [Real.dist_eq] using hxd)
  simpa [Real.dist_eq] using this

/-- 3.1 a) ugyanez szűrőkkel. -/
theorem gyak_3_1_a : Tendsto (fun x : ℝ => 1 / (x ^ 3 + 2)) (punktalt 1) (𝓝 (1 / 3)) := by
  have hc : Tendsto (fun x : ℝ => 1 / (x ^ 3 + 2)) (𝓝 1) (𝓝 (1 / ((1 : ℝ) ^ 3 + 2))) :=
    ContinuousAt.div continuousAt_const (by fun_prop) (by norm_num)
  have h3 : (1 : ℝ) / ((1 : ℝ) ^ 3 + 2) = 1 / 3 := by norm_num
  rw [h3] at hc
  exact hc.mono_left nhdsWithin_le_nhds

/-- 3.1 b) `lim_{x→π/2} sin x = 1`. -/
theorem gyak_3_1_b : Tendsto (fun x : ℝ => Real.sin x) (punktalt (Real.pi / 2)) (𝓝 1) := by
  have h : Tendsto Real.sin (𝓝 (Real.pi / 2)) (𝓝 (Real.sin (Real.pi / 2))) :=
    Real.continuous_sin.continuousAt
  rw [Real.sin_pi_div_two] at h
  exact h.mono_left nhdsWithin_le_nhds

/-! ## 3.2-3.3. gyakorlat — határérték a végtelenben -/

/-- 3.2 a) `lim_{x→∞} (2x³+7)/(x³-x²+x+7) = 2`. -/
theorem gyak_3_2_a :
    Tendsto (fun x : ℝ => (2 * x ^ 3 + 7) / (x ^ 3 - x ^ 2 + x + 7)) atTop (𝓝 2) := by
  have hnum : Tendsto (fun x : ℝ => 2 + 7 / x ^ 3) atTop (𝓝 2) := by
    simpa using tendsto_const_nhds.add (tendsto_const_div_pow_atTop 7 (k := 3) (by norm_num))
  have hden : Tendsto (fun x : ℝ => 1 - 1 / x + 1 / x ^ 2 + 7 / x ^ 3) atTop (𝓝 1) := by
    have h1 := tendsto_const_div_pow_atTop 1 (k := 1) (by norm_num)
    have h2 := tendsto_const_div_pow_atTop 1 (k := 2) (by norm_num)
    have h3 := tendsto_const_div_pow_atTop 7 (k := 3) (by norm_num)
    simp only [pow_one] at h1
    simpa using ((tendsto_const_nhds.sub h1).add h2).add h3
  have hq : Tendsto (fun x : ℝ => (2 + 7 / x ^ 3) / (1 - 1 / x + 1 / x ^ 2 + 7 / x ^ 3))
      atTop (𝓝 (2 / 1)) := hnum.div hden (by norm_num)
  rw [show (2 : ℝ) / 1 = 2 by norm_num] at hq
  refine hq.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hx3 : x ^ 3 ≠ 0 := by positivity
  have e1 : 2 + 7 / x ^ 3 = (2 * x ^ 3 + 7) / x ^ 3 := by field_simp
  have e2 : 1 - 1 / x + 1 / x ^ 2 + 7 / x ^ 3 = (x ^ 3 - x ^ 2 + x + 7) / x ^ 3 := by field_simp
  rw [e1, e2, div_div_div_cancel_right₀ hx3]

/-- 3.2 b) `lim_{x→∞} (3x+7)/(x²-2) = 0`. -/
theorem gyak_3_2_b : Tendsto (fun x : ℝ => (3 * x + 7) / (x ^ 2 - 2)) atTop (𝓝 0) := by
  have hnum : Tendsto (fun x : ℝ => 3 / x + 7 / x ^ 2) atTop (𝓝 0) := by
    have h1 := tendsto_const_div_pow_atTop 3 (k := 1) (by norm_num)
    have h2 := tendsto_const_div_pow_atTop 7 (k := 2) (by norm_num)
    simp only [pow_one] at h1
    simpa using h1.add h2
  have hden : Tendsto (fun x : ℝ => 1 - 2 / x ^ 2) atTop (𝓝 1) := by
    have h2 := tendsto_const_div_pow_atTop 2 (k := 2) (by norm_num)
    simpa using tendsto_const_nhds.sub h2
  have hq : Tendsto (fun x : ℝ => (3 / x + 7 / x ^ 2) / (1 - 2 / x ^ 2)) atTop (𝓝 (0 / 1)) :=
    hnum.div hden (by norm_num)
  rw [show (0 : ℝ) / 1 = 0 by norm_num] at hq
  refine hq.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  have hx2 : x ^ 2 ≠ 0 := by positivity
  have e1 : 3 / x + 7 / x ^ 2 = (3 * x + 7) / x ^ 2 := by field_simp
  have e2 : 1 - 2 / x ^ 2 = (x ^ 2 - 2) / x ^ 2 := by field_simp
  rw [e1, e2, div_div_div_cancel_right₀ hx2]

/-- 3.3 g) `lim_{x→∞} (√(x²+x) - √(x²-x)) = 1` (gyöktelenítés). -/
theorem gyak_3_3_g :
    Tendsto (fun x : ℝ => Real.sqrt (x ^ 2 + x) - Real.sqrt (x ^ 2 - x)) atTop (𝓝 1) := by
  have hinv : Tendsto (fun x : ℝ => 1 / x) atTop (𝓝 0) := by
    simpa using tendsto_const_div_pow_atTop 1 (k := 1) (by norm_num)
  have hs : Tendsto (fun x : ℝ => Real.sqrt (1 + 1 / x)) atTop (𝓝 1) := by
    have h0 : Tendsto (fun x : ℝ => 1 + 1 / x) atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.add hinv
    have := (Real.continuous_sqrt.tendsto (1 : ℝ)).comp h0
    simpa using this
  have ht : Tendsto (fun x : ℝ => Real.sqrt (1 - 1 / x)) atTop (𝓝 1) := by
    have h0 : Tendsto (fun x : ℝ => 1 - 1 / x) atTop (𝓝 1) := by
      simpa using tendsto_const_nhds.sub hinv
    have := (Real.continuous_sqrt.tendsto (1 : ℝ)).comp h0
    simpa using this
  have hsum2 : Tendsto (fun x : ℝ => Real.sqrt (1 + 1 / x) + Real.sqrt (1 - 1 / x))
      atTop (𝓝 (1 + 1)) := hs.add ht
  have hq : Tendsto
      (fun x : ℝ => 2 / (Real.sqrt (1 + 1 / x) + Real.sqrt (1 - 1 / x))) atTop (𝓝 (2 / (1 + 1))) :=
    tendsto_const_nhds.div hsum2 (by norm_num)
  rw [show (2 : ℝ) / (1 + 1) = 1 by norm_num] at hq
  refine hq.congr' ?_
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx
  have hA : 0 ≤ 1 + 1 / x := by positivity
  have hB : 0 ≤ 1 - 1 / x := by
    have : 1 / x ≤ 1 := by rw [div_le_one hx0]; exact hx
    linarith
  set s := Real.sqrt (1 + 1 / x) with hs_def
  set t := Real.sqrt (1 - 1 / x) with ht_def
  have hsq1 : Real.sqrt (x ^ 2 + x) = x * s := by
    rw [hs_def, show x ^ 2 + x = x ^ 2 * (1 + 1 / x) by field_simp,
      Real.sqrt_mul (by positivity), Real.sqrt_sq hx0.le]
  have hsq2 : Real.sqrt (x ^ 2 - x) = x * t := by
    rw [ht_def, show x ^ 2 - x = x ^ 2 * (1 - 1 / x) by field_simp,
      Real.sqrt_mul (by positivity), Real.sqrt_sq hx0.le]
  have hspos : 0 < s := Real.sqrt_pos.mpr (by positivity)
  have hsum : 0 < s + t := add_pos_of_pos_of_nonneg hspos (Real.sqrt_nonneg _)
  have h1 : s ^ 2 = 1 + 1 / x := Real.sq_sqrt hA
  have h2 : t ^ 2 = 1 - 1 / x := Real.sq_sqrt hB
  have hdiff : (s - t) * (s + t) = 2 / x := by
    have hexp : (s - t) * (s + t) = s ^ 2 - t ^ 2 := by ring
    rw [hexp, h1, h2]
    ring
  rw [hsq1, hsq2, ← mul_sub, div_eq_iff (ne_of_gt hsum)]
  have hassoc : x * (s - t) * (s + t) = x * ((s - t) * (s + t)) := by ring
  rw [hassoc, hdiff]
  field_simp

/-- 3.3 i) `lim_{x→∞} sin(2x)/x = 0` (rendőrelv). -/
theorem gyak_3_3_i : Tendsto (fun x : ℝ => Real.sin (2 * x) / x) atTop (𝓝 0) := by
  have hg : Tendsto (fun x : ℝ => 1 / x) atTop (𝓝 0) := by
    simpa using tendsto_const_div_pow_atTop 1 (k := 1) (by norm_num)
  refine squeeze_zero_norm' ?_ hg
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le zero_lt_one hx
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hx0]
  gcongr
  exact Real.abs_sin_le_one _

/-! ## 3.4. gyakorlat — „0/0” típusú határértékek véges helyen -/

/-- 3.4 a) `lim_{x→2} (x-2)/(x²-4) = 1/4`. -/
theorem gyak_3_4_a :
    Tendsto (fun x : ℝ => (x - 2) / (x ^ 2 - 4)) (punktalt 2) (𝓝 (1 / 4)) := by
  have hc : Tendsto (fun x : ℝ => 1 / (x + 2)) (𝓝 2) (𝓝 (1 / ((2 : ℝ) + 2))) :=
    ContinuousAt.div continuousAt_const (by fun_prop) (by norm_num)
  rw [show (1 : ℝ) / ((2 : ℝ) + 2) = 1 / 4 by norm_num] at hc
  refine (hc.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (eventually_gt_nhds (by norm_num : (0 : ℝ) < 2))] with x hx hx0
  have h : x - 2 ≠ 0 := sub_ne_zero.mpr hx
  have h2 : x + 2 ≠ 0 := by positivity
  rw [show x ^ 2 - 4 = (x - 2) * (x + 2) by ring]
  field_simp

/-- 3.4 b) `lim_{x→-1} (x²+3x+2)/(x²+4x+3) = 1/2`. -/
theorem gyak_3_4_b :
    Tendsto (fun x : ℝ => (x ^ 2 + 3 * x + 2) / (x ^ 2 + 4 * x + 3)) (punktalt (-1))
      (𝓝 (1 / 2)) := by
  have hc : Tendsto (fun x : ℝ => (x + 2) / (x + 3)) (𝓝 (-1)) (𝓝 (((-1 : ℝ) + 2) / (-1 + 3))) :=
    ContinuousAt.div (by fun_prop) (by fun_prop) (by norm_num)
  rw [show ((-1 : ℝ) + 2) / (-1 + 3) = 1 / 2 by norm_num] at hc
  refine (hc.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (eventually_gt_nhds (by norm_num : (-2 : ℝ) < -1))] with x hx hx0
  have hx' : x ≠ -1 := hx
  have h : x + 1 ≠ 0 := fun hc' => hx' (by linarith)
  have h3 : x + 3 ≠ 0 := by intro hc'; linarith
  rw [show x ^ 2 + 3 * x + 2 = (x + 1) * (x + 2) by ring,
    show x ^ 2 + 4 * x + 3 = (x + 1) * (x + 3) by ring]
  exact (mul_div_mul_left _ _ h).symm

/-! ## 3.7. gyakorlat — a nevezetes `sin x / x` határérték -/

/-- 3.7 alap: `lim_{x→0} sin x / x = 1`.
Trükk: ez pontosan a `sin` differenciahányadosának határértéke a `0`-ban, azaz `sin'(0) = 1`. -/
theorem gyak_3_7_alap : Tendsto (fun x : ℝ => Real.sin x / x) (punktalt 0) (𝓝 1) := by
  have h : HasDerivAt Real.sin 1 0 := by simpa using Real.hasDerivAt_sin 0
  refine (hasDerivAt_iff_tendsto_slope.mp h).congr ?_
  intro x
  simp [slope_def_field, div_eq_inv_mul]

/-- 3.7 b) `lim_{x→0} sin(3x)/x = 3`. Ugyanaz a trükk: `(sin ∘ (3·))'(0) = 3`. -/
theorem gyak_3_7_b : Tendsto (fun x : ℝ => Real.sin (3 * x) / x) (punktalt 0) (𝓝 3) := by
  have h : HasDerivAt (fun x : ℝ => Real.sin (3 * x)) 3 0 := by
    have := (Real.hasDerivAt_sin (3 * (0 : ℝ))).comp 0 ((hasDerivAt_id (0 : ℝ)).const_mul 3)
    simpa using this
  refine (hasDerivAt_iff_tendsto_slope.mp h).congr ?_
  intro x
  simp [slope_def_field, div_eq_inv_mul]

/-- 3.7 i) `lim_{x→0} (1 - cos x)/x² = 1/2`. -/
theorem gyak_3_7_i :
    Tendsto (fun x : ℝ => (1 - Real.cos x) / x ^ 2) (punktalt 0) (𝓝 (1 / 2)) := by
  have hhalf : Tendsto (fun x : ℝ => (1 / 2 : ℝ) * x) (punktalt 0) (punktalt 0) := by
    simpa using tendsto_punktalt_const_mul (c := (1 / 2 : ℝ)) (by norm_num) 0
  have hcomp : Tendsto (fun x : ℝ => Real.sin ((1 / 2 : ℝ) * x) / ((1 / 2 : ℝ) * x))
      (punktalt 0) (𝓝 1) := gyak_3_7_alap.comp hhalf
  have hsq : Tendsto
      (fun x : ℝ => (1 / 2 : ℝ) *
        (Real.sin ((1 / 2 : ℝ) * x) / ((1 / 2 : ℝ) * x)) ^ 2) (punktalt 0) (𝓝 ((1 / 2) * 1 ^ 2)) :=
    tendsto_const_nhds.mul (hcomp.pow 2)
  rw [show (1 / 2 : ℝ) * 1 ^ 2 = 1 / 2 by norm_num] at hsq
  refine hsq.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hx0 : x ≠ 0 := hx
  have key : Real.sin (x / 2) ^ 2 = (1 - Real.cos x) / 2 := by
    have h1 : Real.cos (2 * (x / 2)) = Real.cos (x / 2) ^ 2 - Real.sin (x / 2) ^ 2 :=
      Real.cos_two_mul' _
    have h2 := Real.sin_sq_add_cos_sq (x / 2)
    rw [show 2 * (x / 2) = x by ring] at h1
    linarith
  have hhx : (1 / 2 : ℝ) * x = x / 2 := by ring
  rw [hhx, div_pow, key]
  field_simp

/-! ## 3.8. gyakorlat — „1/0” típusú határértékek -/

/-- 3.8 b) `lim_{x→2⁻} (-3)/(x-2) = +∞`. -/
theorem gyak_3_8_b :
    Tendsto (fun x : ℝ => (-3) / (x - 2)) (nhdsWithin 2 (Set.Iio 2)) atTop := by
  have h1 : Tendsto (fun x : ℝ => 2 - x) (nhdsWithin 2 (Set.Iio 2)) (nhdsWithin 0 (Set.Ioi 0)) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have h0 : Tendsto (fun x : ℝ => 2 - x) (𝓝 2) (𝓝 ((2 : ℝ) - 2)) :=
        (continuous_const.sub continuous_id).tendsto 2
      simpa using h0.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      simp only [Set.mem_Ioi]
      exact sub_pos.mpr hx
  have h2 : Tendsto (fun x : ℝ => (2 - x)⁻¹) (nhdsWithin 2 (Set.Iio 2)) atTop :=
    tendsto_inv_nhdsGT_zero.comp h1
  have h3 : Tendsto (fun x : ℝ => 3 * (2 - x)⁻¹) (nhdsWithin 2 (Set.Iio 2)) atTop :=
    h2.const_mul_atTop (by norm_num)
  refine h3.congr ?_
  intro x
  rw [show x - 2 = -(2 - x) by ring]
  rcases eq_or_ne (2 - x) 0 with h | h
  · rw [h]; simp
  · field_simp

/-- 3.8 e) `lim_{x→7} 4/(x-7)² = +∞`. -/
theorem gyak_3_8_e : Tendsto (fun x : ℝ => 4 / (x - 7) ^ 2) (punktalt 7) atTop := by
  have h1 : Tendsto (fun x : ℝ => (x - 7) ^ 2) (punktalt 7) (nhdsWithin 0 (Set.Ioi 0)) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have h0 : Tendsto (fun x : ℝ => (x - 7) ^ 2) (𝓝 7) (𝓝 (((7 : ℝ) - 7) ^ 2)) :=
        ((continuous_id.sub continuous_const).pow 2).tendsto 7
      simpa using h0.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      have h : x - 7 ≠ 0 := sub_ne_zero.mpr hx
      simp only [Set.mem_Ioi]
      exact lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 h))
  have h2 : Tendsto (fun x : ℝ => ((x - 7) ^ 2)⁻¹) (punktalt 7) atTop :=
    tendsto_inv_nhdsGT_zero.comp h1
  have h3 : Tendsto (fun x : ℝ => 4 * ((x - 7) ^ 2)⁻¹) (punktalt 7) atTop :=
    h2.const_mul_atTop (by norm_num)
  exact h3.congr (fun x => by rw [div_eq_mul_inv])

/-! ## 3.10. gyakorlat — az `e` szám körüli határértékek -/

/-- 3.10 d) `lim_{x→∞} (1 + 3/x)^x = e³`. -/
theorem gyak_3_10_d :
    Tendsto (fun x : ℝ => (1 + 3 / x) ^ x) atTop (𝓝 (Real.exp 3)) :=
  Real.tendsto_one_add_div_rpow_exp 3

/-- 3.10 a) `lim_{x→∞} (1 - 1/x)^x = e⁻¹`. -/
theorem gyak_3_10_a :
    Tendsto (fun x : ℝ => (1 + (-1) / x) ^ x) atTop (𝓝 (Real.exp (-1))) :=
  Real.tendsto_one_add_div_rpow_exp (-1)

/-! ## 3.11-3.13. gyakorlat — folytonosság, megszüntethető szakadás -/

/-- 3.12 a) `h(t) = (t²+3t-10)/(t-2)` a `t = 2` helyen `h(2) = 7`-tel folytonossá tehető. -/
theorem gyak_3_12_a :
    Tendsto (fun t : ℝ => (t ^ 2 + 3 * t - 10) / (t - 2)) (punktalt 2) (𝓝 7) := by
  have hc : Tendsto (fun t : ℝ => t + 5) (𝓝 2) (𝓝 ((2 : ℝ) + 5)) :=
    (continuous_id.add continuous_const).tendsto 2
  rw [show (2 : ℝ) + 5 = 7 by norm_num] at hc
  refine (hc.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have h : t - 2 ≠ 0 := sub_ne_zero.mpr ht
  rw [show t ^ 2 + 3 * t - 10 = (t - 2) * (t + 5) by ring]
  field_simp

/-- 3.12 b) `g(x) = (x²-16)/(x²-3x-4)` a `x = 4` helyen `g(4) = 8/5`-tel folytonossá tehető. -/
theorem gyak_3_12_b :
    Tendsto (fun x : ℝ => (x ^ 2 - 16) / (x ^ 2 - 3 * x - 4)) (punktalt 4) (𝓝 (8 / 5)) := by
  have hc : Tendsto (fun x : ℝ => (x + 4) / (x + 1)) (𝓝 4) (𝓝 (((4 : ℝ) + 4) / (4 + 1))) :=
    ContinuousAt.div (by fun_prop) (by fun_prop) (by norm_num)
  rw [show ((4 : ℝ) + 4) / (4 + 1) = 8 / 5 by norm_num] at hc
  refine (hc.mono_left nhdsWithin_le_nhds).congr' ?_
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (eventually_gt_nhds (by norm_num : (0 : ℝ) < 4))] with x hx hx0
  have h : x - 4 ≠ 0 := sub_ne_zero.mpr hx
  have h1 : x + 1 ≠ 0 := by positivity
  rw [show x ^ 2 - 16 = (x - 4) * (x + 4) by ring,
    show x ^ 2 - 3 * x - 4 = (x - 4) * (x + 1) by ring]
  field_simp

/-- 3.13 A `f(x) = x²-1` (`x<3`), `f(x) = 2ax` (`x≥3`) függvény pontosan `a = 4/3` esetén
folytonos mindenütt. -/
theorem gyak_3_13 (a : ℝ) :
    Continuous (fun x : ℝ => if x < 3 then x ^ 2 - 1 else 2 * a * x) ↔ a = 4 / 3 := by
  constructor
  · intro hcont
    -- a bal oldali határérték 8, a helyettesítési érték 2·a·3
    have hlim : Tendsto (fun x : ℝ => if x < 3 then x ^ 2 - 1 else 2 * a * x)
        (nhdsWithin 3 (Set.Iio 3)) (𝓝 (2 * a * 3)) := by
      have h0 := (hcont.tendsto 3).mono_left
        (nhdsWithin_le_nhds (a := (3 : ℝ)) (s := Set.Iio 3))
      simpa only [if_neg (show ¬ (3 : ℝ) < 3 by norm_num)] using h0
    have hlim2 : Tendsto (fun x : ℝ => x ^ 2 - 1) (nhdsWithin 3 (Set.Iio 3)) (𝓝 (2 * a * 3)) := by
      refine hlim.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with x hx
      simp only [Set.mem_Iio] at hx
      rw [if_pos hx]
    have hlim3 : Tendsto (fun x : ℝ => x ^ 2 - 1) (nhdsWithin 3 (Set.Iio 3)) (𝓝 8) := by
      have h1 : Tendsto (fun x : ℝ => x ^ 2 - 1) (𝓝 3) (𝓝 ((3 : ℝ) ^ 2 - 1)) :=
        ((continuous_pow 2).sub continuous_const).tendsto 3
      rw [show (3 : ℝ) ^ 2 - 1 = 8 by norm_num] at h1
      exact h1.mono_left nhdsWithin_le_nhds
    have huniq := tendsto_nhds_unique hlim2 hlim3
    linarith
  · rintro rfl
    have heq : (fun x : ℝ => if x < 3 then x ^ 2 - 1 else 2 * (4 / 3 : ℝ) * x) =
        fun x : ℝ => if (3 : ℝ) ≤ x then 2 * (4 / 3 : ℝ) * x else x ^ 2 - 1 := by
      funext x
      by_cases h : x < 3
      · rw [if_pos h, if_neg (by linarith)]
      · rw [if_neg h, if_pos (by linarith)]
    rw [heq]
    refine Continuous.if_le (by fun_prop) (by fun_prop) continuous_const continuous_id ?_
    intro x hx
    rw [← hx]
    norm_num

/-! ## 3.14-3.16. gyakorlat — szerkezeti állítások -/

/-- 3.14 (*) Korlátos, monoton növő függvénynek van (véges) bal oldali határértéke `b`-ben. -/
theorem gyak_3_14 {a b : ℝ} (hab : a < b) (f : ℝ → ℝ)
    (hmono : MonotoneOn f (Set.Ioo a b)) (hbdd : BddAbove (f '' Set.Ioo a b)) :
    ∃ L : ℝ, Tendsto f (nhdsWithin b (Set.Iio b)) (𝓝 L) :=
  ⟨sSup (f '' Set.Ioo a b),
    MonotoneOn.tendsto_nhdsWithin_Ioo_left (Set.nonempty_Ioo.mpr hab) hmono hbdd⟩

/-- 3.15 (*) Ha két folytonos függvény minden racionális helyen megegyezik, akkor egyenlők. -/
theorem gyak_3_15 {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ q : ℚ, f q = g q) : f = g := by
  refine Continuous.ext_on (Rat.denseRange_cast (𝕜 := ℝ)) hf hg ?_
  rintro x ⟨q, rfl⟩
  exact h q

/-- 3.16 b) Az `(1 + 1/n)ⁿ` sorozat szigorúan monoton nő. -/
theorem gyak_3_16_b (n : ℕ) (hn : 1 ≤ n) :
    (1 + 1 / (n : ℝ)) ^ n < (1 + 1 / ((n : ℝ) + 1)) ^ (n + 1) := by
  have hm0 : (0 : ℝ) < n := by exact_mod_cast hn
  set m : ℝ := (n : ℝ) with hm_def
  have hm1 : (0 : ℝ) < m + 1 := by linarith
  have hs : (-1 : ℝ) ≤ -(1 / (m + 1) ^ 2) := by
    rw [neg_le_neg_iff, div_le_one (by positivity)]
    nlinarith
  have hs' : -(1 / (m + 1) ^ 2) ≠ 0 := by
    have h : (0 : ℝ) < 1 / (m + 1) ^ 2 := by positivity
    linarith
  have hp : (1 : ℝ) < m + 1 := by linarith
  -- szigorú Bernoulli-egyenlőtlenség
  have key := one_add_mul_self_lt_rpow_one_add hs hs' hp
  have hcast : ((1 : ℝ) + -(1 / (m + 1) ^ 2)) ^ (m + 1) = (1 - 1 / (m + 1) ^ 2) ^ (n + 1) := by
    rw [show m + 1 = ((n + 1 : ℕ) : ℝ) by push_cast [hm_def]; ring, Real.rpow_natCast]
    ring
  rw [hcast] at key
  have hleft : m / (m + 1) ≤ 1 + (m + 1) * -(1 / (m + 1) ^ 2) := by
    field_simp
    linarith
  have key2 : m / (m + 1) < (1 - 1 / (m + 1) ^ 2) ^ (n + 1) := lt_of_le_of_lt hleft key
  set u : ℝ := 1 + 1 / m with hu_def
  set v : ℝ := 1 + 1 / (m + 1) with hv_def
  have hu : 0 < u := by rw [hu_def]; positivity
  have hratio : v / u = 1 - 1 / (m + 1) ^ 2 := by
    rw [hu_def, hv_def]; field_simp; ring
  rw [← hratio, div_pow, lt_div_iff₀ (pow_pos hu _)] at key2
  have hmu : m / (m + 1) * u = 1 := by rw [hu_def]; field_simp
  have hexp : m / (m + 1) * u ^ (n + 1) = u ^ n := by
    rw [pow_succ, ← mul_assoc, mul_comm (m / (m + 1)) (u ^ n), mul_assoc, hmu, mul_one]
  rw [hexp] at key2
  exact key2

/-- 3.16 c) Az `(1 + 1/n)ⁿ` sorozat felülről korlátos: `< 4`.
Trükk: `1 + t ≤ eᵗ`, ezért `(1+1/n)ⁿ ≤ e < 4`. -/
theorem gyak_3_16_c (n : ℕ) (hn : 1 ≤ n) : (1 + 1 / (n : ℝ)) ^ n < 4 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hbase : (0 : ℝ) < 1 + 1 / n := by positivity
  have hle : 1 + 1 / (n : ℝ) ≤ Real.exp (1 / n) := by
    have := Real.add_one_le_exp (1 / (n : ℝ))
    linarith
  have hpow : (1 + 1 / (n : ℝ)) ^ n ≤ (Real.exp (1 / n)) ^ n :=
    pow_le_pow_left₀ hbase.le hle n
  have hexp : (Real.exp (1 / (n : ℝ))) ^ n = Real.exp 1 := by
    rw [← Real.exp_nat_mul]
    congr 1
    field_simp
  rw [hexp] at hpow
  have : Real.exp 1 < 4 := lt_trans Real.exp_one_lt_d9 (by norm_num)
  linarith

end Kalkulus1.Szakasz3
