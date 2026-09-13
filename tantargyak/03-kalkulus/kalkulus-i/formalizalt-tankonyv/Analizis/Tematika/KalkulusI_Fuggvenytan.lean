import Analizis.Tematika.KalkulusI
import Analizis.Ch05h_VegtelenbenVettHatarertek

/-!
# Kalkulus I. (MBLK37E) — függvénytani alapok és nevezetes határértékek

Ez a modul a *Kalkulus I. előadás* tematikájának azon pontjait formalizálja, amelyek a
`Tematika/KalkulusI.lean` modulban még nem szerepeltek:

1. **Értelmezési tartomány, értékkészlet, injektivitás, inverz függvény** (és az inverz
   grafikonjának tükrözési tulajdonsága).
2. **Összetett függvény** és tulajdonságai (folytonosság, monotonitás).
3. **Szimmetriatulajdonságok:** páros és páratlan függvények, periodicitás.
4. **Elemi határérték-számítási technikák:** a nevezetes határértékek
   (`sin x / x`, `(1 - cos x)/x²`, `(eˣ - 1)/x`, `log(1+x)/x`), racionális törtfüggvény
   határértéke a végtelenben, valamint a **gyöktelenítés** módszere.

A modul a Leindler-jegyzet fogalmait használja (`CauchyHatarErtek`,
`HatarErtekVegtelenben`, `CauchyFolytonos`, `ParosFv`, `ParatlanFv`), és minden
határértéket a könyv `ε`–`δ` definíciója szerint mond ki; a bizonyítások a
`cauchyHatarErtek_iff_tendsto` híd-lemmán keresztül a Mathlib eszköztárára támaszkodnak.
-/

namespace Tematika.KalkulusI

open Set Filter Topology
open Leindler Leindler.Ch05

/-! ## 1. Értelmezési tartomány, értékkészlet, inverz függvény -/

/-- Egy `f` függvény **értékkészlete** a `D` értelmezési tartományon: `f[D]`. -/
def ErtekKeszlet (f : ℝ → ℝ) (D : Set ℝ) : Set ℝ := f '' D

theorem mem_ertekKeszlet {f : ℝ → ℝ} {D : Set ℝ} {y : ℝ} :
    y ∈ ErtekKeszlet f D ↔ ∃ x ∈ D, f x = y := by
  simp [ErtekKeszlet]

/-- Szigorúan monoton függvény injektív az értelmezési tartományán. -/
theorem szigNovekedo_injektiv {f : ℝ → ℝ} {D : Set ℝ} (h : SzigNovekedo f D) :
    Set.InjOn f D := by
  intro x hx y hy hxy
  rcases lt_trichotomy x y with hlt | heq | hgt
  · exact absurd hxy (ne_of_lt (h x hx y hy hlt))
  · exact heq
  · exact absurd hxy.symm (ne_of_lt (h y hy x hx hgt))

/-- **Az inverz függvény grafikonja** az eredeti grafikon tükörképe az `y = x`
egyenesre: `(x, y)` pontosan akkor van `f` grafikonján, ha `(y, x)` a `g` grafikonján,
ahol `g` az `f` (kétoldali) inverze. -/
theorem inverz_grafikon_tukrozes {f g : ℝ → ℝ}
    (hgf : Function.LeftInverse g f) (hfg : Function.RightInverse g f) (x y : ℝ) :
    f x = y ↔ g y = x := by
  constructor
  · intro h; rw [← h, hgf x]
  · intro h; rw [← h]; exact hfg y

/-- Az exponenciális és a logaritmusfüggvény: a grafikonok egymás tükörképei. -/
theorem exp_log_grafikon {x y : ℝ} (hy : 0 < y) : Real.exp x = y ↔ Real.log y = x := by
  constructor
  · intro h; rw [← h, Real.log_exp]
  · intro h; rw [← h, Real.exp_log hy]

/-! ## 2. Összetett függvény -/

/-- **Összetett függvény folytonossága**: ha `g` folytonos `x₀`-ban és `f` folytonos
`g(x₀)`-ban, akkor `f ∘ g` folytonos `x₀`-ban. -/
theorem osszetett_folytonos {f g : ℝ → ℝ} {x₀ : ℝ} (hg : CauchyFolytonos g x₀)
    (hf : CauchyFolytonos f (g x₀)) : CauchyFolytonos (fun x => f (g x)) x₀ := by
  rw [← heineFolytonos_iff_cauchyFolytonos] at hg hf ⊢
  exact folytonos_osszetett hg hf

/-- **Növekedő függvények kompozíciója növekedő.** -/
theorem osszetett_szigNovekedo {f g : ℝ → ℝ} {D E : Set ℝ} (hg : SzigNovekedo g D)
    (hf : SzigNovekedo f E) (hmap : ∀ x ∈ D, g x ∈ E) :
    SzigNovekedo (fun x => f (g x)) D := by
  intro x hx y hy hxy
  exact hf (g x) (hmap x hx) (g y) (hmap y hy) (hg x hx y hy hxy)

/-- **Növekedő és csökkenő függvény kompozíciója csökkenő.** -/
theorem osszetett_szigCsokkeno {f g : ℝ → ℝ} {D E : Set ℝ} (hg : SzigNovekedo g D)
    (hf : SzigCsokkeno f E) (hmap : ∀ x ∈ D, g x ∈ E) :
    SzigCsokkeno (fun x => f (g x)) D := by
  intro x hx y hy hxy
  exact hf (g x) (hmap x hx) (g y) (hmap y hy) (hg x hx y hy hxy)

/-! ## 3. Szimmetriatulajdonságok -/

/-- Páros függvény grafikonja szimmetrikus az `y` tengelyre: ha `(x, y)` rajta van,
akkor `(-x, y)` is. -/
theorem paros_grafikon_szimmetrikus {f : ℝ → ℝ} (h : ParosFv f) (x y : ℝ) :
    f x = y ↔ f (-x) = y := by
  rw [← h x]

/-- Páratlan függvény grafikonja szimmetrikus az origóra: ha `(x, y)` rajta van, akkor
`(-x, -y)` is. -/
theorem paratlan_grafikon_szimmetrikus {f : ℝ → ℝ} (h : ParatlanFv f) (x y : ℝ) :
    f x = y ↔ f (-x) = -y := by
  rw [h x]
  constructor
  · intro hx; rw [hx]
  · intro hx; linarith

/-- Két páratlan függvény szorzata páros. -/
theorem paratlan_mul_paratlan {f g : ℝ → ℝ} (hf : ParatlanFv f) (hg : ParatlanFv g) :
    ParosFv (fun x => f x * g x) := by
  intro x
  simp only
  rw [hf x, hg x]
  ring

/-- Páros és páratlan függvény szorzata páratlan. -/
theorem paros_mul_paratlan {f g : ℝ → ℝ} (hf : ParosFv f) (hg : ParatlanFv g) :
    ParatlanFv (fun x => f x * g x) := by
  intro x
  simp only
  rw [← hf x, hg x]
  ring

/-- A szinuszfüggvény `2π` szerint periodikus. -/
theorem sin_periodikus (x : ℝ) : Real.sin (x + 2 * Real.pi) = Real.sin x :=
  Real.sin_add_two_pi x

/-! ## 4. Elemi határérték-számítási technikák

Először egy híd-lemma: a végtelenben vett határérték könyvbeli definíciója megegyezik a
Mathlib `Filter.Tendsto _ atTop (𝓝 c)` fogalmával.
-/

/-- **Híd-lemma.** A `+∞`-ben vett határérték `ε`–`K` definíciója (5.18. Definíció)
ekvivalens a Mathlib `Tendsto f atTop (𝓝 c)` fogalmával. -/
theorem hatarErtekVegtelenben_iff_tendsto (f : ℝ → ℝ) (c : ℝ) :
    HatarErtekVegtelenben f c ↔ Filter.Tendsto f Filter.atTop (nhds c) := by
  rw [Metric.tendsto_atTop]
  constructor
  · intro h ε hε
    obtain ⟨K, hK⟩ := h ε hε
    exact ⟨K + 1, fun n hn => by simpa [Real.dist_eq] using hK n (by linarith)⟩
  · intro h ε hε
    obtain ⟨K, hK⟩ := h ε hε
    exact ⟨K, fun x hx => by simpa [Real.dist_eq] using hK x hx.le⟩

/-- **Nevezetes határérték:** `lim_{x→0} (sin x)/x = 1`.

*Bizonyítás.* A hányados éppen a `sin` függvény `0` pontbeli különbségi hányadosa, és
`sin'(0) = cos 0 = 1`. -/
theorem sin_per_x_hatarertek : CauchyHatarErtek (fun x : ℝ => Real.sin x / x) 0 1 := by
  rw [cauchyHatarErtek_iff_tendsto]
  have h := Real.hasDerivAt_sin 0
  rw [hasDerivAt_iff_tendsto_slope] at h
  simp only [Real.cos_zero] at h
  convert h using 2 with x
  simp [slope, Real.sin_zero, div_eq_inv_mul]

/-- **Nevezetes határérték:** `lim_{x→0} (eˣ - 1)/x = 1` (az `exp` deriváltja `0`-ban). -/
theorem exp_per_x_hatarertek :
    CauchyHatarErtek (fun x : ℝ => (Real.exp x - 1) / x) 0 1 := by
  rw [cauchyHatarErtek_iff_tendsto]
  have h := Real.hasDerivAt_exp 0
  rw [hasDerivAt_iff_tendsto_slope] at h
  simp only [Real.exp_zero] at h
  convert h using 2 with x
  simp [slope, div_eq_inv_mul]

/-- **Nevezetes határérték:** `lim_{x→0} log(1+x)/x = 1`. -/
theorem log_per_x_hatarertek :
    CauchyHatarErtek (fun x : ℝ => Real.log (1 + x) / x) 0 1 := by
  rw [cauchyHatarErtek_iff_tendsto]
  have h : HasDerivAt (fun x : ℝ => Real.log (1 + x)) 1 0 := by
    simpa using ((hasDerivAt_id (0 : ℝ)).const_add (1 : ℝ)).log (by norm_num)
  rw [hasDerivAt_iff_tendsto_slope] at h
  convert h using 2 with x
  simp [slope, div_eq_inv_mul]

/-- **Nevezetes határérték:** `lim_{x→0} (1 - cos x)/x² = 1/2`.

*Bizonyítás.* `1 - cos x = 2 sin²(x/2)`, így a hányados
`½ · (sin(x/2)/(x/2))²`, és az előző nevezetes határérték alkalmazható. -/
theorem egy_minusz_cos_per_x_negyzet :
    CauchyHatarErtek (fun x : ℝ => (1 - Real.cos x) / x ^ 2) 0 (1 / 2) := by
  rw [cauchyHatarErtek_iff_tendsto]
  have hs : Filter.Tendsto (fun x : ℝ => Real.sin x / x) (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhds 1) := by
    rw [← cauchyHatarErtek_iff_tendsto]
    exact sin_per_x_hatarertek
  have hhalf : Filter.Tendsto (fun x : ℝ => x / 2) (nhdsWithin 0 {(0 : ℝ)}ᶜ)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have h0 : Filter.Tendsto (fun x : ℝ => x / 2) (nhds 0) (nhds 0) := by
        simpa using (continuous_id.div_const (2 : ℝ)).tendsto 0
      exact h0.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with x hx
      have hx0 : x ≠ 0 := by simpa using hx
      simp [hx0]
  have hsq := ((hs.comp hhalf).mul (hs.comp hhalf)).div_const 2
  have hgoal : Filter.Tendsto (fun x : ℝ => (1 - Real.cos x) / x ^ 2)
      (nhdsWithin 0 {(0 : ℝ)}ᶜ) (nhds (1 * 1 / 2)) := by
    refine hsq.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with x hx
    have hx0 : x ≠ 0 := by simpa using hx
    have hcos : 1 - Real.cos x = 2 * Real.sin (x / 2) ^ 2 := by
      have h1 : Real.cos (2 * (x / 2)) = 1 - 2 * Real.sin (x / 2) ^ 2 := by
        rw [Real.cos_two_mul]
        nlinarith [Real.sin_sq_add_cos_sq (x / 2)]
      rw [show (2 : ℝ) * (x / 2) = x by ring] at h1
      rw [h1]; ring
    simp only [Function.comp]
    field_simp
    linarith [hcos]
  simpa using hgoal

/-- **Racionális törtfüggvény határértéke a végtelenben:** a legmagasabb fokú tagok
együtthatóinak hányadosa, ha a számláló és a nevező foka megegyezik. -/
theorem racionalis_hatarertek_vegtelenben :
    HatarErtekVegtelenben (fun x : ℝ => (2 * x ^ 2 + 3 * x) / (5 * x ^ 2 - 1)) (2 / 5) := by
  rw [hatarErtekVegtelenben_iff_tendsto]
  have hnum : Filter.Tendsto (fun x : ℝ => 2 + 3 * x⁻¹) Filter.atTop (nhds 2) := by
    have h := tendsto_inv_atTop_zero (𝕜 := ℝ)
    simpa using (tendsto_const_nhds (x := (2 : ℝ)) (f := Filter.atTop (α := ℝ))).add
      (h.const_mul (3 : ℝ))
  have hden : Filter.Tendsto (fun x : ℝ => 5 - (x ^ 2)⁻¹) Filter.atTop (nhds 5) := by
    have hpow : Filter.Tendsto (fun x : ℝ => x ^ 2) Filter.atTop Filter.atTop :=
      tendsto_pow_atTop (n := 2) (by norm_num)
    have h : Filter.Tendsto (fun x : ℝ => (x ^ 2)⁻¹) Filter.atTop (nhds 0) :=
      hpow.inv_tendsto_atTop
    simpa using (tendsto_const_nhds (x := (5 : ℝ)) (f := Filter.atTop (α := ℝ))).sub h
  have hquot : Filter.Tendsto (fun x : ℝ => (2 + 3 * x⁻¹) / (5 - (x ^ 2)⁻¹))
      Filter.atTop (nhds (2 / 5)) := hnum.div hden (by norm_num)
  refine hquot.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with x hx
  have hx0 : x ≠ 0 := by intro h; rw [h] at hx; linarith
  have hden0 : 5 * x ^ 2 - 1 ≠ 0 := by nlinarith
  field_simp

/-- **Gyöktelenítés:** `lim_{x→∞} (√(x² + x) - x) = 1/2`.

*Bizonyítás.* A gyökös kifejezést a konjugálttal bővítve
`√(x²+x) - x = x/(√(x²+x) + x) = 1/(√(1 + 1/x) + 1)`, és az utóbbi `1/2`-hez tart. -/
theorem gyoktelenites_hatarertek :
    HatarErtekVegtelenben (fun x : ℝ => Real.sqrt (x ^ 2 + x) - x) (1 / 2) := by
  rw [hatarErtekVegtelenben_iff_tendsto]
  have h1 : Filter.Tendsto (fun x : ℝ => 1 + x⁻¹) Filter.atTop (nhds 1) := by
    simpa using (tendsto_const_nhds (x := (1 : ℝ)) (f := Filter.atTop (α := ℝ))).add
      tendsto_inv_atTop_zero
  have h2 : Filter.Tendsto (fun x : ℝ => Real.sqrt (1 + x⁻¹) + 1) Filter.atTop (nhds 2) := by
    have h := (Real.continuous_sqrt.tendsto (1 : ℝ)).comp h1
    simp only [Real.sqrt_one] at h
    have h4 := h.add (tendsto_const_nhds (x := (1 : ℝ)))
    norm_num at h4
    exact h4
  have h3 : Filter.Tendsto (fun x : ℝ => 1 / (Real.sqrt (1 + x⁻¹) + 1)) Filter.atTop
      (nhds (1 / 2)) := (tendsto_const_nhds (x := (1 : ℝ))).div h2 two_ne_zero
  refine h3.congr' ?_
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with x hx
  have hx0 : x ≠ 0 := ne_of_gt hx
  have hprod : x ^ 2 * (1 + x⁻¹) = x ^ 2 + x := by field_simp
  have hsq : Real.sqrt (x ^ 2 + x) = x * Real.sqrt (1 + x⁻¹) := by
    calc Real.sqrt (x ^ 2 + x) = Real.sqrt (x ^ 2 * (1 + x⁻¹)) := by rw [hprod]
      _ = Real.sqrt (x ^ 2) * Real.sqrt (1 + x⁻¹) := Real.sqrt_mul (by positivity) _
      _ = x * Real.sqrt (1 + x⁻¹) := by rw [Real.sqrt_sq hx.le]
  set s := Real.sqrt (1 + x⁻¹) with hs
  have hs2 : s ^ 2 = 1 + x⁻¹ := Real.sq_sqrt (by positivity)
  have hpos : 0 < s + 1 := by positivity
  rw [hsq, eq_comm, eq_div_iff (ne_of_gt hpos)]
  have hexp : (x * s - x) * (s + 1) = x * (s ^ 2 - 1) := by ring
  rw [hexp, hs2]
  field_simp
  ring

end Tematika.KalkulusI
