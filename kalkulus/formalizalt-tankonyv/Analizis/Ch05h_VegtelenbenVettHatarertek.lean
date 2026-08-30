import Analizis.Ch05d_FuggvenyHatarertek

/-!
# Leindler László: Analízis — 5.18–5.19. pont (folytatás)

Ez a modul a végtelenben vett határérték **Heine-féle** definícióit (5.18.1., 5.19.1.)
és a `Ch05d_FuggvenyHatarertek` modulban már szereplő **Cauchy-féle** definíciókkal
(5.18.2., 5.19.2.) való ekvivalenciájukat tartalmazza, továbbá a mínusz végtelenben vett
határérték fogalmát, az `5.18.2.` utáni `lim_{x→∞} sign x = 1` példát és az
**5.19.3. Tételt**: `lim_{|x|→∞} (1 + 1/x)^x = e` (80–81. oldal).
-/

namespace Leindler.Ch05

open Filter Topology

/-! ## 5.18. Határérték a végtelenben -/

/-- **5.18.1. Definíció (Heine).** Az `f(x)` függvénynek a plusz végtelenben a
határértéke `c`, ha bármely `xₙ → ∞` sorozat esetén `f(xₙ) → c`. -/
def HeineHatarErtekVegtelenben (f : ℝ → ℝ) (c : ℝ) : Prop :=
  ∀ x : Ch04.Sorozat, Ch04.PlusVegtelenbeDivergal x → Ch04.HatarErtek (fun n => f (x n)) c

/-- **5.18.2. Definíció (Cauchy, mínusz végtelen).** Az `f(x)` függvénynek a mínusz
végtelenben a határértéke `c`, ha bármely `ε > 0`-hoz van olyan `D`, hogy ha `x < D`,
akkor `|f(x) - c| < ε`. -/
def HatarErtekMinuszVegtelenben (f : ℝ → ℝ) (c : ℝ) : Prop :=
  ∀ ε > 0, ∃ D : ℝ, ∀ x : ℝ, x < D → |f x - c| < ε

/-- **5.18.1. Definíció (Heine, mínusz végtelen).** -/
def HeineHatarErtekMinuszVegtelenben (f : ℝ → ℝ) (c : ℝ) : Prop :=
  ∀ x : Ch04.Sorozat, Ch04.MinuszVegtelenbeDivergal x → Ch04.HatarErtek (fun n => f (x n)) c

/-- **5.18. Tétel.** A `+∞`-ben vett határérték Heine- és Cauchy-féle definíciója
ekvivalens.

*Bizonyítás.* Cauchy ⇒ Heine: ha `ε > 0`-hoz `D` a Cauchy-definíció küszöbe és
`xₙ → ∞`, akkor van olyan `ν`, hogy `n > ν` esetén `xₙ > D`, tehát `|f(xₙ) - c| < ε`.
Heine ⇒ Cauchy indirekt: ha volna olyan `ε₀ > 0`, hogy minden `D`-hez van `x > D`
`|f(x) - c| ≥ ε₀`-lal, akkor a `D = n` választással kapott `xₙ` sorozat a végtelenbe
divergál, de `f(xₙ)` nem tart `c`-hez. -/
theorem heineHatarErtekVegtelenben_iff (f : ℝ → ℝ) (c : ℝ) :
    HeineHatarErtekVegtelenben f c ↔ HatarErtekVegtelenben f c := by
  constructor
  · intro hHeine
    by_contra hC
    unfold HatarErtekVegtelenben at hC
    push_neg at hC
    obtain ⟨ε₀, hε₀, hbad⟩ := hC
    choose x hxgt hfx using fun n : ℕ => hbad (n : ℝ)
    have hdiv : Ch04.PlusVegtelenbeDivergal x := by
      intro M
      obtain ⟨N, hN⟩ := exists_nat_gt M
      refine ⟨N, fun n hn => ?_⟩
      have h1 : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast le_of_lt hn
      exact lt_of_lt_of_le (lt_of_lt_of_le hN h1) (le_of_lt (hxgt n))
    obtain ⟨N, hN⟩ := hHeine x hdiv ε₀ hε₀
    exact absurd (hN (N + 1) (by omega)) (not_lt.2 (hfx (N + 1)))
  · intro hC x hdiv ε hε
    obtain ⟨K, hK⟩ := hC ε hε
    obtain ⟨N, hN⟩ := hdiv K
    exact ⟨N, fun n hn => hK (x n) (hN n hn)⟩

/-- **5.18. Tétel (mínusz végtelen).** -/
theorem heineHatarErtekMinuszVegtelenben_iff (f : ℝ → ℝ) (c : ℝ) :
    HeineHatarErtekMinuszVegtelenben f c ↔ HatarErtekMinuszVegtelenben f c := by
  constructor
  · intro hHeine
    by_contra hC
    unfold HatarErtekMinuszVegtelenben at hC
    push_neg at hC
    obtain ⟨ε₀, hε₀, hbad⟩ := hC
    choose x hxlt hfx using fun n : ℕ => hbad (-(n : ℝ))
    have hdiv : Ch04.MinuszVegtelenbeDivergal x := by
      intro m
      obtain ⟨N, hN⟩ := exists_nat_gt (-m)
      refine ⟨N, fun n hn => ?_⟩
      have h1 : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast le_of_lt hn
      have : -(n : ℝ) ≤ m := by linarith
      exact lt_of_lt_of_le (hxlt n) this
    obtain ⟨N, hN⟩ := hHeine x hdiv ε₀ hε₀
    exact absurd (hN (N + 1) (by omega)) (not_lt.2 (hfx (N + 1)))
  · intro hC x hdiv ε hε
    obtain ⟨D, hD⟩ := hC ε hε
    obtain ⟨N, hN⟩ := hdiv D
    exact ⟨N, fun n hn => hD (x n) (hN n hn)⟩

/-- **5.18. Példa.** `lim_{x→∞} sign x = 1`. -/
theorem szignum_vegtelenben : HatarErtekVegtelenben szignum 1 := by
  intro ε hε
  refine ⟨0, fun x hx => ?_⟩
  have : szignum x = 1 := by
    rw [szignum]
    simp [not_lt.2 (le_of_lt hx), ne_of_gt hx]
  simp [this, hε]

/-! ## 5.19. Végtelen határérték a végtelenben -/

/-- **5.19.1. Definíció (Heine).** Az `f(x)` függvénynek `+∞`-ben a határértéke `+∞`, ha
valahányszor `xₙ → +∞`, mindannyiszor `f(xₙ) → +∞`. -/
def HeineVegtelenHatarErtekVegtelenben (f : ℝ → ℝ) : Prop :=
  ∀ x : Ch04.Sorozat, Ch04.PlusVegtelenbeDivergal x →
    Ch04.PlusVegtelenbeDivergal (fun n => f (x n))

/-- **5.19. Tétel.** A `+∞`-beli `+∞` határérték Heine- és Cauchy-féle definíciója
ekvivalens.

*Bizonyítás.* Ugyanaz a gondolatmenet, mint az 5.18. Tételnél; az indirekt irányban a
„rossz” pontokból álló `xₙ > n`, `f(xₙ) < M₀` sorozatot használjuk. -/
theorem heineVegtelenHatarErtekVegtelenben_iff (f : ℝ → ℝ) :
    HeineVegtelenHatarErtekVegtelenben f ↔ VegtelenHatarErtekVegtelenben f := by
  constructor
  · intro hHeine
    by_contra hC
    unfold VegtelenHatarErtekVegtelenben at hC
    push_neg at hC
    obtain ⟨M₀, hbad⟩ := hC
    choose x hxgt hfx using fun n : ℕ => hbad (n : ℝ)
    have hdiv : Ch04.PlusVegtelenbeDivergal x := by
      intro M
      obtain ⟨N, hN⟩ := exists_nat_gt M
      refine ⟨N, fun n hn => ?_⟩
      have h1 : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast le_of_lt hn
      exact lt_of_lt_of_le (lt_of_lt_of_le hN h1) (le_of_lt (hxgt n))
    obtain ⟨N, hN⟩ := hHeine x hdiv M₀
    exact absurd (hN (N + 1) (by omega)) (not_lt.2 (le_of_lt (hfx (N + 1))))
  · intro hC x hdiv M
    obtain ⟨K, hK⟩ := hC (M + 1)
    obtain ⟨N, hN⟩ := hdiv K
    exact ⟨N, fun n hn => by linarith [hK (x n) (hN n hn)]⟩

/-! ## 5.19.3. Tétel -/

/-- **5.19.3. Tétel (a `+∞` eset).** `lim_{x→+∞} (1 + 1/x)^x = e`.

*Bizonyítás (a könyv gondolatmenete).* Mivel `(1 + 1/n)ⁿ → e` (4.16.1. Tétel), a
`[x] ≤ x < [x] + 1` becslésekkel a `(1 + 1/x)^x` kifejezés két `e`-hez tartó sorozat
közé szorítható. -/
theorem egy_plusz_egy_per_x_vegtelenben :
    HatarErtekVegtelenben (fun x : ℝ => (1 + 1 / x) ^ x) (Real.exp 1) := by
  have h : Tendsto (fun x : ℝ => (1 + 1 / x) ^ x) atTop (𝓝 (Real.exp 1)) := by
    simpa using Real.tendsto_one_add_div_rpow_exp 1
  intro ε hε
  have hmem : {y : ℝ | |y - Real.exp 1| < ε} ∈ 𝓝 (Real.exp 1) := by
    have : Metric.ball (Real.exp 1) ε ⊆ {y : ℝ | |y - Real.exp 1| < ε} := by
      intro y hy
      simpa [Real.dist_eq] using hy
    exact Filter.mem_of_superset (Metric.ball_mem_nhds _ hε) this
  obtain ⟨K, hK⟩ := (Filter.eventually_atTop.mp (h.eventually_mem hmem))
  exact ⟨K, fun x hx => hK x (le_of_lt hx)⟩

/-- **5.19.3. Tétel (a `-∞` eset).** `lim_{x→-∞} (1 + 1/x)^x = e`.

*Bizonyítás.* Az `x = -y` helyettesítéssel `(1 + 1/x)^x = ((1 - 1/y)^y)⁻¹`, és
`(1 - 1/y)^y → e⁻¹`, tehát a reciprok `e`-hez tart. -/
theorem egy_plusz_egy_per_x_minusz_vegtelenben :
    HatarErtekMinuszVegtelenben (fun x : ℝ => (1 + 1 / x) ^ x) (Real.exp 1) := by
  have hneg : Tendsto (fun y : ℝ => (1 + 1 / (-y)) ^ (-y)) atTop (𝓝 (Real.exp 1)) := by
    have h1 : Tendsto (fun y : ℝ => (1 + (-1) / y) ^ y) atTop (𝓝 (Real.exp (-1))) :=
      Real.tendsto_one_add_div_rpow_exp (-1)
    have h2 : Tendsto (fun y : ℝ => ((1 + (-1) / y) ^ y)⁻¹) atTop (𝓝 (Real.exp (-1))⁻¹) :=
      h1.inv₀ (Real.exp_ne_zero _)
    have h3 : (Real.exp (-1))⁻¹ = Real.exp 1 := by
      rw [Real.exp_neg, inv_inv]
    rw [h3] at h2
    refine h2.congr' ?_
    filter_upwards [eventually_gt_atTop (1 : ℝ)] with y hy
    have hy0 : (0 : ℝ) < y := lt_trans zero_lt_one hy
    have hbase : (0 : ℝ) ≤ 1 + (-1) / y := by
      have h1y : 1 / y ≤ 1 := by
        rw [div_le_one hy0]
        linarith
      rw [neg_div]
      linarith [h1y]
    have hrw : 1 + 1 / (-y) = 1 + (-1) / y := by
      rw [div_neg, neg_div]
    rw [hrw, Real.rpow_neg hbase]
  have hbot : Tendsto (fun x : ℝ => (1 + 1 / x) ^ x) atBot (𝓝 (Real.exp 1)) := by
    have hcomp := hneg.comp tendsto_neg_atBot_atTop
    have heq : ((fun y : ℝ => (1 + 1 / (-y)) ^ (-y)) ∘ (Neg.neg : ℝ → ℝ))
        = fun x : ℝ => (1 + 1 / x) ^ x := by
      funext x
      simp only [Function.comp_apply, neg_neg]
    rwa [heq] at hcomp
  intro ε hε
  have hmem : {y : ℝ | |y - Real.exp 1| < ε} ∈ 𝓝 (Real.exp 1) := by
    have hsub : Metric.ball (Real.exp 1) ε ⊆ {y : ℝ | |y - Real.exp 1| < ε} := by
      intro y hy
      simpa [Real.dist_eq] using hy
    exact Filter.mem_of_superset (Metric.ball_mem_nhds _ hε) hsub
  obtain ⟨D, hD⟩ := (Filter.eventually_atBot.mp (hbot.eventually_mem hmem))
  exact ⟨D, fun x hx => hD x (le_of_lt hx)⟩

/-! ## 5.19.2. Definíció: végtelen határérték a végtelenben -/

/-- **5.19.2. Definíció.** Az `f(x)`-nek a `-∞`-ben a határértéke `+∞`, ha bármely `M`
számhoz van olyan `D` szám, hogy `x < D` esetén `f(x) > M`. -/
def VegtelenHatarErtekMinuszVegtelenben (f : ℝ → ℝ) : Prop :=
  ∀ M : ℝ, ∃ D : ℝ, ∀ x : ℝ, x < D → M < f x

/-- **5.19.2. Definíció.** Az `f(x)`-nek a `+∞`-ben a határértéke `-∞`, ha bármely `M`
számhoz van olyan `D` szám, hogy `x > D` esetén `f(x) < M`. -/
def MinuszVegtelenHatarErtekVegtelenben (f : ℝ → ℝ) : Prop :=
  ∀ M : ℝ, ∃ D : ℝ, ∀ x : ℝ, D < x → f x < M

/-- **5.19.2. Definíció.** Az `f(x)`-nek a `-∞`-ben a határértéke `-∞`. -/
def MinuszVegtelenHatarErtekMinuszVegtelenben (f : ℝ → ℝ) : Prop :=
  ∀ M : ℝ, ∃ D : ℝ, ∀ x : ℝ, x < D → f x < M

/-- **5.19.2. Példa.** `lim_{x→-∞} x² = +∞`. -/
theorem x_negyzet_minusz_vegtelenben :
    VegtelenHatarErtekMinuszVegtelenben (fun x : ℝ => x ^ 2) := by
  intro M
  refine ⟨-(|M| + 1), fun x hx => ?_⟩
  have habs : 0 ≤ |M| := abs_nonneg M
  have ht : |M| + 1 < -x := by linarith
  have ht1 : (1 : ℝ) ≤ -x := by linarith
  show M < x ^ 2
  nlinarith [le_abs_self M, ht, ht1]

/-- **5.19.2. Példa.** `lim_{x→-∞} x³ = -∞`. -/
theorem x_kob_minusz_vegtelenben :
    MinuszVegtelenHatarErtekMinuszVegtelenben (fun x : ℝ => x ^ 3) := by
  intro M
  refine ⟨-(|M| + 1), fun x hx => ?_⟩
  have habs : 0 ≤ |M| := abs_nonneg M
  have ht : |M| + 1 < -x := by linarith
  have ht1 : (1 : ℝ) ≤ -x := by linarith
  show x ^ 3 < M
  have h1 : (0 : ℝ) ≤ (-x) * ((-x) - 1) * ((-x) + 1) :=
    mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  have h2 : x ^ 3 ≤ x := by nlinarith [h1]
  have h3 : x < M := by linarith [neg_abs_le M]
  linarith

/-- **5.19.2. Példa.** `lim_{x→+∞} (-x) = -∞`. -/
theorem minusz_x_vegtelenben : MinuszVegtelenHatarErtekVegtelenben (fun x : ℝ => -x) := by
  intro M
  exact ⟨-M, fun x hx => by simpa using neg_lt_neg hx⟩

end Leindler.Ch05
