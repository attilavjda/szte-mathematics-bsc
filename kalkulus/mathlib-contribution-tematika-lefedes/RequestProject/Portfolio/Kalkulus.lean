/-
# Kalkulus I — validációs portfólió (feladat ↔ formalizált bizonyítás)

Ebben a fájlban a `kalkulus_gyakorlo.pdf` ("Feladatok Kalkulus 1. kurzushoz")
gyakorlatai szerepelnek Lean 4 tételként, **gépileg ellenőrzött** bizonyítással.
Minden tétel neve a feladat sorszámát viseli (`ex_1_11` = 1.11. gyakorlat), így a
kreditelismerési kérelemhez csatolt táblázat egy az egyben hivatkozható
(lásd `KREDITELISMERES.md`, `PORTFOLIO.md`).

Lefedett feladatsorok:
* 1. feladatsor (halmazok, egyenlőtlenségek, teljes indukció): 1.9, 1.11, 1.13,
  1.14 a)–c), 1.15 a), b), c), d);
* 2. feladatsor (függvények, injektivitás, kompozíció): 2.11, 2.18, 2.19;
* 3. feladatsor (határérték, folytonosság): 3.7 i), 3.14, 3.15, 3.16 c);
* 4. feladatsor (differenciálszámítás és alkalmazásai): 4.8/18., 4.10 e), 4.13.
-/
import Mathlib

namespace SZTE.Portfolio.Kalkulus

open Filter Topology Finset

/-! ## 1. feladatsor -/

/-- **1.9. gyakorlat.** `√2` irracionális. -/
theorem ex_1_9 : Irrational (Real.sqrt 2) := irrational_sqrt_two

/-- **1.11. gyakorlat.** Tetszőleges `x, y` valós számokra `||x| − |y|| ≤ |x − y|`
(fordított háromszög-egyenlőtlenség). -/
theorem ex_1_11 (x y : ℝ) : |(|x| - |y|)| ≤ |x - y| := abs_abs_sub_abs_le_abs_sub x y

/-- **1.13. gyakorlat (általánosított háromszög-egyenlőtlenség).**
`|a₁ + … + aₙ| ≤ |a₁| + … + |aₙ|`. -/
theorem ex_1_13 (n : ℕ) (a : ℕ → ℝ) :
    |∑ i ∈ range n, a i| ≤ ∑ i ∈ range n, |a i| :=
  Finset.abs_sum_le_sum_abs a (range n)

/-- **1.14. a) gyakorlat.** `1 + 2 + … + n = n(n+1)/2`. -/
theorem ex_1_14a (n : ℕ) : ∑ i ∈ range (n + 1), (i : ℝ) = n * (n + 1) / 2 := by
  induction n with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

/-- **1.14. b) gyakorlat.** `1³ + 2³ + … + n³ = (n(n+1)/2)²`. -/
theorem ex_1_14b (n : ℕ) : ∑ i ∈ range (n + 1), (i : ℝ) ^ 3 = (n * (n + 1) / 2) ^ 2 := by
  induction n with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ih]; push_cast; ring

/-- **1.14. c) gyakorlat.** Mértani sor részletösszege: `q ≠ 1` esetén
`1 + q + … + qⁿ = (qⁿ⁺¹ − 1)/(q − 1)`. -/
theorem ex_1_14c (q : ℝ) (hq : q ≠ 1) (n : ℕ) :
    ∑ i ∈ range (n + 1), q ^ i = (q ^ (n + 1) - 1) / (q - 1) :=
  geom_sum_eq hq (n + 1)

/-- **1.15. a) gyakorlat.** `∑_{i=1}^n i(3i+1) = n(n+1)²`. -/
theorem ex_1_15a (n : ℕ) : ∑ i ∈ Icc 1 n, i * (3 * i + 1) = n * (n + 1) ^ 2 := by
  induction n with
  | zero => simp
  | succ k ih => rw [Finset.sum_Icc_succ_top (by omega), ih]; ring

/-- **1.15. b) gyakorlat.** `∑_{i=1}^n i(i+1) = n(n+1)(n+2)/3` (egész alakban felírva). -/
theorem ex_1_15b (n : ℕ) : 3 * ∑ i ∈ Icc 1 n, i * (i + 1) = n * (n + 1) * (n + 2) := by
  induction n with
  | zero => simp
  | succ k ih => rw [Finset.sum_Icc_succ_top (by omega), Nat.mul_add, ih]; ring

/-- **1.15. c) gyakorlat (alsó becslés).** `2√(n+1) − 2 < ∑_{i=1}^n 1/√i`. -/
theorem ex_1_15c_lower (n : ℕ) (hn : 1 ≤ n) :
    2 * Real.sqrt (n + 1) - 2 < ∑ i ∈ Icc 1 n, 1 / Real.sqrt i := by
  induction n, hn using Nat.le_induction with
  | base =>
      norm_num
      nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2]
  | succ k hk ih =>
      rw [Finset.sum_Icc_succ_top (by omega)]
      set t := Real.sqrt ((k : ℝ) + 1) with htdef
      set u := Real.sqrt ((k : ℝ) + 2) with hudef
      have ht : 0 < t := Real.sqrt_pos.mpr (by positivity)
      have ht2 : t ^ 2 = (k : ℝ) + 1 := Real.sq_sqrt (by positivity)
      have hu2 : u ^ 2 = (k : ℝ) + 2 := Real.sq_sqrt (by positivity)
      have h : 2 * t * u ≤ 2 * t ^ 2 + 1 := by nlinarith [sq_nonneg (u - t)]
      have key : 2 * u ≤ 2 * t + 1 / t := by
        rw [← sub_nonneg]
        have heq : 2 * t + 1 / t - 2 * u = (2 * t ^ 2 + 1 - 2 * t * u) / t := by field_simp
        rw [heq]
        exact div_nonneg (by linarith) ht.le
      push_cast
      rw [show ((k : ℝ) + 1 + 1) = (k : ℝ) + 2 by ring, ← hudef, ← htdef]
      linarith [ih]

/-- **1.15. c) gyakorlat (felső becslés).** `∑_{i=1}^n 1/√i < 2√n − 1`, ha `n ≥ 2`.
(`n = 1`-re a jobb oldal éppen `1`, tehát ott csak `≤` igaz; a példatár állítása
`n ≥ 2` esetén szigorú.) -/
theorem ex_1_15c_upper (n : ℕ) (hn : 2 ≤ n) :
    ∑ i ∈ Icc 1 n, 1 / Real.sqrt i < 2 * Real.sqrt n - 1 := by
  induction n, hn using Nat.le_induction with
  | base =>
      rw [show (Icc 1 2) = {1, 2} by decide]
      norm_num
      have hpos : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
      have h2 : Real.sqrt 2 * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
      have hinv : (Real.sqrt 2)⁻¹ = Real.sqrt 2 / 2 := by
        rw [eq_div_iff (by norm_num), inv_mul_eq_div, div_eq_iff (ne_of_gt hpos)]
        linarith [h2]
      rw [hinv]
      nlinarith [h2, hpos]
  | succ k hk ih =>
      rw [Finset.sum_Icc_succ_top (by omega)]
      set s := Real.sqrt (k : ℝ) with hsdef
      set t := Real.sqrt ((k : ℝ) + 1) with htdef
      have hk0 : (0 : ℝ) < k := by positivity
      have hs : 0 < s := Real.sqrt_pos.mpr hk0
      have ht : 0 < t := Real.sqrt_pos.mpr (by positivity)
      have hs2 : s ^ 2 = (k : ℝ) := Real.sq_sqrt (by positivity)
      have ht2 : t ^ 2 = (k : ℝ) + 1 := Real.sq_sqrt (by positivity)
      have key : 1 / t ≤ 2 * t - 2 * s := by
        rw [← sub_nonneg]
        have heq : 2 * t - 2 * s - 1 / t = (2 * t ^ 2 - 2 * s * t - 1) / t := by field_simp
        rw [heq]
        have h : 2 * s * t ≤ s ^ 2 + t ^ 2 := by nlinarith [sq_nonneg (t - s)]
        exact div_nonneg (by nlinarith) ht.le
      push_cast
      rw [← htdef]
      linarith [ih]

/-- Segédállítás (Bernoulli-egyenlőtlenség következménye): `2 ≤ (1 + 1/m)^m`. -/
theorem bernoulli_two_le (m : ℕ) (hm : 1 ≤ m) : (2 : ℝ) ≤ (1 + 1 / (m : ℝ)) ^ m := by
  have hm0 : (0 : ℝ) < m := by exact_mod_cast hm
  have h0 : (0 : ℝ) ≤ 1 / (m : ℝ) := by positivity
  have h := one_add_mul_le_pow (a := 1 / (m : ℝ)) (by linarith) m
  have hmm : (m : ℝ) * (1 / (m : ℝ)) = 1 := by field_simp
  rw [hmm] at h
  linarith

/-- **1.15. d) gyakorlat.** `n! < ((n+1)/2)ⁿ`, ha `n ≥ 2`.
(`n = 1`-re a két oldal egyenlő, ezért ott csak `≤` áll fenn.) -/
theorem ex_1_15d (n : ℕ) (hn : 2 ≤ n) : (Nat.factorial n : ℝ) < ((n + 1) / 2) ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num [Nat.factorial]
  | succ k hk ih =>
      have hk0 : (0 : ℝ) < k := by positivity
      have hpos : (0 : ℝ) < (k : ℝ) + 1 := by linarith
      have h1 : (Nat.factorial (k + 1) : ℝ) = ((k : ℝ) + 1) * Nat.factorial k := by
        push_cast [Nat.factorial_succ]; ring
      have h2 : (Nat.factorial (k + 1) : ℝ) < ((k : ℝ) + 1) * (((k : ℝ) + 1) / 2) ^ k := by
        rw [h1]; exact mul_lt_mul_of_pos_left ih hpos
      have hb := bernoulli_two_le (k + 1) (by omega)
      push_cast at hb
      rw [show (1 + 1 / ((k : ℝ) + 1)) = ((k : ℝ) + 2) / ((k : ℝ) + 1) by field_simp; ring] at hb
      have hsplit : (((k : ℝ) + 2) / 2) ^ (k + 1)
          = (((k : ℝ) + 2) / ((k : ℝ) + 1)) ^ (k + 1) * (((k : ℝ) + 1) / 2) ^ (k + 1) := by
        rw [← mul_pow]; congr 1; field_simp
      have hp : (0 : ℝ) < (((k : ℝ) + 1) / 2) ^ (k + 1) := by positivity
      have hkey : ((k : ℝ) + 1) * (((k : ℝ) + 1) / 2) ^ k ≤ (((k : ℝ) + 2) / 2) ^ (k + 1) := by
        rw [hsplit]
        calc ((k : ℝ) + 1) * (((k : ℝ) + 1) / 2) ^ k = 2 * (((k : ℝ) + 1) / 2) ^ (k + 1) := by ring
          _ ≤ (((k : ℝ) + 2) / ((k : ℝ) + 1)) ^ (k + 1) * (((k : ℝ) + 1) / 2) ^ (k + 1) :=
              mul_le_mul_of_nonneg_right hb hp.le
      push_cast
      rw [show ((k : ℝ) + 1 + 1) / 2 = ((k : ℝ) + 2) / 2 by ring]
      push_cast at h2
      linarith

/-! ## 2. feladatsor -/

/-- **2.11. gyakorlat.** Az `f(x) = 2x² − 1` és `g(x) = 4x³ − 3x` függvények
felcserélhetők: `f ∘ g = g ∘ f` (a Csebisev-polinomok `T₂ ∘ T₃ = T₃ ∘ T₂` azonossága). -/
theorem ex_2_11 : (fun x : ℝ => 2 * x ^ 2 - 1) ∘ (fun x : ℝ => 4 * x ^ 3 - 3 * x) =
    (fun x : ℝ => 4 * x ^ 3 - 3 * x) ∘ (fun x : ℝ => 2 * x ^ 2 - 1) := by
  funext x
  simp only [Function.comp_apply]
  ring

/-- **2.18. gyakorlat.** Injektív függvények kompozíciója injektív. -/
theorem ex_2_18 {f g : ℝ → ℝ} (hf : Function.Injective f) (hg : Function.Injective g) :
    Function.Injective (f ∘ g) := hf.comp hg

/-- **2.19. gyakorlat.** Egy nem azonosan nulla, valós együtthatós, `n`-edfokú
polinomnak legfeljebb `n` gyöke van. -/
theorem ex_2_19 (p : Polynomial ℝ) : p.roots.toFinset.card ≤ p.natDegree :=
  le_trans (Multiset.toFinset_card_le _) (Polynomial.card_roots' p)

/-! ## 3. feladatsor -/

/-- **3.7. i) gyakorlat.** `lim_{x→0} (1 − cos x)/x² = 1/2`. -/
theorem ex_3_7i :
    Tendsto (fun x : ℝ => (1 - Real.cos x) / x ^ 2) (𝓝[≠] 0) (𝓝 (1 / 2)) := by
  have step2 : Tendsto (fun x : ℝ => Real.sin x / (2 * x)) (𝓝[≠] 0) (𝓝 (1 / 2)) := by
    apply HasDerivAt.lhopital_zero_nhdsNE (f' := fun x => Real.cos x) (g' := fun _ => (2 : ℝ))
    · filter_upwards with x using Real.hasDerivAt_sin x
    · filter_upwards with x using ((hasDerivAt_id x).const_mul 2).congr_deriv (by ring)
    · filter_upwards with x using two_ne_zero
    · simpa using (Real.continuous_sin.tendsto 0).mono_left nhdsWithin_le_nhds
    · exact ((continuous_const.mul continuous_id).tendsto' 0 0 (by simp)).mono_left
        nhdsWithin_le_nhds
    · have := (Real.continuous_cos.tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := {(0 : ℝ)}ᶜ))
      simpa using this.div_const 2
  apply HasDerivAt.lhopital_zero_nhdsNE (f' := fun x => Real.sin x) (g' := fun x => 2 * x)
  · filter_upwards with x using ((Real.hasDerivAt_cos x).const_sub 1).congr_deriv (by ring)
  · filter_upwards with x using (hasDerivAt_pow 2 x).congr_deriv (by push_cast; ring)
  · filter_upwards [self_mem_nhdsWithin] with x hx using by simpa using hx
  · exact ((continuous_const.sub Real.continuous_cos).tendsto' 0 0 (by simp)).mono_left
      nhdsWithin_le_nhds
  · exact ((continuous_pow 2).tendsto' 0 0 (by simp)).mono_left nhdsWithin_le_nhds
  · exact step2

/-- **3.14. gyakorlat.** Ha `f` az `(a,b)` nyílt intervallumon monoton növő és
felülről korlátos, akkor létezik (véges) bal oldali határértéke `b`-ben. -/
theorem ex_3_14 {a b : ℝ} (hab : a < b) {f : ℝ → ℝ}
    (hmono : MonotoneOn f (Set.Ioo a b)) (hbdd : BddAbove (f '' Set.Ioo a b)) :
    ∃ L : ℝ, Tendsto f (𝓝[Set.Ioo a b] b) (𝓝 L) := by
  have hne : (f '' Set.Ioo a b).Nonempty :=
    ⟨f ((a + b) / 2), ⟨(a + b) / 2, by constructor <;> linarith, rfl⟩⟩
  refine ⟨sSup (f '' Set.Ioo a b), ?_⟩
  set L := sSup (f '' Set.Ioo a b) with hL
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  obtain ⟨y, hy, hyL⟩ : ∃ y ∈ Set.Ioo a b, L - ε < f y := by
    by_contra hcon
    push_neg at hcon
    have : L ≤ L - ε := csSup_le hne (by rintro _ ⟨z, hz, rfl⟩; exact hcon z hz)
    linarith
  refine ⟨b - y, by simp only [Set.mem_Ioo] at hy ⊢; linarith [hy.2], ?_⟩
  intro x hx hdist
  have hxy : y < x := by
    rw [Real.dist_eq, abs_lt] at hdist
    linarith [hdist.1]
  have h1 : f y ≤ f x := hmono hy hx hxy.le
  have h2 : f x ≤ L := le_csSup hbdd ⟨x, hx, rfl⟩
  rw [Real.dist_eq, abs_lt]
  constructor <;> linarith

/-- **3.15. gyakorlat.** Ha két folytonos valós függvény minden racionális helyen
megegyezik, akkor mindenütt megegyezik. -/
theorem ex_3_15 {f g : ℝ → ℝ} (hf : Continuous f) (hg : Continuous g)
    (h : ∀ q : ℚ, f q = g q) : f = g :=
  Continuous.ext_on Rat.denseRange_cast hf hg (by rintro _ ⟨q, rfl⟩; exact h q)

/-- **3.16. c) gyakorlat.** `(1 + 1/n)ⁿ < 4` minden `n ≥ 1` esetén. -/
theorem ex_3_16c (n : ℕ) (hn : 1 ≤ n) : (1 + 1 / (n : ℝ)) ^ n < 4 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have h1 : (1 : ℝ) + 1 / n ≤ Real.exp (1 / n) := by
    have := Real.add_one_le_exp (1 / (n : ℝ)); linarith
  have h2 : (1 + 1 / (n : ℝ)) ^ n ≤ Real.exp (1 / n) ^ n :=
    pow_le_pow_left₀ (by positivity) h1 n
  have h3 : Real.exp (1 / (n : ℝ)) ^ n = Real.exp 1 := by
    rw [← Real.exp_nat_mul]; congr 1; field_simp
  have h4 : Real.exp 1 < 4 := by have := Real.exp_one_lt_d9; linarith
  rw [h3] at h2
  linarith

/-! ## 4. feladatsor -/

/-- **4.8/18. feladat (teljes függvényvizsgálat).** Az `f(x) = x·eˣ` függvény
abszolút minimumhelye `x = −1`, a minimum értéke `−1/e`. -/
theorem ex_4_8_18 (x : ℝ) : -Real.exp (-1) ≤ x * Real.exp x := by
  have h := Real.add_one_le_exp (-1 - x)
  have hx : 0 < Real.exp x := Real.exp_pos x
  have hmul : Real.exp (-1 - x) * Real.exp x = Real.exp (-1) := by
    rw [← Real.exp_add]; ring_nf
  nlinarith [h, hx, hmul]

/-- **4.10. e) gyakorlat (L'Hospital-szabály).** `lim_{x→0} (eˣ − (1+x))/x² = 1/2`. -/
theorem ex_4_10e :
    Tendsto (fun x : ℝ => (Real.exp x - (1 + x)) / x ^ 2) (𝓝[≠] 0) (𝓝 (1 / 2)) := by
  have step2 : Tendsto (fun x : ℝ => (Real.exp x - 1) / (2 * x)) (𝓝[≠] 0) (𝓝 (1 / 2)) := by
    apply HasDerivAt.lhopital_zero_nhdsNE (f' := fun x => Real.exp x) (g' := fun _ => (2 : ℝ))
    · filter_upwards with x using (Real.hasDerivAt_exp x).sub_const 1
    · filter_upwards with x using ((hasDerivAt_id x).const_mul 2).congr_deriv (by ring)
    · filter_upwards with x using two_ne_zero
    · exact ((Real.continuous_exp.sub continuous_const).tendsto' 0 0 (by simp)).mono_left
        nhdsWithin_le_nhds
    · exact ((continuous_const.mul continuous_id).tendsto' 0 0 (by simp)).mono_left
        nhdsWithin_le_nhds
    · have := (Real.continuous_exp.tendsto (0 : ℝ)).mono_left (nhdsWithin_le_nhds (s := {(0 : ℝ)}ᶜ))
      simpa using this.div_const 2
  apply HasDerivAt.lhopital_zero_nhdsNE (f' := fun x => Real.exp x - 1) (g' := fun x => 2 * x)
  · filter_upwards with x using
      ((Real.hasDerivAt_exp x).sub ((hasDerivAt_id x).const_add 1)).congr_deriv (by simp)
  · filter_upwards with x using (hasDerivAt_pow 2 x).congr_deriv (by push_cast; ring)
  · filter_upwards [self_mem_nhdsWithin] with x hx using by simpa using hx
  · exact ((Real.continuous_exp.sub (continuous_const.add continuous_id)).tendsto' 0 0
      (by simp)).mono_left nhdsWithin_le_nhds
  · exact ((continuous_pow 2).tendsto' 0 0 (by simp)).mono_left nhdsWithin_le_nhds
  · exact step2

/-- **4.13. gyakorlat.** *Középponti konvexitás + folytonosság ⇒ konvexitás.*
Ha `f` folytonos az `(a,b)` intervallumon, és bármely `x₁, x₂ ∈ (a,b)` esetén
`f((x₁+x₂)/2) ≤ (f(x₁)+f(x₂))/2`, akkor `f` konvex `(a,b)`-n. -/
theorem ex_4_13 {a b : ℝ} {f : ℝ → ℝ} (hcont : ContinuousOn f (Set.Ioo a b))
    (hmid : ∀ x ∈ Set.Ioo a b, ∀ y ∈ Set.Ioo a b, f ((x + y) / 2) ≤ (f x + f y) / 2) :
    ConvexOn ℝ (Set.Ioo a b) f := by
  refine ⟨convex_Ioo a b, ?_⟩
  intro x hx y hy p q hp hq hpq
  set γ : ℝ → ℝ := fun t => (1 - t) * x + t * y with hγdef
  have hγmem : ∀ t ∈ Set.Icc (0:ℝ) 1, γ t ∈ Set.Ioo a b := by
    intro t ht
    have := (convex_Ioo a b) hx hy (by linarith [ht.2] : (0:ℝ) ≤ 1 - t) ht.1 (by ring)
    simpa [hγdef, smul_eq_mul] using this
  set H : ℝ → ℝ := fun t => (1 - t) * f x + t * f y - f (γ t) with hHdef
  have hcontH : ContinuousOn H (Set.Icc 0 1) := by
    apply ContinuousOn.sub
    · fun_prop
    · exact hcont.comp (by fun_prop) hγmem
  have hsuper : ∀ s ∈ Set.Icc (0:ℝ) 1, ∀ t ∈ Set.Icc (0:ℝ) 1,
      (H s + H t) / 2 ≤ H ((s + t) / 2) := by
    intro s hs t ht
    have hkey := hmid (γ s) (hγmem s hs) (γ t) (hγmem t ht)
    have hg : γ ((s + t) / 2) = (γ s + γ t) / 2 := by simp only [hγdef]; ring
    have haff : (1 - (s + t) / 2) * f x + ((s + t) / 2) * f y
        = ((1 - s) * f x + s * f y + ((1 - t) * f x + t * f y)) / 2 := by ring
    simp only [hHdef, hg]
    linarith
  have hH0 : H 0 = 0 := by simp [hHdef, hγdef]
  have hH1 : H 1 = 0 := by simp [hHdef, hγdef]
  have main : ∀ t ∈ Set.Icc (0:ℝ) 1, 0 ≤ H t := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨t₀, ht₀mem, ht₀⟩ := hcon
    obtain ⟨c, hc, hmin⟩ :=
      isCompact_Icc.exists_isMinOn (Set.nonempty_Icc.2 zero_le_one) hcontH
    set m := H c with hmdef
    have hm : m < 0 := lt_of_le_of_lt (hmin ht₀mem) ht₀
    set T := Set.Icc (0:ℝ) 1 ∩ H ⁻¹' (Set.Iic m) with hTdef
    have hTclosed : IsClosed T :=
      hcontH.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
    have hTne : T.Nonempty := ⟨c, hc, le_refl m⟩
    have hTbdd : BddBelow T := ⟨0, fun z hz => hz.1.1⟩
    have hdT : sInf T ∈ T := hTclosed.csInf_mem hTne hTbdd
    set d := sInf T with hddef
    have hdmem : d ∈ Set.Icc (0:ℝ) 1 := hdT.1
    have hdle : H d ≤ m := hdT.2
    have hdge : m ≤ H d := hmin hdmem
    have hd0 : d ≠ 0 := by intro hd; rw [hd, hH0] at hdle; linarith
    have hd1 : d ≠ 1 := by intro hd; rw [hd, hH1] at hdle; linarith
    have hd0' : 0 < d := lt_of_le_of_ne hdmem.1 (Ne.symm hd0)
    have hd1' : d < 1 := lt_of_le_of_ne hdmem.2 hd1
    set ε := min d (1 - d) with hεdef
    have hε : 0 < ε := lt_min hd0' (by linarith)
    have hεd : ε ≤ d := min_le_left _ _
    have hε1 : ε ≤ 1 - d := min_le_right _ _
    have hm1 : d - ε ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith, by linarith⟩
    have hm2 : d + ε ∈ Set.Icc (0:ℝ) 1 := ⟨by linarith, by linarith⟩
    have hmid' := hsuper (d - ε) hm1 (d + ε) hm2
    have heq : (d - ε + (d + ε)) / 2 = d := by ring
    rw [heq] at hmid'
    have hge2 : m ≤ H (d + ε) := hmin hm2
    have : H (d - ε) ≤ m := by linarith
    have hin : (d - ε) ∈ T := ⟨hm1, this⟩
    have := csInf_le hTbdd hin
    linarith
  have hq1 : p = 1 - q := by linarith
  have := main q ⟨hq, by linarith⟩
  simp only [hHdef, hγdef] at this
  simp only [smul_eq_mul, hq1]
  linarith


end SZTE.Portfolio.Kalkulus
