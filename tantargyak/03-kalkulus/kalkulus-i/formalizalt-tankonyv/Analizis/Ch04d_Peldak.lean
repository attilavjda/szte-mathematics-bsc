import Mathlib
import Analizis.Ch04a_SorozatokAlapok
import Analizis.Ch04b_SorozatokMuveletek

/-!
# Leindler László: Analízis — 4.13. pont: Néhány példa és megoldási fogás

Ez a fájl a könyv **4.13. pontjának** feladatait formalizálja (a 4.13.1. feladat és a
4.13.6. feladat szorzatának zárt alakja a `Ch04b` modulban található):

* **4.13.2.** `√n(√(n+1) - √n) → 1/2` (típusa `∞·(∞ - ∞)`),
* **4.13.3.** `n(n+1)/(n²+1) → 1` (típusa `∞/∞`),
* **4.13.4.** `(1/n² + 1/n)/(2/n² + 3/n) → 1/3` (típusa `0/0`),
* **4.13.6.** `(1 - 1/2²)(1 - 1/3²)⋯(1 - 1/n²) → 1/2`,
* **4.13.7.** `(1 - 2/(2·3))(1 - 2/(3·4))⋯(1 - 2/(n(n+1))) → 1/3`,
* **4.13.8.** `(1² + 2² + ⋯ + n²)/n³ → 1/3`,
* **4.13.9.** `ⁿ√(n³ + 3n + 2) → 1` (a rendőrelv alkalmazásával),
* **4.13.10.** `((n+1)/(n-1))^(1/n²) → 1` (`n ≥ 2`, kétszeres rendőrelv).

A bizonyítások a könyv megoldási fogásait követik: gyöktelenítés, a számláló és a
nevező legmagasabb fokú taggal való osztása, a szorzat, illetve az összeg zárt
alakjának teljes indukcióval való igazolása, végül a rendőrelv.
-/

namespace Leindler.Ch04

open Filter Topology

/-- `1/n → 0` a Mathlib alakjában (a könyv 4.7.2. Tétele). -/
theorem tendsto_egy_per_n : Tendsto (fun n : ℕ => 1 / (n : ℝ)) atTop (𝓝 0) :=
  tendsto_one_div_atTop_nhds_zero_nat

/-! ## 4.13.2. Feladat -/

/-- **4.13.2. Feladat.** `√n(√(n+1) - √n) → 1/2`.  (Típusa `∞·(∞ - ∞)`.)

*Megoldás.* Gyöktelenítéssel
`√n(√(n+1) - √n) = √n/(√(n+1) + √n) = 1/(√(1 + 1/n) + 1) → 1/2`. -/
theorem feladat_4_13_2 :
    HatarErtek (fun n : ℕ => Real.sqrt n * (Real.sqrt ((n : ℝ) + 1) - Real.sqrt n)) (1 / 2) := by
  rw [hatarErtek_iff_tendsto]
  have key : ∀ n : ℕ, 1 ≤ n →
      Real.sqrt n * (Real.sqrt ((n : ℝ) + 1) - Real.sqrt n)
        = 1 / (Real.sqrt (1 + 1 / (n : ℝ)) + 1) := by
    intro n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    set s := Real.sqrt (n : ℝ) with hs
    set t := Real.sqrt ((n : ℝ) + 1) with ht
    have hs2 : s ^ 2 = (n : ℝ) := Real.sq_sqrt hnpos.le
    have ht2 : t ^ 2 = (n : ℝ) + 1 := Real.sq_sqrt (by linarith)
    have hspos : 0 < s := Real.sqrt_pos.mpr hnpos
    have htpos : 0 < t := Real.sqrt_pos.mpr (by linarith)
    have hsum : 0 < t + s := by linarith
    have h1 : s * (t - s) = s / (t + s) := by
      rw [eq_div_iff (ne_of_gt hsum)]
      nlinarith
    have h2 : Real.sqrt (1 + 1 / (n : ℝ)) = t / s := by
      rw [hs, ht, ← Real.sqrt_div (by linarith : (0 : ℝ) ≤ (n : ℝ) + 1)]
      congr 1
      field_simp
    rw [h1, h2, div_add' _ _ _ (ne_of_gt hspos), one_div, inv_div]
    field_simp
  have hEq : (fun n : ℕ => Real.sqrt n * (Real.sqrt ((n : ℝ) + 1) - Real.sqrt n))
      =ᶠ[atTop] fun n : ℕ => 1 / (Real.sqrt (1 + 1 / (n : ℝ)) + 1) :=
    eventually_atTop.2 ⟨1, key⟩
  refine Tendsto.congr' hEq.symm ?_
  have h0 : Tendsto (fun n : ℕ => 1 + 1 / (n : ℝ)) atTop (𝓝 1) := by
    have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).add
      tendsto_egy_per_n
    rwa [add_zero] at h
  have h1 : Tendsto (fun n : ℕ => Real.sqrt (1 + 1 / (n : ℝ))) atTop (𝓝 1) := by
    have h := (Real.continuous_sqrt.continuousAt (x := (1 : ℝ))).tendsto.comp h0
    rwa [Real.sqrt_one] at h
  have h2 : Tendsto (fun n : ℕ => Real.sqrt (1 + 1 / (n : ℝ)) + 1) atTop (𝓝 2) := by
    have h := h1.add (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1))
    rw [show (1 : ℝ) + 1 = 2 from by norm_num] at h
    simpa using h
  exact (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).div h2 two_ne_zero

/-! ## 4.13.3. Feladat -/

/-- **4.13.3. Feladat.** `n(n+1)/(n²+1) → 1`.  (Típusa `∞/∞`.)

*Megoldás.* A számlálót és a nevezőt `n²`-tel osztva
`n(n+1)/(n²+1) = (1 + 1/n)/(1 + 1/n²) → 1`. -/
theorem feladat_4_13_3 :
    HatarErtek (fun n : ℕ => (n : ℝ) * ((n : ℝ) + 1) / ((n : ℝ) ^ 2 + 1)) 1 := by
  rw [hatarErtek_iff_tendsto]
  have key : ∀ n : ℕ, 1 ≤ n →
      (n : ℝ) * ((n : ℝ) + 1) / ((n : ℝ) ^ 2 + 1)
        = (1 + 1 / (n : ℝ)) / (1 + 1 / (n : ℝ) ^ 2) := by
    intro n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    rw [div_eq_div_iff (by positivity) (by positivity)]
    field_simp
  have hEq : (fun n : ℕ => (n : ℝ) * ((n : ℝ) + 1) / ((n : ℝ) ^ 2 + 1))
      =ᶠ[atTop] fun n : ℕ => (1 + 1 / (n : ℝ)) / (1 + 1 / (n : ℝ) ^ 2) :=
    eventually_atTop.2 ⟨1, key⟩
  refine Tendsto.congr' hEq.symm ?_
  have h1 : Tendsto (fun n : ℕ => 1 + 1 / (n : ℝ)) atTop (𝓝 1) := by
    have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).add
      tendsto_egy_per_n
    rwa [add_zero] at h
  have h0 : Tendsto (fun n : ℕ => 1 / (n : ℝ) ^ 2) atTop (𝓝 0) := by
    have h := tendsto_egy_per_n.mul tendsto_egy_per_n
    simpa [div_mul_div_comm, sq] using h
  have h2 : Tendsto (fun n : ℕ => 1 + 1 / (n : ℝ) ^ 2) atTop (𝓝 1) := by
    have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)).add h0
    rwa [add_zero] at h
  have h := h1.div h2 one_ne_zero
  rwa [div_one] at h

/-! ## 4.13.6. Feladat -/

/-- **4.13.6. Feladat.** `(1 - 1/2²)(1 - 1/3²)⋯(1 - 1/n²) → 1/2`.

*Megoldás.* A `Ch04b`-ben teljes indukcióval igazolt zárt alak szerint a szorzat
`(n+1)/(2n) = 1/2 + (1/2)·(1/n)`, ami `1/2`-hez tart. -/
theorem feladat_4_13_6 :
    HatarErtek (fun n : ℕ => ∏ k ∈ Finset.Icc 2 n, (1 - 1 / (k : ℝ) ^ 2)) (1 / 2) := by
  rw [hatarErtek_iff_tendsto]
  have hEq : (fun n : ℕ => ∏ k ∈ Finset.Icc 2 n, (1 - 1 / (k : ℝ) ^ 2))
      =ᶠ[atTop] fun n : ℕ => 1 / 2 + 1 / 2 * (1 / (n : ℝ)) := by
    refine eventually_atTop.2 ⟨2, fun n hn => ?_⟩
    dsimp only
    have hnpos : (0 : ℝ) < n := by
      have : (2 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    rw [feladat_4_13_6_szorzat n hn]
    field_simp
  refine Tendsto.congr' hEq.symm ?_
  have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 / 2 : ℝ)) atTop (𝓝 (1 / 2))).add
    (tendsto_egy_per_n.const_mul (1 / 2 : ℝ))
  simpa using h

/-! ## 4.13.7. Feladat -/

/-- **4.13.7. Feladat (zárt alak).** `∏_{k=2}^{n} (1 - 2/(k(k+1))) = (n+2)/(3n)`
(`n ≥ 2`); a könyv szerint ezt először teljes indukcióval kell igazolni. -/
theorem feladat_4_13_7_szorzat (n : ℕ) (hn : 2 ≤ n) :
    ∏ k ∈ Finset.Icc 2 n, (1 - 2 / ((k : ℝ) * ((k : ℝ) + 1))) = ((n : ℝ) + 2) / (3 * n) := by
  induction n with
  | zero => omega
  | succ m ih =>
      rcases Nat.lt_or_ge m 2 with hm | hm
      · interval_cases m
        · omega
        · norm_num
      · rw [Finset.prod_Icc_succ_top (by omega), ih hm]
        have hm0 : (0 : ℝ) < m := by
          have : (2 : ℝ) ≤ m := by exact_mod_cast hm
          linarith
        push_cast
        field_simp
        ring

/-- **4.13.7. Feladat.** `(1 - 2/(2·3))(1 - 2/(3·4))⋯(1 - 2/(n(n+1))) → 1/3`. -/
theorem feladat_4_13_7 :
    HatarErtek (fun n : ℕ => ∏ k ∈ Finset.Icc 2 n, (1 - 2 / ((k : ℝ) * ((k : ℝ) + 1))))
      (1 / 3) := by
  rw [hatarErtek_iff_tendsto]
  have hEq : (fun n : ℕ => ∏ k ∈ Finset.Icc 2 n, (1 - 2 / ((k : ℝ) * ((k : ℝ) + 1))))
      =ᶠ[atTop] fun n : ℕ => 1 / 3 + 2 / 3 * (1 / (n : ℝ)) := by
    refine eventually_atTop.2 ⟨2, fun n hn => ?_⟩
    dsimp only
    have hnpos : (0 : ℝ) < n := by
      have : (2 : ℝ) ≤ n := by exact_mod_cast hn
      linarith
    rw [feladat_4_13_7_szorzat n hn]
    field_simp
  refine Tendsto.congr' hEq.symm ?_
  have h := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 / 3 : ℝ)) atTop (𝓝 (1 / 3))).add
    (tendsto_egy_per_n.const_mul (2 / 3 : ℝ))
  simpa using h

/-! ## 4.13.8. Feladat -/

/-- **4.13.8. Feladat (zárt alak).** `1² + 2² + ⋯ + n² = n(n+1)(2n+1)/6`. -/
theorem negyzetosszeg (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (k : ℝ) ^ 2 = (n : ℝ) * ((n : ℝ) + 1) * (2 * (n : ℝ) + 1) / 6 := by
  induction n with
  | zero => simp
  | succ m ih =>
      rw [Finset.sum_range_succ, ih]
      push_cast
      ring

/-- **4.13.8. Feladat.** `(1² + 2² + ⋯ + n²)/n³ → 1/3`.

*Megoldás.* A zárt alak szerint a sorozat `(n+1)(2n+1)/(6n²)`, ami `1/3`-hoz tart. -/
theorem feladat_4_13_8 :
    HatarErtek (fun n : ℕ => (∑ k ∈ Finset.range (n + 1), (k : ℝ) ^ 2) / (n : ℝ) ^ 3) (1 / 3) := by
  rw [hatarErtek_iff_tendsto]
  have hEq : (fun n : ℕ => (∑ k ∈ Finset.range (n + 1), (k : ℝ) ^ 2) / (n : ℝ) ^ 3)
      =ᶠ[atTop] fun n : ℕ =>
        1 / 3 + 1 / 2 * (1 / (n : ℝ)) + 1 / 6 * (1 / (n : ℝ)) * (1 / (n : ℝ)) := by
    refine eventually_atTop.2 ⟨1, fun n hn => ?_⟩
    dsimp only
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    rw [negyzetosszeg n]
    field_simp
    ring
  refine Tendsto.congr' hEq.symm ?_
  have h := ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 / 3 : ℝ)) atTop (𝓝 (1 / 3))).add
    (tendsto_egy_per_n.const_mul (1 / 2 : ℝ))).add
      ((tendsto_egy_per_n.const_mul (1 / 6 : ℝ)).mul tendsto_egy_per_n)
  simpa using h

/-! ## 4.13.4. Feladat -/

/-- **4.13.4. Feladat.** Mi a határértéke az `aₙ = (1/n² + 1/n)/(2/n² + 3/n)` általános
tagú sorozatnak?  (Típusa `0/0`, vagy `0·∞`.)

*Megoldás.* A törtet `n/n`-nel bővítve
`(1/n² + 1/n)/(2/n² + 3/n) = (1/n + 1)/(2/n + 3) → 1/3`. -/
theorem feladat_4_13_4 :
    HatarErtek
      (fun n : ℕ => (1 / (n : ℝ) ^ 2 + 1 / (n : ℝ)) / (2 / (n : ℝ) ^ 2 + 3 / (n : ℝ)))
      (1 / 3) := by
  rw [hatarErtek_iff_tendsto]
  have h1 : Tendsto (fun n : ℕ => 1 / (n : ℝ) + 1) atTop (𝓝 1) := by
    simpa using tendsto_egy_per_n.add (tendsto_const_nhds (x := (1 : ℝ)))
  have h2 : Tendsto (fun n : ℕ => 2 / (n : ℝ) + 3) atTop (𝓝 3) := by
    have h := (tendsto_egy_per_n.const_mul (2 : ℝ)).add (tendsto_const_nhds (x := (3 : ℝ)))
    simpa [mul_one_div] using h
  have h3 : Tendsto (fun n : ℕ => (1 / (n : ℝ) + 1) / (2 / (n : ℝ) + 3)) atTop (𝓝 (1 / 3)) :=
    h1.div h2 (by norm_num)
  refine h3.congr' (eventually_atTop.2 ⟨1, fun n hn => ?_⟩)
  have hn0 : (n : ℝ) ≠ 0 := by
    have : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
    exact ne_of_gt this
  field_simp

/-! ## 4.13.9. Feladat -/

/-- Segédazonosság: `ⁿ√(n³) = (ⁿ√n)³`. -/
theorem rpow_kob (n : ℕ) (hn : 1 ≤ n) :
    ((n : ℝ) ^ 3) ^ ((n : ℝ)⁻¹) = ((n : ℝ) ^ ((n : ℝ)⁻¹)) ^ 3 := by
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
  rw [← Real.rpow_natCast ((n : ℝ) ^ ((n : ℝ)⁻¹)) 3, ← Real.rpow_mul hnpos.le,
    ← Real.rpow_natCast (n : ℝ) 3, ← Real.rpow_mul hnpos.le, mul_comm]

/-- **4.13.9. Feladat.** `ⁿ√(n³ + 3n + 2) → 1`.

*Megoldás.* Itt a rendőrelvet alkalmazzuk:
`1 ≤ ⁿ√(n³ + 3n + 2) ≤ ⁿ√(6n³) = ⁿ√6 · (ⁿ√n)³ → 1`. -/
theorem feladat_4_13_9 :
    HatarErtek (fun n : ℕ => ((n : ℝ) ^ 3 + 3 * n + 2) ^ ((n : ℝ)⁻¹)) 1 := by
  rw [hatarErtek_iff_tendsto]
  have hinv : Tendsto (fun n : ℕ => ((n : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hsix : Tendsto (fun n : ℕ => (6 : ℝ) ^ ((n : ℝ)⁻¹)) atTop (𝓝 1) := by
    have h := (Real.continuousAt_const_rpow (b := (0 : ℝ)) (a := (6 : ℝ))
      (by norm_num)).tendsto.comp hinv
    simpa using h
  have hnroot : Tendsto (fun n : ℕ => (n : ℝ) ^ ((n : ℝ)⁻¹)) atTop (𝓝 1) := by
    have h := tendsto_rpow_div.comp tendsto_natCast_atTop_atTop
    simpa [Function.comp_def, one_div] using h
  have hupper : Tendsto (fun n : ℕ => (6 : ℝ) ^ ((n : ℝ)⁻¹) * ((n : ℝ) ^ ((n : ℝ)⁻¹)) ^ 3)
      atTop (𝓝 1) := by
    have h := hsix.mul (hnroot.pow 3)
    simpa using h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hupper
    (eventually_atTop.2 ⟨1, fun n hn => ?_⟩) (eventually_atTop.2 ⟨1, fun n hn => ?_⟩)
  · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hnpos : (0 : ℝ) < n := by linarith
    have hcube : (1 : ℝ) ≤ (n : ℝ) ^ 3 := one_le_pow₀ hn1
    have hbase : (1 : ℝ) ≤ (n : ℝ) ^ 3 + 3 * n + 2 := by linarith
    exact Real.one_le_rpow hbase (by positivity)
  · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hnpos : (0 : ℝ) < n := by linarith
    have hkob : (n : ℝ) ≤ (n : ℝ) ^ 3 := by
      have h := pow_le_pow_right₀ hn1 (by norm_num : 1 ≤ 3)
      simpa using h
    have hone : (1 : ℝ) ≤ (n : ℝ) ^ 3 := one_le_pow₀ hn1
    have hbase : (n : ℝ) ^ 3 + 3 * n + 2 ≤ 6 * (n : ℝ) ^ 3 := by linarith
    calc ((n : ℝ) ^ 3 + 3 * n + 2) ^ ((n : ℝ)⁻¹)
        ≤ (6 * (n : ℝ) ^ 3) ^ ((n : ℝ)⁻¹) :=
          Real.rpow_le_rpow (by positivity) hbase (by positivity)
      _ = (6 : ℝ) ^ ((n : ℝ)⁻¹) * ((n : ℝ) ^ ((n : ℝ)⁻¹)) ^ 3 := by
          rw [Real.mul_rpow (by norm_num) (by positivity), rpow_kob n hn]

/-! ## 4.13.10. Feladat -/

/-- **4.13.10. Feladat.** Mi a határértéke az `((n+1)/(n-1))^(1/n²)` (`n ≥ 2`) sorozatnak?

*Megoldás.* Itt kétszer egymást követően alkalmazzuk a rendőrelvet: `n ≥ 2` esetén
`1 ≤ (n+1)/(n-1) ≤ 3`, ezért
`1 = 1^(1/n²) ≤ ((n+1)/(n-1))^(1/n²) ≤ 3^(1/n²) ≤ 3^(1/n)`,
és a jobb oldal `1`-hez tart. -/
theorem feladat_4_13_10 :
    HatarErtek (fun n : ℕ => (((n : ℝ) + 1) / ((n : ℝ) - 1)) ^ (((n : ℝ) ^ 2)⁻¹)) 1 := by
  rw [hatarErtek_iff_tendsto]
  have hinv : Tendsto (fun n : ℕ => ((n : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hharom : Tendsto (fun n : ℕ => (3 : ℝ) ^ ((n : ℝ)⁻¹)) atTop (𝓝 1) := by
    have h := (Real.continuousAt_const_rpow (b := (0 : ℝ)) (a := (3 : ℝ))
      (by norm_num)).tendsto.comp hinv
    simpa using h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hharom
    (eventually_atTop.2 ⟨2, fun n hn => ?_⟩) (eventually_atTop.2 ⟨2, fun n hn => ?_⟩)
  · have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hnev : (0 : ℝ) < (n : ℝ) - 1 := by linarith
    have hbase : (1 : ℝ) ≤ ((n : ℝ) + 1) / ((n : ℝ) - 1) := by
      rw [le_div_iff₀ hnev]; linarith
    exact Real.one_le_rpow hbase (by positivity)
  · have hn2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
    have hnev : (0 : ℝ) < (n : ℝ) - 1 := by linarith
    have hbase3 : ((n : ℝ) + 1) / ((n : ℝ) - 1) ≤ 3 := by
      rw [div_le_iff₀ hnev]; linarith
    have hexp : ((n : ℝ) ^ 2)⁻¹ ≤ ((n : ℝ))⁻¹ :=
      inv_anti₀ (by linarith) (by nlinarith)
    calc (((n : ℝ) + 1) / ((n : ℝ) - 1)) ^ (((n : ℝ) ^ 2)⁻¹)
        ≤ (3 : ℝ) ^ (((n : ℝ) ^ 2)⁻¹) :=
          Real.rpow_le_rpow (by positivity) hbase3 (by positivity)
      _ ≤ (3 : ℝ) ^ ((n : ℝ)⁻¹) :=
          Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp

end Leindler.Ch04
