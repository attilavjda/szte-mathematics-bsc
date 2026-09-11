/-
# 1. feladatsor — Ismétlés: halmazok, számhalmazok, algebrai azonosságok,
#    egyenletek, egyenlőtlenségek, teljes indukció

A `kalkulus_gyakorlo.pdf` 1. feladatsorának formalizálása.
Minden tétel neve a feladat sorszámát követi (`gyak_1_11` = 1.11. gyakorlat).
-/
import Mathlib

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace Kalkulus1.Szakasz1

open Finset Filter

/-! ## 1.3. gyakorlat — számhalmazok leírása formulákkal -/

/-- 1.3 a) A negatív valós számok halmaza. -/
def negativValosak : Set ℝ := {x : ℝ | x < 0}

/-- 1.3 b) A páros pozitív egészek halmaza. -/
def parosPozitivEgeszek : Set ℤ := {n : ℤ | 0 < n ∧ Even n}

/-- 1.3 c) A kettőnél nagyobb racionális számok halmaza. -/
def kettonelNagyobbRacionalisok : Set ℚ := {q : ℚ | 2 < q}

/-- 1.3 d) A kettőnél nagyobb valós számok halmaza. -/
def kettonelNagyobbValosak : Set ℝ := {x : ℝ | 2 < x}

/-- 1.3 e) A kilenccel osztható pozitív egészek halmaza. -/
def kilenccelOszthatoPozitivEgeszek : Set ℤ := {n : ℤ | 0 < n ∧ (9 : ℤ) ∣ n}

/-- 1.3 b) A megadott halmaz pontosan a `2k` alakú számokból áll, `k` pozitív egész. -/
theorem gyak_1_3_b (n : ℤ) : n ∈ parosPozitivEgeszek ↔ ∃ k : ℤ, 0 < k ∧ n = 2 * k := by
  constructor
  · rintro ⟨hpos, k, rfl⟩
    exact ⟨k, by omega, by ring⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨by omega, ⟨k, by ring⟩⟩

/-- 1.3 e) A megadott halmaz pontosan a `9k` alakú számokból áll, `k` pozitív egész. -/
theorem gyak_1_3_e (n : ℤ) :
    n ∈ kilenccelOszthatoPozitivEgeszek ↔ ∃ k : ℤ, 0 < k ∧ n = 9 * k := by
  constructor
  · rintro ⟨hpos, k, rfl⟩
    exact ⟨k, by omega, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨by omega, ⟨k, rfl⟩⟩

/-- 1.3 a) és d) — a két halmaz diszjunkt, és egyikük sem üres. -/
theorem gyak_1_3_ad : negativValosak ∩ kettonelNagyobbValosak = ∅ := by
  ext x
  simp only [Set.mem_inter_iff, negativValosak, kettonelNagyobbValosak, Set.mem_setOf_eq,
    Set.mem_empty_iff_false, iff_false, not_and, not_lt]
  intro hx
  linarith

/-! ## 1.4. gyakorlat — korlátosság, alsó és felső határ -/

/-- 1.4 a) A néggyel osztható pozitív egészek halmazának legkisebb eleme `4`. -/
theorem gyak_1_4_a_isLeast :
    IsLeast {n : ℤ | 0 < n ∧ (4 : ℤ) ∣ n} 4 := by
  constructor
  · exact ⟨by norm_num, ⟨1, by ring⟩⟩
  · rintro n ⟨hn, k, rfl⟩
    have : 0 < k := by omega
    omega

/-- 1.4 a) A néggyel osztható pozitív egészek halmaza felülről nem korlátos. -/
theorem gyak_1_4_a_not_bddAbove :
    ¬ BddAbove {n : ℤ | 0 < n ∧ (4 : ℤ) ∣ n} := by
  rintro ⟨M, hM⟩
  have h : (4 : ℤ) * (max M 1) ∈ {n : ℤ | 0 < n ∧ (4 : ℤ) ∣ n} := by
    refine ⟨by positivity, ⟨max M 1, rfl⟩⟩
  have := hM h
  have h1 : (1 : ℤ) ≤ max M 1 := le_max_right _ _
  have h2 : M ≤ max M 1 := le_max_left _ _
  omega

/-- 1.4 b) A `(-1,1]` intervallum felső határa `1` (és az elem is: maximum). -/
theorem gyak_1_4_b_isLUB : IsLUB (Set.Ioc (-1 : ℝ) 1) 1 := isLUB_Ioc (by norm_num)

/-- 1.4 b) A `(-1,1]` intervallum alsó határa `-1`, de nem eleme: nincs minimuma. -/
theorem gyak_1_4_b_isGLB : IsGLB (Set.Ioc (-1 : ℝ) 1) (-1) := isGLB_Ioc (by norm_num)

/-- 1.4 c) Az `{1/n | n ∈ ℤ⁺}` halmaz felső határa `1`. -/
theorem gyak_1_4_c_isLUB :
    IsLUB {x : ℝ | ∃ n : ℕ, 0 < n ∧ x = 1 / n} 1 := by
  constructor
  · rintro x ⟨n, hn, rfl⟩
    rw [div_le_one (by exact_mod_cast hn)]
    exact_mod_cast hn
  · intro b hb
    have : (1 : ℝ) ∈ {x : ℝ | ∃ n : ℕ, 0 < n ∧ x = 1 / n} := ⟨1, by norm_num⟩
    simpa using hb this

/-- 1.4 c) Az `{1/n | n ∈ ℤ⁺}` halmaz alsó határa `0`, ami nem eleme a halmaznak. -/
theorem gyak_1_4_c_isGLB :
    IsGLB {x : ℝ | ∃ n : ℕ, 0 < n ∧ x = 1 / n} 0 := by
  constructor
  · rintro x ⟨n, hn, rfl⟩
    positivity
  · intro b hb
    by_contra hlt
    push_neg at hlt
    obtain ⟨n, hn⟩ := exists_nat_one_div_lt hlt
    have hpos : 0 < n + 1 := Nat.succ_pos n
    have hmem : (1 : ℝ) / (n + 1 : ℕ) ∈ {x : ℝ | ∃ n : ℕ, 0 < n ∧ x = 1 / n} :=
      ⟨n + 1, hpos, by push_cast; ring⟩
    have := hb hmem
    push_cast at this hn
    linarith

/-! ## 1.5. gyakorlat — a felső határ egyértelműsége -/

/-- 1.5 Egy számhalmaznak legfeljebb egy felső határa van. -/
theorem gyak_1_5 {S : Set ℝ} {a b : ℝ} (ha : IsLUB S a) (hb : IsLUB S b) : a = b :=
  ha.unique hb

/-! ## 1.6. gyakorlat — a szélesszájú kisbéka (mértani sor) -/

/-- 1.6 A béka `n` ugrás után az `1 - 2⁻ⁿ` pontban van. -/
theorem gyak_1_6_reszletosszeg (n : ℕ) :
    ∑ i ∈ Finset.range n, (1 / 2 : ℝ) ^ (i + 1) = 1 - (1 / 2 : ℝ) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    ring

/-- 1.6 A béka soha nem éri el az `1` pontot: minden véges lépés után `< 1`. -/
theorem gyak_1_6_soha_nem_er_oda (n : ℕ) :
    ∑ i ∈ Finset.range n, (1 / 2 : ℝ) ^ (i + 1) < 1 := by
  rw [gyak_1_6_reszletosszeg]
  have : (0 : ℝ) < (1 / 2 : ℝ) ^ n := by positivity
  linarith

/-- 1.6 De tetszőlegesen közel kerül hozzá: a részletösszegek `1`-hez tartanak. -/
theorem gyak_1_6_hatarertek :
    Tendsto (fun n : ℕ => ∑ i ∈ Finset.range n, (1 / 2 : ℝ) ^ (i + 1)) atTop (nhds 1) := by
  simp only [gyak_1_6_reszletosszeg]
  have h : Tendsto (fun n : ℕ => (1 / 2 : ℝ) ^ n) atTop (nhds 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)
  simpa using (tendsto_const_nhds (x := (1 : ℝ)) (f := atTop (α := ℕ))).sub h

/-! ## 1.9. gyakorlat — a gyök kettő irracionális -/

/-- 1.9 `√2` irracionális. -/
theorem gyak_1_9 : Irrational (Real.sqrt 2) := irrational_sqrt_two

/-- 1.9 Ugyanez elemi alakban: nincs olyan `p/q` tört, amelynek négyzete `2`. -/
theorem gyak_1_9' : ¬ ∃ q : ℚ, (q : ℝ) ^ 2 = 2 := by
  rintro ⟨q, hq⟩
  refine irrational_sqrt_two ⟨|q|, ?_⟩
  rw [← hq, Real.sqrt_sq_eq_abs, Rat.cast_abs]

/-! ## 1.11. gyakorlat — fordított háromszög-egyenlőtlenség -/

/-- 1.11 `||x| - |y|| ≤ |x - y|`. -/
theorem gyak_1_11 (x y : ℝ) : |(|x| - |y|)| ≤ |x - y| := abs_abs_sub_abs_le_abs_sub x y

/-! ## 1.12. gyakorlat — egyenlőtlenségek megoldása -/

/-- 1.12 a) `|x+2| > 4 ↔ x > 2 ∨ x < -6`. -/
theorem gyak_1_12_a (x : ℝ) : |x + 2| > 4 ↔ 2 < x ∨ x < -6 := by
  rw [gt_iff_lt, lt_abs]
  constructor
  · rintro (h | h) <;> [left; right] <;> linarith
  · rintro (h | h) <;> [left; right] <;> linarith

/-- 1.12 d) `(x+2)/(x-4) < 2 ↔ x < 4 ∨ x > 10` (az `x = 4` hely kizárva). -/
theorem gyak_1_12_d (x : ℝ) (hx : x ≠ 4) : (x + 2) / (x - 4) < 2 ↔ x < 4 ∨ 10 < x := by
  rcases lt_trichotomy x 4 with h | h | h
  · have hneg : x - 4 < 0 := by linarith
    rw [div_lt_iff_of_neg hneg]
    constructor
    · intro _; exact Or.inl h
    · intro _; linarith
  · exact absurd h hx
  · have hpos : 0 < x - 4 := by linarith
    rw [div_lt_iff₀ hpos]
    constructor
    · intro hlt; exact Or.inr (by linarith)
    · rintro (h' | h')
      · linarith
      · linarith

/-- 1.12 i) `|x - 5| ≤ ε ↔ x ∈ [5-ε, 5+ε]`. -/
theorem gyak_1_12_i (x eps : ℝ) : |x - 5| ≤ eps ↔ x ∈ Set.Icc (5 - eps) (5 + eps) := by
  rw [abs_le, Set.mem_Icc]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩; exact ⟨by linarith, by linarith⟩

/-! ## 1.13. gyakorlat — általánosított háromszög-egyenlőtlenség -/

/-- 1.13 `|a₁ + ... + aₙ| ≤ |a₁| + ... + |aₙ|`. -/
theorem gyak_1_13 (n : ℕ) (a : ℕ → ℝ) :
    |∑ i ∈ Finset.range n, a i| ≤ ∑ i ∈ Finset.range n, |a i| :=
  Finset.abs_sum_le_sum_abs a _

/-- 1.13 Indukciós bizonyítás „kézzel”: a lépés a kéttagú háromszög-egyenlőtlenség. -/
theorem gyak_1_13_indukcioval (n : ℕ) (a : ℕ → ℝ) :
    |∑ i ∈ Finset.range n, a i| ≤ ∑ i ∈ Finset.range n, |a i| := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    calc |∑ i ∈ Finset.range n, a i + a n|
        ≤ |∑ i ∈ Finset.range n, a i| + |a n| := abs_add_le _ _
      _ ≤ (∑ i ∈ Finset.range n, |a i|) + |a n| := by linarith

/-! ## 1.14. gyakorlat — nevezetes azonosságok teljes indukcióval -/

/-- 1.14 a) `1 + 2 + ... + n = n(n+1)/2`. -/
theorem gyak_1_14_a (n : ℕ) : (∑ i ∈ Finset.range (n + 1), (i : ℝ)) = n * (n + 1) / 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

/-- 1.14 b) `1³ + 2³ + ... + n³ = (n(n+1)/2)²`. -/
theorem gyak_1_14_b (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), (i : ℝ) ^ 3) = (n * (n + 1) / 2) ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

/-- 1.14 c) Mértani sor: `1 + q + ... + qⁿ = (qⁿ⁺¹ - 1)/(q - 1)`, ha `q ≠ 1`. -/
theorem gyak_1_14_c (q : ℝ) (hq : q ≠ 1) (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), q ^ i) = (q ^ (n + 1) - 1) / (q - 1) := by
  have hq' : q - 1 ≠ 0 := sub_ne_zero.mpr hq
  rw [eq_div_iff hq', geom_sum_mul]

/-! ## 1.15. gyakorlat — további indukciós állítások -/

/-- 1.15 a) `∑ i(3i+1) = n(n+1)²`. -/
theorem gyak_1_15_a (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), (i : ℝ) * (3 * i + 1)) = n * (n + 1) ^ 2 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

/-- 1.15 b) `∑ i(i+1) = n(n+1)(n+2)/3`. -/
theorem gyak_1_15_b (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), (i : ℝ) * (i + 1)) = n * (n + 1) * (n + 2) / 3 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

/-- Segédlemma: `2(√(x+1) - √x) < 1/√x`, azaz a gyökös teleszkopikus becslés alsó fele.
Gyöktelenítés: `√(x+1) - √x = 1/(√(x+1)+√x)`. -/
theorem sqrt_lepes_also (x : ℝ) (hx : 0 < x) :
    2 * (Real.sqrt (x + 1) - Real.sqrt x) < 1 / Real.sqrt x := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have ht : 0 < Real.sqrt (x + 1) := Real.sqrt_pos.mpr (by linarith)
  have hlt : Real.sqrt x < Real.sqrt (x + 1) := Real.sqrt_lt_sqrt hx.le (by linarith)
  have h1 : Real.sqrt (x + 1) ^ 2 = x + 1 := Real.sq_sqrt (by linarith)
  have h2 : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx.le
  rw [lt_div_iff₀ hs]
  nlinarith

/-- Segédlemma: `1/√(x+1) < 2(√(x+1) - √x)`. -/
theorem sqrt_lepes_felso (x : ℝ) (hx : 0 < x) :
    1 / Real.sqrt (x + 1) < 2 * (Real.sqrt (x + 1) - Real.sqrt x) := by
  have hs : 0 < Real.sqrt x := Real.sqrt_pos.mpr hx
  have ht : 0 < Real.sqrt (x + 1) := Real.sqrt_pos.mpr (by linarith)
  have hlt : Real.sqrt x < Real.sqrt (x + 1) := Real.sqrt_lt_sqrt hx.le (by linarith)
  have h1 : Real.sqrt (x + 1) ^ 2 = x + 1 := Real.sq_sqrt (by linarith)
  have h2 : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx.le
  rw [div_lt_iff₀ ht]
  nlinarith

/-- 1.15 c) alsó becslés: `2√(n+1) - 2 < ∑_{i=1}^n 1/√i`. -/
theorem gyak_1_15_c_also (n : ℕ) (hn : 1 ≤ n) :
    2 * Real.sqrt (n + 1) - 2 < ∑ i ∈ Finset.Icc 1 n, 1 / Real.sqrt i := by
  induction n, hn using Nat.le_induction with
  | base =>
    norm_num
    nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), Real.sqrt_nonneg 2,
      Real.sqrt_lt_sqrt (by norm_num : (0 : ℝ) ≤ 2) (by norm_num : (2 : ℝ) < 9 / 4)]
  | succ n hn ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have hx : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hstep := sqrt_lepes_also ((n : ℝ) + 1) hx
    have hcast2 : Real.sqrt ((n + 1 : ℕ) : ℝ) = Real.sqrt ((n : ℝ) + 1) := by push_cast; ring_nf
    rw [hcast2]
    push_cast
    linarith [hstep, ih]

/-- 1.15 c) felső becslés: `∑_{i=1}^n 1/√i < 2√n - 1`.
Megjegyzés: `n = 1`-re a két oldal *egyenlő* (`1 = 1`), ezért a szigorú egyenlőtlenség
csak `n ≥ 2` esetén igaz; a feladatszöveg állítását ennek megfelelően pontosítottuk. -/
theorem gyak_1_15_c_felso (n : ℕ) (hn : 2 ≤ n) :
    (∑ i ∈ Finset.Icc 1 n, 1 / Real.sqrt i) < 2 * Real.sqrt n - 1 := by
  induction n, hn using Nat.le_induction with
  | base =>
    rw [show Finset.Icc 1 2 = {1, 2} by decide]
    norm_num
    have h2 : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
    have hinv : (Real.sqrt 2)⁻¹ = Real.sqrt 2 / 2 := by
      rw [inv_eq_one_div, div_eq_div_iff (ne_of_gt h2) (by norm_num : (2 : ℝ) ≠ 0)]
      nlinarith [hsq]
    rw [hinv]
    nlinarith [hsq, h2]
  | succ n hn ih =>
    rw [Finset.sum_Icc_succ_top (by omega)]
    have hx : (0 : ℝ) < (n : ℝ) := by positivity
    have hstep := sqrt_lepes_felso (n : ℝ) hx
    have hcast : Real.sqrt ((n + 1 : ℕ) : ℝ) = Real.sqrt ((n : ℝ) + 1) := by push_cast; ring_nf
    rw [hcast]
    linarith [hstep, ih]

/-- 1.15 d) `n! < ((n+1)/2)ⁿ`, ha `n ≥ 2`. A lépés magja a Bernoulli-egyenlőtlenségből
adódó `(1 + 1/(n+1))^(n+1) ≥ 2` becslés. -/
theorem gyak_1_15_d (n : ℕ) (hn : 2 ≤ n) : (Nat.factorial n : ℝ) < (((n : ℝ) + 1) / 2) ^ n := by
  induction n, hn using Nat.le_induction with
  | base => norm_num [Nat.factorial]
  | succ n hn ih =>
    have hn0 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hbern : (2 : ℝ) ≤ (1 + 1 / ((n : ℝ) + 1)) ^ (n + 1) := by
      have h := one_add_mul_le_pow (a := 1 / ((n : ℝ) + 1))
        (by
          have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
          linarith) (n + 1)
      have hcast : ((n + 1 : ℕ) : ℝ) * (1 / ((n : ℝ) + 1)) = 1 := by
        push_cast
        field_simp
      rw [hcast] at h
      linarith
    have hfac : (Nat.factorial (n + 1) : ℝ) = ((n : ℝ) + 1) * Nat.factorial n := by
      rw [Nat.factorial_succ]
      push_cast
      ring
    have hstep : ((n : ℝ) + 1) * (((n : ℝ) + 1) / 2) ^ n ≤ (((n : ℝ) + 1 + 1) / 2) ^ (n + 1) := by
      have hsplit : ((n : ℝ) + 1 + 1) / 2 = (((n : ℝ) + 1) / 2) * (1 + 1 / ((n : ℝ) + 1)) := by
        field_simp
      rw [hsplit, mul_pow]
      have hpos : (0 : ℝ) < (((n : ℝ) + 1) / 2) ^ (n + 1) := by positivity
      have h1 : (((n : ℝ) + 1) / 2) ^ (n + 1) * 2 ≤
          (((n : ℝ) + 1) / 2) ^ (n + 1) * (1 + 1 / ((n : ℝ) + 1)) ^ (n + 1) := by
        exact mul_le_mul_of_nonneg_left hbern hpos.le
      have h2 : ((n : ℝ) + 1) * (((n : ℝ) + 1) / 2) ^ n = (((n : ℝ) + 1) / 2) ^ (n + 1) * 2 := by
        rw [pow_succ]
        field_simp
      linarith
    have hpos2 : (0 : ℝ) < (n : ℝ) + 1 := hn0
    have hmul : ((n : ℝ) + 1) * (Nat.factorial n : ℝ) <
        ((n : ℝ) + 1) * (((n : ℝ) + 1) / 2) ^ n := by
      exact mul_lt_mul_of_pos_left ih hpos2
    have hgoal : (((n : ℝ) + 1 + 1) / 2) ^ (n + 1) = ((((n + 1 : ℕ) : ℝ) + 1) / 2) ^ (n + 1) := by
      push_cast
      ring_nf
    rw [hfac, ← hgoal]
    linarith [hmul, hstep]

/-! ## 1.16. gyakorlat — az első n négyzetszám összege -/

/-- 1.16 `1² + 2² + ... + n² = n(n+1)(2n+1)/6`. -/
theorem gyak_1_16 (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1), (i : ℝ) ^ 2) = n * (n + 1) * (2 * n + 1) / 6 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

/-- 1.17 „Teleszkópos” módszer az `1.16`-hoz: `(i+1)³ - i³ = 3i² + 3i + 1`,
és az összegzés teleszkopikusan összeomlik. Ez a nem indukciós bizonyítás magja. -/
theorem gyak_1_17_teleszkop (n : ℕ) :
    (∑ i ∈ Finset.range n, (((i : ℝ) + 1) ^ 3 - (i : ℝ) ^ 3)) = (n : ℝ) ^ 3 := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

/-! ## 1.19. gyakorlat — binomiális azonosságok -/

/-- 1.19 a) Pascal-azonosság. -/
theorem gyak_1_19_a (n k : ℕ) :
    Nat.choose n k + Nat.choose n (k + 1) = Nat.choose (n + 1) (k + 1) :=
  (Nat.choose_succ_succ n k).symm

/-- 1.19 b) Binomiális tétel. -/
theorem gyak_1_19_b (a b : ℝ) (n : ℕ) :
    (a + b) ^ n = ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * a ^ (n - k) * b ^ k := by
  rw [add_pow, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun k hk => ?_
  simp only [Finset.mem_range] at hk
  have hk' : k ≤ n := by omega
  have e1 : n + 1 - 1 - k = n - k := by omega
  rw [e1, Nat.sub_sub_self hk', Nat.choose_symm hk']
  ring

/-- 1.19 c) „Hokiütő-azonosság”. -/
theorem gyak_1_19_c (n k : ℕ) :
    (∑ i ∈ Finset.Icc k n, Nat.choose i k) = Nat.choose (n + 1) (k + 1) :=
  Nat.sum_Icc_choose n k

end Kalkulus1.Szakasz1
