import Analizis.Ch04a_SorozatokAlapok

/-!
# Leindler László: Analízis — 4. fejezet: Számsorozatok (4.9–4.13. szakasz)

Műveletek konvergens sorozatokkal, egyenlőtlenségekkel kapcsolatos határértéktételek,
végtelenbe divergáló sorozatok, valamint a 4.13. szakasz néhány kidolgozott feladata
(25–32. oldal).
-/

namespace Leindler
namespace Ch04

open scoped BigOperators

/-! ## 4.9. Műveletek konvergens sorozatokkal -/

/-- **4.9.1. Tétel, 1. állítás.** Ha `aₙ → A` és `bₙ → B`, akkor `aₙ + bₙ → A + B`.

*Bizonyítás.* `ε/2`-höz is van `ν₁` és `ν₂`; ha `n > ν = max(ν₁, ν₂)`, akkor
`|(aₙ + bₙ) - (A + B)| ≤ |aₙ - A| + |bₙ - B| < ε/2 + ε/2 = ε`. -/
theorem hatarErtek_add {a b : Sorozat} {A B : ℝ} (ha : HatarErtek a A) (hb : HatarErtek b B) :
    HatarErtek (fun n => a n + b n) (A + B) := by
  intro ε hε
  obtain ⟨N₁, hN₁⟩ := ha (ε / 2) (by linarith)
  obtain ⟨N₂, hN₂⟩ := hb (ε / 2) (by linarith)
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  have h₁ := hN₁ n (lt_of_le_of_lt (le_max_left _ _) hn)
  have h₂ := hN₂ n (lt_of_le_of_lt (le_max_right _ _) hn)
  calc |a n + b n - (A + B)| = |(a n - A) + (b n - B)| := by ring_nf
    _ ≤ |a n - A| + |b n - B| := Ch03.haromszog_egyenlotlenseg _ _
    _ < ε := by linarith

/-- **4.9.1. Tétel, 1. állítás (különbség).** Ha `aₙ → A` és `bₙ → B`, akkor
`aₙ - bₙ → A - B`. -/
theorem hatarErtek_sub {a b : Sorozat} {A B : ℝ} (ha : HatarErtek a A) (hb : HatarErtek b B) :
    HatarErtek (fun n => a n - b n) (A - B) := by
  intro ε hε
  obtain ⟨N₁, hN₁⟩ := ha (ε / 2) (by linarith)
  obtain ⟨N₂, hN₂⟩ := hb (ε / 2) (by linarith)
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  have h₁ := hN₁ n (lt_of_le_of_lt (le_max_left _ _) hn)
  have h₂ := hN₂ n (lt_of_le_of_lt (le_max_right _ _) hn)
  calc |a n - b n - (A - B)| = |(a n - A) + (-(b n - B))| := by ring_nf
    _ ≤ |a n - A| + |(-(b n - B))| := Ch03.haromszog_egyenlotlenseg _ _
    _ = |a n - A| + |b n - B| := by rw [abs_neg]
    _ < ε := by linarith

/-- **4.9.1. Tétel, 2. állítás.** Ha `aₙ → A`, akkor `c·aₙ → c·A`.

*Bizonyítás.* `c = 0` esetén az állítás nyilvánvaló.  Ha `c ≠ 0`, akkor
`|caₙ - cA| = |c||aₙ - A| < ε` teljesül, ha `|aₙ - A| < ε/|c|`. -/
theorem hatarErtek_const_mul {a : Sorozat} {A : ℝ} (c : ℝ) (ha : HatarErtek a A) :
    HatarErtek (fun n => c * a n) (c * A) := by
  intro ε hε
  rcases eq_or_ne c 0 with rfl | hc
  · exact ⟨0, fun n _ => by simpa using hε⟩
  · have hc' : 0 < |c| := abs_pos.mpr hc
    obtain ⟨N, hN⟩ := ha (ε / |c|) (by positivity)
    refine ⟨N, fun n hn => ?_⟩
    have := hN n hn
    calc |c * a n - c * A| = |c| * |a n - A| := by rw [← abs_mul]; ring_nf
      _ < |c| * (ε / |c|) := by exact mul_lt_mul_of_pos_left this hc'
      _ = ε := by field_simp

/-- **4.9.1. Tétel, 3. állítás.** Ha `aₙ → A` és `bₙ → B`, akkor `aₙbₙ → AB`.

*Bizonyítás.* Alkalmasan választott nullával bővítünk:
`|aₙbₙ - AB| ≤ |aₙ||bₙ - B| + |B||aₙ - A|`.  Mivel konvergens sorozat korlátos,
`|aₙ| ≤ K`; a nevezőkben `K + 1`, illetve `|B| + 1` szerepel, hogy ne legyen nulla. -/
theorem hatarErtek_mul {a b : Sorozat} {A B : ℝ} (ha : HatarErtek a A) (hb : HatarErtek b B) :
    HatarErtek (fun n => a n * b n) (A * B) := by
  intro ε hε
  obtain ⟨K, hK⟩ := (korlatos_iff_abs a).mp (konvergens_korlatos ⟨A, ha⟩)
  have hK0 : 0 ≤ K := le_trans (abs_nonneg _) (hK 0)
  obtain ⟨N₁, hN₁⟩ := ha (ε / (2 * (|B| + 1))) (by positivity)
  obtain ⟨N₂, hN₂⟩ := hb (ε / (2 * (K + 1))) (by positivity)
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  have h₁ := hN₁ n (lt_of_le_of_lt (le_max_left _ _) hn)
  have h₂ := hN₂ n (lt_of_le_of_lt (le_max_right _ _) hn)
  have t₁ : |a n| * |b n - B| ≤ K * (ε / (2 * (K + 1))) :=
    le_trans (mul_le_mul_of_nonneg_right (hK n) (abs_nonneg _))
      (mul_le_mul_of_nonneg_left (le_of_lt h₂) hK0)
  have t₂ : |B| * |a n - A| ≤ |B| * (ε / (2 * (|B| + 1))) :=
    mul_le_mul_of_nonneg_left (le_of_lt h₁) (abs_nonneg _)
  have hb1 : K * (ε / (2 * (K + 1))) < ε / 2 := by
    rw [mul_div_assoc'] at *
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hb2 : |B| * (ε / (2 * (|B| + 1))) < ε / 2 := by
    rw [mul_div_assoc'] at *
    rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [abs_nonneg B]
  calc |a n * b n - A * B| = |a n * (b n - B) + B * (a n - A)| := by ring_nf
    _ ≤ |a n * (b n - B)| + |B * (a n - A)| := Ch03.haromszog_egyenlotlenseg _ _
    _ = |a n| * |b n - B| + |B| * |a n - A| := by rw [abs_mul, abs_mul]
    _ < ε := by linarith

/-- Segédállítás a hányadoshoz: ha `bₙ → B` és `B ≠ 0`, akkor van olyan `ν₀`, hogy
`n > ν₀` esetén `|bₙ| > |B|/2`. -/
theorem nevezo_also_becsles {b : Sorozat} {B : ℝ} (hb : HatarErtek b B) (hB : B ≠ 0) :
    ∃ N₀ : ℕ, ∀ n > N₀, |B| / 2 < |b n| := by
  have hB' : 0 < |B| := abs_pos.mpr hB
  obtain ⟨N₀, hN₀⟩ := hb (|B| / 2) (by linarith)
  refine ⟨N₀, fun n hn => ?_⟩
  have h := hN₀ n hn
  have : |B| - |b n| ≤ |B - b n| := by
    have := abs_sub_abs_le_abs_sub B (b n)
    linarith
  rw [abs_sub_comm] at this
  linarith

/-- **4.9.1. Tétel, 4. állítás.** Ha `aₙ → A`, `bₙ → B` és `B ≠ 0`, akkor `aₙ/bₙ → A/B`. -/
theorem hatarErtek_div {a b : Sorozat} {A B : ℝ} (ha : HatarErtek a A) (hb : HatarErtek b B)
    (hB : B ≠ 0) : HatarErtek (fun n => a n / b n) (A / B) := by
  rw [hatarErtek_iff_tendsto] at ha hb ⊢
  exact ha.div hb hB

/-- **4.9.4. Tétel, 1. állítás.** Ha `aₙ → 0` és `|bₙ| ≤ K`, akkor `aₙbₙ → 0`. -/
theorem nullsorozat_szor_korlatos {a b : Sorozat} {K : ℝ} (ha : HatarErtek a 0)
    (hb : ∀ n, |b n| ≤ K) : HatarErtek (fun n => a n * b n) 0 := by
  have hK0 : 0 ≤ K := le_trans (abs_nonneg _) (hb 0)
  intro ε hε
  obtain ⟨N, hN⟩ := ha (ε / (K + 1)) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have h := hN n hn
  rw [sub_zero] at h ⊢
  rw [abs_mul]
  calc |a n| * |b n| ≤ |a n| * K := mul_le_mul_of_nonneg_left (hb n) (abs_nonneg _)
    _ ≤ (ε / (K + 1)) * K := by
        exact mul_le_mul_of_nonneg_right (le_of_lt h) hK0
    _ < ε := by
        rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
        nlinarith

/-- **4.9.4. Tétel, 5. állítás.** Ha `aₙ → A`, akkor `|aₙ| → |A|`.  (A fordítottja
általában nem igaz, lásd a `{(-1)ⁿ}` sorozatot.) -/
theorem hatarErtek_abs {a : Sorozat} {A : ℝ} (ha : HatarErtek a A) :
    HatarErtek (fun n => |a n|) |A| := by
  intro ε hε
  obtain ⟨N, hN⟩ := ha ε hε
  refine ⟨N, fun n hn => ?_⟩
  exact lt_of_le_of_lt (abs_abs_sub_abs_le_abs_sub _ _) (hN n hn)

/-- **4.9.4. Tétel, 6. állítás.** Ha `|aₙ| → 0`, akkor `aₙ → 0`. -/
theorem hatarErtek_of_abs {a : Sorozat} (ha : HatarErtek (fun n => |a n|) 0) :
    HatarErtek a 0 := by
  intro ε hε
  obtain ⟨N, hN⟩ := ha ε hε
  refine ⟨N, fun n hn => ?_⟩
  have := hN n hn
  simpa using this

/-- **4.9.4. Tétel, 2. állítás.** Ha `aₙ → A`, `A > 0`, akkor `√aₙ → √A`. -/
theorem hatarErtek_sqrt {a : Sorozat} {A : ℝ} (ha : HatarErtek a A) :
    HatarErtek (fun n => Real.sqrt (a n)) (Real.sqrt A) := by
  rw [hatarErtek_iff_tendsto] at ha ⊢
  exact (Real.continuous_sqrt.tendsto A).comp ha

/-! ## 4.10. Egyenlőtlenségekkel kapcsolatos határértéktételek -/

/-- **4.10.1. Tétel.** Ha `aₙ → A`, `bₙ → B` és `A < B`, akkor majdnem minden `n`-re
`aₙ < bₙ`.

*Bizonyítás.* `(B - A)/4`-hez választva a küszöbszámokat, `n > ν` esetén
`aₙ < A + (B-A)/4 = (3A + B)/4 < (A + 3B)/4 = B - (B-A)/4 < bₙ`. -/
theorem kisebb_majdnem_minden {a b : Sorozat} {A B : ℝ} (ha : HatarErtek a A)
    (hb : HatarErtek b B) (hAB : A < B) : ∃ N : ℕ, ∀ n > N, a n < b n := by
  obtain ⟨N₁, hN₁⟩ := ha ((B - A) / 4) (by linarith)
  obtain ⟨N₂, hN₂⟩ := hb ((B - A) / 4) (by linarith)
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  have h₁ := abs_lt.mp (hN₁ n (lt_of_le_of_lt (le_max_left _ _) hn))
  have h₂ := abs_lt.mp (hN₂ n (lt_of_le_of_lt (le_max_right _ _) hn))
  linarith [h₁.2, h₂.1]

/-- **4.10.3. Tétel.** Ha `aₙ → A`, `bₙ → B` és `aₙ ≤ bₙ` majdnem minden `n`-re,
akkor `A ≤ B`.

*Bizonyítás.* Indirekt: ha `A > B` lenne, akkor a 4.10.1. Tétel szerint majdnem minden
`n`-re `bₙ < aₙ` teljesülne, ami ellentmond a feltételnek. -/
theorem hatarErtek_le {a b : Sorozat} {A B : ℝ} (ha : HatarErtek a A) (hb : HatarErtek b B)
    {N₀ : ℕ} (hle : ∀ n > N₀, a n ≤ b n) : A ≤ B := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨N, hN⟩ := kisebb_majdnem_minden hb ha hcon
  have := hN (max N N₀ + 1) (by omega)
  have := hle (max N N₀ + 1) (by omega)
  linarith

/-- **4.10.5. Következmény.** Nemnegatív tagú konvergens sorozat határértéke is
nemnegatív. -/
theorem nemnegativ_hatarerteke {a : Sorozat} {A : ℝ} (ha : HatarErtek a A)
    (hpos : ∀ n, 0 ≤ a n) : 0 ≤ A :=
  hatarErtek_le (a := fun _ => 0) (b := a) (allando_hatarerteke 0) ha (N₀ := 0)
    (fun n _ => hpos n)

/-- **4.10.6. Tétel (Rendőrelv).** Ha `aₙ ≤ bₙ ≤ cₙ` majdnem minden `n`-re, továbbá
`aₙ → A` és `cₙ → A`, akkor `bₙ → A`.

*Bizonyítás.* A könyv becslése szerint `n > ν = max(ν₀, ν₁, ν₂)` esetén
`|bₙ - A| = |bₙ - cₙ + cₙ - A| ≤ |aₙ - A| + 2|cₙ - A| < ε`. -/
theorem rendorelv {a b c : Sorozat} {A : ℝ} {N₀ : ℕ} (hle : ∀ n > N₀, a n ≤ b n ∧ b n ≤ c n)
    (ha : HatarErtek a A) (hc : HatarErtek c A) : HatarErtek b A := by
  intro ε hε
  obtain ⟨N₁, hN₁⟩ := ha (ε / 2) (by linarith)
  obtain ⟨N₂, hN₂⟩ := hc (ε / 2) (by linarith)
  refine ⟨max N₀ (max N₁ N₂), fun n hn => ?_⟩
  have hn0 : n > N₀ := lt_of_le_of_lt (le_max_left _ _) hn
  have hn1 : n > N₁ := lt_of_le_of_lt (le_trans (le_max_left _ _) (le_max_right N₀ _)) hn
  have hn2 : n > N₂ := lt_of_le_of_lt (le_trans (le_max_right _ _) (le_max_right N₀ _)) hn
  obtain ⟨hab, hbc⟩ := hle n hn0
  have h₁ := abs_lt.mp (hN₁ n hn1)
  have h₂ := abs_lt.mp (hN₂ n hn2)
  exact abs_lt.mpr ⟨by linarith [h₁.1], by linarith [h₂.2]⟩

/-! ## 4.11. Végtelenbe divergáló sorozatok (valódi divergens sorozatok) -/

/-- **4.11.1. Definíció.** A `{dₙ}` sorozat a *plusz végtelenbe divergál*, ha bármilyen
(nagy) `M` számhoz megadható olyan `ν` index, hogy `n > ν` esetén `dₙ > M`. -/
def PlusVegtelenbeDivergal (d : Sorozat) : Prop := ∀ M : ℝ, ∃ N : ℕ, ∀ n > N, d n > M

/-- **4.11.1. Definíció.** A `{dₙ}` sorozat a *mínusz végtelenbe divergál*, ha bármilyen
(kicsi) `m` számhoz megadható olyan `ν`, hogy `n > ν` esetén `dₙ < m`. -/
def MinuszVegtelenbeDivergal (d : Sorozat) : Prop := ∀ m : ℝ, ∃ N : ℕ, ∀ n > N, d n < m

/-! ## 4.12. Néhány egyszerű állítás divergens sorozatokkal kapcsolatban -/

/-- **4.12.1. Tétel, 1. állítás.** Valódi divergens sorozat bármely részsorozata is
valódi divergens. -/
theorem reszsorozat_divergal {d e : Sorozat} (he : Reszsorozat e d)
    (hd : PlusVegtelenbeDivergal d) : PlusVegtelenbeDivergal e := by
  obtain ⟨φ, hφ, rfl⟩ := he
  intro M
  obtain ⟨N, hN⟩ := hd M
  exact ⟨N, fun k hk => hN (φ k) (lt_of_lt_of_le hk (strictMono_id_le hφ k))⟩

/-- **4.12.1. Tétel, 2. állítás.** Ha `dₙ → ∞`, akkor `-dₙ → -∞`. -/
theorem negalt_divergal {d : Sorozat} (hd : PlusVegtelenbeDivergal d) :
    MinuszVegtelenbeDivergal (fun n => -d n) := by
  intro m
  obtain ⟨N, hN⟩ := hd (-m)
  exact ⟨N, fun n hn => by linarith [hN n hn]⟩

/-- **4.12.1. Tétel, 3. állítás.** Ha `dₙ → ∞` és `cₙ → C`, akkor `dₙ ± cₙ → ∞`. -/
theorem divergal_add_konvergens {d c : Sorozat} {C : ℝ} (hd : PlusVegtelenbeDivergal d)
    (hc : HatarErtek c C) : PlusVegtelenbeDivergal (fun n => d n + c n) := by
  intro M
  obtain ⟨N₁, hN₁⟩ := hc 1 one_pos
  obtain ⟨N₂, hN₂⟩ := hd (M + |C| + 1)
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  have h₁ := abs_lt.mp (hN₁ n (lt_of_le_of_lt (le_max_left _ _) hn))
  have h₂ := hN₂ n (lt_of_le_of_lt (le_max_right _ _) hn)
  have : -|C| ≤ C := neg_abs_le C
  linarith [h₁.1]

/-- **4.12.1. Tétel, 5. állítás.** Ha `dₙ → ∞` és `|bₙ| ≤ K`, akkor `dₙ ± bₙ → ∞`.

*Bizonyítás (a könyv szerint).* `M + K`-hoz is van olyan `ν₁`, hogy `n > ν₁` esetén
`dₙ > M + K`; így `n > ν₁`-re `dₙ ± bₙ > (M + K) - K = M`. -/
theorem divergal_add_korlatos {d b : Sorozat} {K : ℝ} (hd : PlusVegtelenbeDivergal d)
    (hb : ∀ n, |b n| ≤ K) : PlusVegtelenbeDivergal (fun n => d n + b n) := by
  intro M
  obtain ⟨N, hN⟩ := hd (M + K)
  refine ⟨N, fun n hn => ?_⟩
  have h₁ := hN n hn
  have h₂ : -K ≤ b n := neg_le_of_abs_le (hb n)
  linarith

/-- **4.12.1. Tétel, 6. állítás.** Ha `dₙ → ∞` és `|bₙ| ≤ K`, akkor `bₙ/dₙ → 0`. -/
theorem korlatos_per_divergal {d b : Sorozat} {K : ℝ} (hd : PlusVegtelenbeDivergal d)
    (hb : ∀ n, |b n| ≤ K) : HatarErtek (fun n => b n / d n) 0 := by
  have hK0 : 0 ≤ K := le_trans (abs_nonneg _) (hb 0)
  intro ε hε
  obtain ⟨N, hN⟩ := hd ((K + 1) / ε)
  refine ⟨N, fun n hn => ?_⟩
  have hdn : d n > (K + 1) / ε := hN n hn
  have hdpos : 0 < d n := lt_of_le_of_lt (by positivity) hdn
  rw [sub_zero, abs_div, abs_of_pos hdpos, div_lt_iff₀ hdpos]
  have : (K + 1) / ε * ε < d n * ε := by
    exact mul_lt_mul_of_pos_right hdn hε
  rw [div_mul_cancel₀ _ (ne_of_gt hε)] at this
  calc |b n| ≤ K := hb n
    _ < K + 1 := by linarith
    _ < d n * ε := this
    _ = ε * d n := mul_comm _ _

/-- **4.12.1. Tétel, 10. állítás.** Ha `cₙ → 0` és `cₙ > 0`, akkor `1/cₙ → ∞`. -/
theorem reciprok_nullsorozat_divergal {c : Sorozat} (hc : HatarErtek c 0)
    (hpos : ∀ n, 0 < c n) : PlusVegtelenbeDivergal (fun n => 1 / c n) := by
  intro M
  rcases le_or_gt M 0 with hM | hM
  · obtain ⟨N, -⟩ := hc 1 one_pos
    exact ⟨N, fun n _ => lt_of_le_of_lt hM (div_pos one_pos (hpos n))⟩
  · obtain ⟨N, hN⟩ := hc (1 / M) (by positivity)
    refine ⟨N, fun n hn => ?_⟩
    have h := hN n hn
    rw [sub_zero, abs_of_pos (hpos n)] at h
    rw [gt_iff_lt, lt_div_iff₀ (hpos n)]
    calc M * c n < M * (1 / M) := by exact mul_lt_mul_of_pos_left h hM
      _ = 1 := by field_simp

/-- **4.12.1. Tétel, 7. állítás.** Ha `dₙ → ∞` és `eₙ → ∞`, akkor `dₙ + eₙ → ∞`. -/
theorem divergal_add_divergal {d e : Sorozat} (hd : PlusVegtelenbeDivergal d)
    (he : PlusVegtelenbeDivergal e) : PlusVegtelenbeDivergal (fun n => d n + e n) := by
  intro M
  obtain ⟨N₁, hN₁⟩ := hd (M / 2)
  obtain ⟨N₂, hN₂⟩ := he (M / 2)
  refine ⟨max N₁ N₂, fun n hn => ?_⟩
  have h₁ := hN₁ n (lt_of_le_of_lt (le_max_left _ _) hn)
  have h₂ := hN₂ n (lt_of_le_of_lt (le_max_right _ _) hn)
  linarith

/-! ## 4.13. Néhány példa és megoldási fogás -/

/-- **4.13.1. Feladat.** `√(n+1) - √(n-1) → 0`.  (Típusa `∞ - ∞`.)

*Megoldás.* A gyöktelenítés fogásával
`√(n+1) - √(n-1) = 2/(√(n+1) + √(n-1))`, ami nullához tart. -/
theorem feladat_4_13_1 :
    HatarErtek (fun n : ℕ => Real.sqrt ((n : ℝ) + 1) - Real.sqrt ((n : ℝ) - 1)) 0 := by
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt ((2 / ε) ^ 2 + 1)
  refine ⟨N, fun n hn => ?_⟩
  have hnN : ((N : ℝ)) < n := by exact_mod_cast hn
  have hn1 : (2 / ε) ^ 2 + 1 < (n : ℝ) := lt_trans hN hnN
  have hnpos : (0 : ℝ) ≤ (n : ℝ) - 1 := by nlinarith [sq_nonneg (2 / ε)]
  set u := Real.sqrt ((n : ℝ) + 1) with hu
  set v := Real.sqrt ((n : ℝ) - 1) with hv
  have hu2 : u ^ 2 = (n : ℝ) + 1 := Real.sq_sqrt (by linarith)
  have hv2 : v ^ 2 = (n : ℝ) - 1 := Real.sq_sqrt hnpos
  have hupos : 0 < u := Real.sqrt_pos.mpr (by linarith)
  have hvnn : 0 ≤ v := Real.sqrt_nonneg _
  have hkey : (u - v) * (u + v) = 2 := by nlinarith
  have huv : 0 < u + v := by linarith
  have hdiff : u - v = 2 / (u + v) := by field_simp; linarith [hkey]
  have hugt : 2 / ε < u := by
    have h1 : (2 / ε) ^ 2 < u ^ 2 := by rw [hu2]; nlinarith
    nlinarith [div_pos (by norm_num : (0:ℝ) < 2) hε]
  have : 0 < u - v := by rw [hdiff]; positivity
  rw [sub_zero, abs_of_pos this, hdiff, div_lt_iff₀ huv]
  have h2 : 2 < ε * u := (div_lt_iff₀' hε).mp hugt
  nlinarith [mul_nonneg hε.le hvnn]

/-- **4.13.6. Feladat.** `∏_{k=2}^{n} (1 - 1/k²) = (n+1)/(2n) → 1/2`.

Először a szorzat zárt alakját igazoljuk teljes indukcióval. -/
theorem feladat_4_13_6_szorzat (n : ℕ) (hn : 2 ≤ n) :
    ∏ k ∈ Finset.Icc 2 n, (1 - 1 / (k : ℝ) ^ 2) = ((n : ℝ) + 1) / (2 * n) := by
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

end Ch04
end Leindler
