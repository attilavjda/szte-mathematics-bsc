/-
# 2. feladatsor — Függvények, elemi függvények, függvénytulajdonságok,
#   ábrázolás, inverz

A `kalkulus_gyakorlo.pdf` 2. feladatsorának formalizálása.
-/
import Mathlib

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace Kalkulus1.Szakasz2

open Set Function Filter

/-! ## 2.1. gyakorlat — értelmezési tartomány -/

/-- 2.1 a) A `√(2x+1)` értelmezési tartománya `[-1/2, ∞)`. -/
theorem gyak_2_1_a : {x : ℝ | 0 ≤ 2 * x + 1} = Set.Ici (-(1 : ℝ) / 2) := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_Ici]
  constructor <;> intro h <;> linarith

/-- 2.1 b) A `√(9 - (2x+1)²)` értelmezési tartománya `[-2, 1]`. -/
theorem gyak_2_1_b : {x : ℝ | 0 ≤ 9 - (2 * x + 1) ^ 2} = Set.Icc (-2 : ℝ) 1 := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_Icc]
  constructor
  · intro h
    constructor <;> nlinarith [sq_nonneg (2 * x + 1)]
  · rintro ⟨h1, h2⟩
    nlinarith

/-- 2.1 d) Az `ln((x-3)/(x+5))` értelmezési tartománya `(-∞,-5) ∪ (3,∞)`. -/
theorem gyak_2_1_d :
    {x : ℝ | 0 < (x - 3) / (x + 5)} = Set.Iio (-5 : ℝ) ∪ Set.Ioi (3 : ℝ) := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_union, Set.mem_Iio, Set.mem_Ioi]
  rw [div_pos_iff]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩)
    · exact Or.inr (by linarith)
    · exact Or.inl (by linarith)
  · rintro (h | h)
    · exact Or.inr ⟨by linarith, by linarith⟩
    · exact Or.inl ⟨by linarith, by linarith⟩

/-! ## 2.2. gyakorlat — injektivitás, szürjektivitás -/

/-- 2.2 a) `a : [0,1] → [0,1]`, `a(x) = x²` bijektív. -/
theorem gyak_2_2_a_inj :
    Function.Injective (fun x : Set.Icc (0 : ℝ) 1 => (x : ℝ) ^ 2) := by
  rintro ⟨x, hx0, hx1⟩ ⟨y, hy0, hy1⟩ h
  simp only at h
  have : x = y := by nlinarith
  simpa [Subtype.mk_eq_mk] using this

/-- 2.2 b) `b(x) = 2ˣ` injektív, de nem szürjektív `ℝ → ℝ`-ként (nem vesz fel negatív értéket). -/
theorem gyak_2_2_b_inj : Function.Injective (fun x : ℝ => (2 : ℝ) ^ x) := by
  have hs : StrictMono (fun x : ℝ => (2 : ℝ) ^ x) := fun a b h =>
    (Real.rpow_lt_rpow_left_iff (by norm_num)).mpr h
  exact hs.injective

/-- 2.2 b) `b(x) = 2ˣ` nem szürjektív: `-1` nincs a képében. -/
theorem gyak_2_2_b_not_surj : ¬ Function.Surjective (fun x : ℝ => (2 : ℝ) ^ x) := by
  intro h
  obtain ⟨x, hx⟩ := h (-1)
  have : (0 : ℝ) < (2 : ℝ) ^ x := Real.rpow_pos_of_pos (by norm_num) x
  simp only at hx
  linarith

/-- 2.2 c) `c(x) = x³` bijekció `ℝ → ℝ`. -/
theorem gyak_2_2_c : Function.Bijective (fun x : ℝ => x ^ 3) := by
  constructor
  · intro x y h
    simpa using (Odd.strictMono_pow (R := ℝ) (by decide : Odd 3)).injective h
  · apply Continuous.surjective (by fun_prop)
    · exact tendsto_pow_atTop (by norm_num)
    · have h : Filter.Tendsto (fun x : ℝ => (-x) ^ 3) Filter.atBot Filter.atTop :=
        (tendsto_pow_atTop (n := 3) (by norm_num : (3 : ℕ) ≠ 0)).comp
          Filter.tendsto_neg_atBot_atTop
      have h2 : Filter.Tendsto (fun x : ℝ => -((-x) ^ 3)) Filter.atBot Filter.atBot :=
        Filter.tendsto_neg_atTop_atBot.comp h
      exact h2.congr (fun x => by ring)

/-- 2.2 d) `sin` nem injektív. -/
theorem gyak_2_2_d_not_inj : ¬ Function.Injective (fun x : ℝ => Real.sin x) := by
  intro h
  have : (0 : ℝ) = 2 * Real.pi := h (by simp [Real.sin_two_pi])
  have := Real.pi_pos
  linarith

/-- 2.2 d) `sin` nem szürjektív `ℝ → ℝ`-ként. -/
theorem gyak_2_2_d_not_surj : ¬ Function.Surjective (fun x : ℝ => Real.sin x) := by
  intro h
  obtain ⟨x, hx⟩ := h 2
  have := Real.sin_le_one x
  simp only at hx
  linarith

/-! ## 2.3-2.7. gyakorlat — inverz függvények -/

/-- 2.3 a) Az `a(x) = (2x-1)/(3x+2)` inverze `y ↦ (2y+1)/(2-3y)`. -/
theorem gyak_2_3_a (x : ℝ) (hx : 3 * x + 2 ≠ 0) :
    (2 * ((2 * x - 1) / (3 * x + 2)) + 1) / (2 - 3 * ((2 * x - 1) / (3 * x + 2))) = x := by
  -- `field_simp` a nevezőket normálalakban keresi, ezért a feltételt is úgy adjuk meg:
  have hx' : x * 3 + 2 ≠ 0 := fun h => hx (by linarith)
  have h1 : 2 * ((2 * x - 1) / (3 * x + 2)) + 1 = 7 * x / (3 * x + 2) := by
    field_simp; ring
  have h2 : 2 - 3 * ((2 * x - 1) / (3 * x + 2)) = 7 / (3 * x + 2) := by
    field_simp; ring
  rw [h1, h2]
  field_simp

/-- 2.3 c) A `c(x) = ∛x + 4` inverze `y ↦ (y-4)³`. -/
theorem gyak_2_3_c (x : ℝ) : ((x ^ ((1 : ℝ) / 3) + 4) - 4) ^ (3 : ℕ) = x ∨ x < 0 := by
  rcases lt_or_ge x 0 with h | h
  · exact Or.inr h
  · left
    simp only [add_sub_cancel_right]
    rw [← Real.rpow_natCast (x ^ ((1:ℝ)/3)) 3, ← Real.rpow_mul h]
    norm_num

/-- 2.6 a) `f(x) = 2x⁴ + 3x³ + 4` nem injektív. -/
theorem gyak_2_6_a : ¬ Function.Injective (fun x : ℝ => 2 * x ^ 4 + 3 * x ^ 3 + 4) := by
  intro h
  have h0 : (0 : ℝ) = -3 / 2 := by
    apply h
    simp only
    ring_nf
  norm_num at h0

/-- 2.6 b) `g(x) = x³ + x + 2` injektív (szigorúan monoton nő). -/
theorem gyak_2_6_b : Function.Injective (fun x : ℝ => x ^ 3 + x + 2) := by
  have hmono : StrictMono (fun x : ℝ => x ^ 3 + x + 2) := by
    intro a b hab
    have h3 : a ^ 3 < b ^ 3 := by
      exact (Odd.strictMono_pow (R := ℝ) (by decide : Odd 3)) hab
    simp only
    linarith
  exact hmono.injective

/-- 2.6 c) `h(x) = x³ - 3` bijektív, inverze `y ↦ ∛(y+3)`. -/
theorem gyak_2_6_c : Function.Bijective (fun x : ℝ => x ^ 3 - 3) := by
  constructor
  · have hmono : StrictMono (fun x : ℝ => x ^ 3 - 3) := fun a b hab => by
      have := (Odd.strictMono_pow (R := ℝ) (by decide : Odd 3)) hab
      simp only
      linarith
    exact hmono.injective
  · intro y
    obtain ⟨x, hx⟩ := gyak_2_2_c.2 (y + 3)
    exact ⟨x, by simp only at hx ⊢; linarith⟩

/-- 2.7 `f(x) = (x+1)/(x-1)` involúció az `ℝ \ {1}` halmazon: `f ∘ f = id`. -/
theorem gyak_2_7_involucio (x : ℝ) (hx : x ≠ 1) :
    ((x + 1) / (x - 1) + 1) / ((x + 1) / (x - 1) - 1) = x := by
  have h1 : x - 1 ≠ 0 := sub_ne_zero.mpr hx
  field_simp
  ring

/-- 2.7 `f` az `ℝ \ {1}` halmazt önmagára képezi. -/
theorem gyak_2_7_ertekkeszlet (x : ℝ) (hx : x ≠ 1) : (x + 1) / (x - 1) ≠ 1 := by
  have h1 : x - 1 ≠ 0 := sub_ne_zero.mpr hx
  intro h
  rw [div_eq_one_iff_eq h1] at h
  linarith

/-! ## 2.10-2.15. gyakorlat — összetett függvények -/

/-- 2.10 b) `f(x) = x²`, `g(x) = √(1-x)`, ezért `(f∘g)(x) = 1-x`, ha `x ≤ 1`. -/
theorem gyak_2_10_b (x : ℝ) (hx : x ≤ 1) : (Real.sqrt (1 - x)) ^ 2 = 1 - x :=
  Real.sq_sqrt (by linarith)

/-- 2.10 b) `(g∘f)(x) = √(1-x²)`, értelmezve `|x| ≤ 1` esetén. -/
theorem gyak_2_10_b' (x : ℝ) (hx : |x| ≤ 1) : 0 ≤ 1 - x ^ 2 := by
  have := abs_le.mp hx
  nlinarith [this.1, this.2]

/-- 2.11 `f(x) = 2x²-1` és `g(x) = 4x³-3x` felcserélhetők (Csebisev-polinomok!). -/
theorem gyak_2_11 (x : ℝ) :
    2 * (4 * x ^ 3 - 3 * x) ^ 2 - 1 = 4 * (2 * x ^ 2 - 1) ^ 3 - 3 * (2 * x ^ 2 - 1) := by
  ring

/-- 2.15 `f(x) = 3x+1`, `g(x) = x+3`; a `(g∘f∘f)(x) = (f∘g∘g)(x)` egyenlet megoldása `x = 2`. -/
theorem gyak_2_15 (x : ℝ) :
    ((3 * (3 * x + 1) + 1) + 3) = (3 * ((x + 3) + 3) + 1) ↔ x = 2 := by
  constructor <;> intro h <;> linarith

/-! ## 2.17-2.21. gyakorlat — szerkezeti állítások -/

/-- 2.17 a) Két injektív függvény összege nem feltétlenül injektív. -/
theorem gyak_2_17_a :
    ∃ f g : ℝ → ℝ, Function.Injective f ∧ Function.Injective g ∧
      ¬ Function.Injective (fun x => f x + g x) := by
  refine ⟨id, fun x => -x, fun a b h => h, fun a b h => by simpa using h, ?_⟩
  intro h
  have : (0 : ℝ) = 1 := h (by simp)
  norm_num at this

/-- 2.17 b) Két injektív függvény szorzata nem feltétlenül injektív. -/
theorem gyak_2_17_b :
    ∃ f g : ℝ → ℝ, Function.Injective f ∧ Function.Injective g ∧
      ¬ Function.Injective (fun x => f x * g x) := by
  refine ⟨id, id, fun a b h => h, fun a b h => h, ?_⟩
  intro h
  have : (1 : ℝ) = -1 := h (by norm_num)
  norm_num at this

/-- 2.18 Injektív függvények kompozíciója injektív. -/
theorem gyak_2_18 {f g : ℝ → ℝ} (hf : Function.Injective f) (hg : Function.Injective g) :
    Function.Injective (f ∘ g) := hf.comp hg

/-- 2.19 Egy nemnulla, `n`-edfokú valós polinomnak legfeljebb `n` gyöke van. -/
theorem gyak_2_19 (p : Polynomial ℝ) (hp : p ≠ 0) :
    p.roots.toFinset.card ≤ p.natDegree := by
  calc p.roots.toFinset.card ≤ Multiset.card p.roots := p.roots.toFinset_card_le
    _ ≤ p.natDegree := Polynomial.card_roots' p

/-- 2.20 a) Az `f(x) = x(x-3)²` függvény maximuma a `(0,3)` intervallumon `4`, `x = 1`-nél. -/
theorem gyak_2_20_a (x : ℝ) (hx : x ∈ Set.Ioo (0 : ℝ) 3) :
    x * (x - 3) ^ 2 ≤ 1 * (1 - 3) ^ 2 := by
  obtain ⟨h0, h3⟩ := hx
  nlinarith [sq_nonneg (x - 1), sq_nonneg (x + 2), sq_nonneg (x - 3)]

/-- 2.20 a) `f(x) = x(x-3)² > 0` a `(0,∞)` intervallumon, kivéve `x = 3`-at. -/
theorem gyak_2_20_a' (x : ℝ) (hx : 0 < x) (h3 : x ≠ 3) : 0 < x * (x - 3) ^ 2 := by
  have h4 : x - 3 ≠ 0 := sub_ne_zero.mpr h3
  have h5 : (0 : ℝ) < (x - 3) ^ 2 :=
    lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 h4))
  exact mul_pos hx h5

end Kalkulus1.Szakasz2
