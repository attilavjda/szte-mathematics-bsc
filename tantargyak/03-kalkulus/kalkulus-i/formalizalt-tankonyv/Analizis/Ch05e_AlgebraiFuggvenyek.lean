import Mathlib
import Analizis.Ch05a_FuggvenyekAlapfogalmak
import Analizis.Ch05b_Folytonossag
import Analizis.Ch05c_ZartIntervallum

/-!
# Leindler László: Analízis — 5.7. pont

## Az elemi függvények folytonossága (algebrai függvények)

Ez a fájl a könyv **5.7. pontját** formalizálja: a konstans és az identikus függvény
folytonosságát (5.7.1–5.7.2), a racionális egész (5.7.3–5.7.4) és a racionális
törtfüggvényeket (5.7.5–5.7.6), az irracionális, illetve algebrai függvények
fogalmát (5.7.7–5.7.8), a pozitív és negatív egész kitevőjű gyökfüggvényeket
(5.7.9–5.7.10), valamint a törtkitevős hatványfüggvényeket (5.7.11).

Az **5.7.1., 5.7.2. és 5.7.4. Tétel** már a `Ch05b_Folytonossag` modulban szerepel
(`folytonos_const`, `folytonos_id`, `folytonos_polinom`, `folytonos_racionalis`), itt
ezekre építünk tovább.

A gyökfüggvényeket a könyvvel egyezően a hatványfüggvény *inverzeként* jellemezzük:
a `gyok n x` érték az az egyetlen nemnegatív szám, amelynek `n`-edik hatványa `x`
(5.7.9. a) pont).
-/

namespace Leindler.Ch05

open Set

/-! ## 5.7.1–5.7.4. Racionális egész függvények -/

/-- **5.7.3. Definíció (speciális eset).** Az `y = xⁿ` pozitív egész kitevőjű
hatványfüggvény mindenütt folytonos (az 5.7.4. Tétel speciális esete). -/
theorem folytonos_hatvany (n : ℕ) (x₀ : ℝ) : CauchyFolytonos (fun x => x ^ n) x₀ :=
  (cauchyFolytonos_iff_continuousAt _ _).2 (continuous_pow n).continuousAt

/-- **5.7.3. Definíció (speciális eset).** Az `y = ax + b` lineáris függvény mindenütt
folytonos. -/
theorem folytonos_linearis (a b x₀ : ℝ) : CauchyFolytonos (fun x => a * x + b) x₀ :=
  (cauchyFolytonos_iff_continuousAt _ _).2
    (((continuous_const.mul continuous_id).add continuous_const).continuousAt)

/-- **5.7.3. megjegyzés.** Az `y = x³` függvény minden valós értéket felvesz.

*Bizonyítás.* A könyv az 5.6.2. Tételre (közbülsőérték-tétel) hivatkozik: az `x³`
függvény folytonos, és a `-(|y|+1)` helyen `≤ y`, a `|y|+1` helyen `≥ y` értéket vesz
fel, tehát a két hely között felveszi az `y` értéket is. -/
theorem kob_szurjektiv (y : ℝ) : ∃ x : ℝ, x ^ 3 = y := by
  set K : ℝ := |y| + 1 with hK
  have hKpos : 0 < K := by positivity
  have hy : |y| ≤ K ^ 3 := by nlinarith [abs_nonneg y, sq_nonneg (|y| - 1), sq_nonneg (|y| + 1)]
  have hy₁ : y ≤ K ^ 3 := le_trans (le_abs_self y) hy
  have hy₂ : (-K) ^ 3 ≤ y := by
    have := neg_abs_le y
    nlinarith [abs_nonneg y]
  obtain ⟨x, -, hx⟩ :=
    intermediate_value_Icc (by linarith : (-K : ℝ) ≤ K)
      ((continuous_pow 3).continuousOn) ⟨hy₂, hy₁⟩
  exact ⟨x, hx⟩

/-- **5.7.3. megjegyzés.** Az `y = x²` függvény minden nemnegatív értéket felvesz. -/
theorem negyzet_szurjektiv {y : ℝ} (hy : 0 ≤ y) : ∃ x : ℝ, 0 ≤ x ∧ x ^ 2 = y := by
  set K : ℝ := y + 1 with hK
  have hy₁ : y ≤ K ^ 2 := by nlinarith
  obtain ⟨x, hx, hfx⟩ :=
    intermediate_value_Icc (by linarith : (0 : ℝ) ≤ K)
      ((continuous_pow 2).continuousOn) ⟨by simpa using hy, hy₁⟩
  exact ⟨x, hx.1, hfx⟩

/-! ## 5.7.9. Pozitív egész kitevőjű gyökfüggvények

**5.7.7. Definíció.** *Irracionális függvénynek* azokat a függvényeket nevezzük, amelyek
a független változóból és valós számokból véges sok összeadás, kivonás, szorzás, osztás
és egész kitevős gyökvonás útján állnak elő. **5.7.8. Definíció.** A racionális és
irracionális függvényeket együtt *algebrai függvényeknek* nevezzük. -/

/-- **5.7.9. Definíció.** Az `y = ⁿ√x` gyökfüggvény: nemnegatív `x`-hez azt az egyetlen
nemnegatív számot rendeli, amelynek `n`-edik hatványa `x`. -/
noncomputable def gyok (n : ℕ) (x : ℝ) : ℝ := x ^ ((n : ℝ)⁻¹)

theorem gyok_nonneg (n : ℕ) {x : ℝ} (hx : 0 ≤ x) : 0 ≤ gyok n x := Real.rpow_nonneg hx _

theorem gyok_zero {n : ℕ} (hn : n ≠ 0) : gyok n 0 = 0 := by
  have : ((n : ℝ))⁻¹ ≠ 0 := by
    simp [Nat.cast_eq_zero, hn]
  simpa [gyok] using Real.zero_rpow this

/-- A gyökfüggvény *hozzárendelési törvénye*: `(ⁿ√x)ⁿ = x` minden `x ≥ 0`-ra. -/
theorem gyok_pow {n : ℕ} (hn : n ≠ 0) {x : ℝ} (hx : 0 ≤ x) : gyok n x ^ n = x := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  rw [gyok, ← Real.rpow_natCast (x ^ ((n : ℝ))⁻¹) n, ← Real.rpow_mul hx,
    inv_mul_cancel₀ hn', Real.rpow_one]

/-- A gyökfüggvény az `y = xⁿ` (`x ≥ 0`) függvény inverze: `ⁿ√(xⁿ) = x` minden
`x ≥ 0`-ra. -/
theorem gyok_pow_self {n : ℕ} (hn : n ≠ 0) {x : ℝ} (hx : 0 ≤ x) : gyok n (x ^ n) = x := by
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hn
  rw [gyok, ← Real.rpow_natCast x n, ← Real.rpow_mul hx, mul_inv_cancel₀ hn', Real.rpow_one]

/-- A gyökfüggvény értéke *egyértelmű*: ha `y ≥ 0` és `yⁿ = x`, akkor `y = ⁿ√x`. -/
theorem gyok_egyertelmu {n : ℕ} (hn : n ≠ 0) {x y : ℝ} (hy : 0 ≤ y) (h : y ^ n = x) :
    y = gyok n x := by
  rw [← h, gyok_pow_self hn hy]

/-- Az `y = ⁿ√x` függvény a nemnegatív számok halmazán szigorúan növekedő. -/
theorem gyok_szigNovekedo {n : ℕ} (hn : n ≠ 0) : SzigNovekedo (gyok n) (Ici 0) := by
  rw [szigNovekedo_iff_strictMonoOn]
  intro a ha b hb hab
  have hn' : (0 : ℝ) < (n : ℝ)⁻¹ := by
    have : (0 : ℝ) < n := by exact_mod_cast Nat.pos_of_ne_zero hn
    positivity
  exact Real.rpow_lt_rpow ha hab hn'

/-- **5.7.9. Tétel (a) és b) eset).** A gyökfüggvény az értelmezési tartománya minden
belső pontjában folytonos.

*Bizonyítás.* A könyv szerint az `y = ⁿ√x` függvény az `y = xⁿ` (`x ≥ 0`) folytonos
függvény inverze, ezért az 5.6.1. Tétel értelmében maga is folytonos. -/
theorem folytonos_gyok (n : ℕ) {x₀ : ℝ} (hx₀ : 0 < x₀) : CauchyFolytonos (gyok n) x₀ :=
  (cauchyFolytonos_iff_continuousAt _ _).2
    (Real.continuousAt_rpow_const _ _ (Or.inl (ne_of_gt hx₀)))

/-- **5.7.9. Tétel (a) eset).** A páros kitevőjű gyökfüggvény az `x = 0` pontban
jobbról folytonos. -/
theorem jobbrol_folytonos_gyok {n : ℕ} (hn : n ≠ 0) : JobbrolFolytonos (gyok n) 0 := by
  have hcont : ContinuousAt (gyok n) 0 :=
    Real.continuousAt_rpow_const _ _ (Or.inr (by positivity))
  have := (cauchyFolytonos_iff_continuousAt (gyok n) 0).2 hcont
  intro ε hε
  obtain ⟨δ, hδ, hδ'⟩ := this ε hε
  exact ⟨δ, hδ, fun x _ hx => hδ' x hx⟩

/-- **5.7.9. Definíció (b) eset).** A páratlan kitevőjű gyökfüggvény, `y = ²ᵏ⁺¹√x`,
minden valós számra értelmezve van; a negatív helyeken a `-²ᵏ⁺¹√(-x)` értéket veszi
fel. -/
noncomputable def paratlanGyok (n : ℕ) (x : ℝ) : ℝ :=
  if 0 ≤ x then gyok n x else -gyok n (-x)

/-- A páratlan kitevőjű gyökfüggvény hozzárendelési törvénye: `y = ²ᵏ⁺¹√x` esetén
`y²ᵏ⁺¹ = x` *minden* valós `x`-re. -/
theorem paratlanGyok_pow {n : ℕ} (hn : n ≠ 0) (hodd : Odd n) (x : ℝ) :
    paratlanGyok n x ^ n = x := by
  by_cases hx : 0 ≤ x
  · simp only [paratlanGyok, if_pos hx]
    exact gyok_pow hn hx
  · push_neg at hx
    have hx' : (0 : ℝ) ≤ -x := by linarith
    simp only [paratlanGyok, if_neg (not_le.mpr hx)]
    rw [hodd.neg_pow, gyok_pow hn hx', neg_neg]

/-- **5.7.9. Tétel (b) eset).** Mivel `y = x²ᵏ⁺¹` mindenütt folytonos, így inverze,
az `y = ²ᵏ⁺¹√x` függvény is mindenütt folytonos. -/
theorem folytonos_paratlanGyok {n : ℕ} (hn : n ≠ 0) (x₀ : ℝ) :
    CauchyFolytonos (paratlanGyok n) x₀ := by
  have hg : Continuous (gyok n) := Real.continuous_rpow_const (by positivity)
  have h2 : Continuous fun x : ℝ => -gyok n (-x) := (hg.comp continuous_neg).neg
  have hcont : Continuous (paratlanGyok n) :=
    Continuous.if_le hg h2 continuous_const continuous_id
      (fun x hx => by simp [gyok, ← hx, hn])
  exact (cauchyFolytonos_iff_continuousAt _ _).2 hcont.continuousAt

/-! ## 5.7.10. Negatív egész kitevőjű gyökfüggvények -/

/-- **5.7.10. Definíció.** `y = 1/ⁿ√x` a negatív egész kitevőjű gyökfüggvény
(ott értelmezve, ahol a jobb oldalnak van értelme). -/
noncomputable def gyokRecipr (n : ℕ) (x : ℝ) : ℝ := (gyok n x)⁻¹

theorem gyokRecipr_pos {n : ℕ} {x : ℝ} (hx : 0 < x) : 0 < gyokRecipr n x :=
  inv_pos.mpr (Real.rpow_pos_of_pos hx _)

/-- **5.7.10. a) eset.** Az `y = 1/ⁿ√x` függvény minden pozitív `x`-re értelmezve van és
ott folytonos.

*Bizonyítás.* `ⁿ√x` folytonos `x > 0`-ra, és ha egy függvény folytonos és nem nulla egy
pontban, akkor ott a reciproka is folytonos. -/
theorem folytonos_gyokRecipr (n : ℕ) {x₀ : ℝ} (hx₀ : 0 < x₀) :
    CauchyFolytonos (gyokRecipr n) x₀ := by
  refine (cauchyFolytonos_iff_continuousAt _ _).2 ?_
  exact ((cauchyFolytonos_iff_continuousAt _ _).1 (folytonos_gyok n hx₀)).inv₀
    (ne_of_gt (Real.rpow_pos_of_pos hx₀ _))

/-- **5.7.10. b) eset.** Páratlan `n` esetén az `y = -1/ⁿ√x` alakú függvény az origó
kivételével mindenütt értelmezve van és folytonos. -/
theorem folytonos_paratlanGyokRecipr {n : ℕ} (hn : n ≠ 0) (hodd : Odd n) {x₀ : ℝ}
    (hx₀ : x₀ ≠ 0) : CauchyFolytonos (fun x => (paratlanGyok n x)⁻¹) x₀ := by
  have hne : paratlanGyok n x₀ ≠ 0 := by
    intro h
    apply hx₀
    have := paratlanGyok_pow hn hodd x₀
    rw [h] at this
    simpa [zero_pow hn] using this.symm
  refine (cauchyFolytonos_iff_continuousAt _ _).2 ?_
  exact ((cauchyFolytonos_iff_continuousAt _ _).1 (folytonos_paratlanGyok hn x₀)).inv₀ hne

/-! ## 5.7.11. Törtkitevős hatványfüggvények -/

/-- **5.7.11. Definíció.** `y = x^(p/q) := ᵠ√(xᵖ)` (ahol a jobb oldalnak van értelme). -/
noncomputable def tortHatvany (p : ℤ) (q : ℕ) (x : ℝ) : ℝ := x ^ ((p : ℝ) / (q : ℝ))

/-- A törtkitevős hatvány valóban a `xᵖ` kifejezés `q`-adik gyöke. -/
theorem tortHatvany_eq_gyok (p : ℤ) {q : ℕ} {x : ℝ} (hx : 0 < x) :
    tortHatvany p q x = gyok q (x ^ p) := by
  rw [tortHatvany, gyok, ← Real.rpow_intCast x p, ← Real.rpow_mul hx.le, div_eq_mul_inv]

/-- **5.7.11.** A törtkitevős hatványfüggvények az értelmezési tartományuk minden belső
pontjában (azaz minden pozitív helyen) folytonosak. -/
theorem folytonos_tortHatvany (p : ℤ) (q : ℕ) {x₀ : ℝ} (hx₀ : 0 < x₀) :
    CauchyFolytonos (tortHatvany p q) x₀ :=
  (cauchyFolytonos_iff_continuousAt _ _).2
    (Real.continuousAt_rpow_const _ _ (Or.inl (ne_of_gt hx₀)))

/-- **5.7.11.** A törtkitevős hatványfüggvények minden pozitív `x`-re értelmezve vannak,
és pozitív értéket vesznek fel. -/
theorem tortHatvany_pos (p : ℤ) (q : ℕ) {x : ℝ} (hx : 0 < x) : 0 < tortHatvany p q x :=
  Real.rpow_pos_of_pos hx _

end Leindler.Ch05
