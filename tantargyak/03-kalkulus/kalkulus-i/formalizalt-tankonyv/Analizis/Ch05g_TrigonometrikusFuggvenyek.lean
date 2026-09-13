import Mathlib
import Analizis.Ch04a_SorozatokAlapok
import Analizis.Ch04b_SorozatokMuveletek
import Analizis.Ch05a_FuggvenyekAlapfogalmak
import Analizis.Ch05b_Folytonossag
import Analizis.Ch05e_AlgebraiFuggvenyek
import Analizis.Ch05f_ExponencialisLogaritmus

/-!
# Leindler László: Analízis — 5.11–5.13. pont

## Trigonometrikus, ciklometrikus és elemi függvények

Ez a fájl a könyv **5.11., 5.12. és 5.13. pontját** formalizálja.

* **5.11.** A `sin x`, `cos x`, `tg x`, `ctg x` függvények periodicitása, az
  **5.11.1. Definíció** (trigonometrikus függvény, trigonometrikus polinom), az
  **5.11.2. Tétel** (a `sin` és a `cos` mindenütt folytonos) és az **5.11.3. Tétel**
  (a `tg` az `x = (2k+1)π/2` pontok kivételével mindenütt folytonos).
  A könyv a `sin` és `cos` függvényt geometriailag (az egységsugarú kör segítségével)
  vezeti be; a formalizálásban a Mathlib `Real.sin`, `Real.cos` függvényeit használjuk,
  amelyek ugyanezeket a tulajdonságokat (addíciós tételek, periodicitás,
  `|sin x| ≤ |x|`) teljesítik. A folytonossági bizonyítás a könyv gondolatmenetét
  követi: előbb a `0` pontbeli folytonosság a Cauchy-féle definícióval, majd a
  `cos x = 1 - 2 sin²(x/2)` összefüggés, végül az addíciós tételek és a
  Heine-féle definíció.
* **5.12.** A ciklometrikus (inverz trigonometrikus) függvények: `arcsin`, `arccos`,
  `arctg`, `arcctg` — értelmezési tartományuk, értékkészletük, monotonitásuk és
  folytonosságuk, valamint az **5.12.1. Definíció** (transzcendens függvények).
* **5.13.** Az **5.13.1. Definíció**: az elemi függvények (algebrai és transzcendens
  függvények), néhány példával, továbbá a fejezet záró megjegyzésében szereplő
  hiperbolikus függvények definíciója és alaptulajdonságai.
-/

namespace Leindler.Ch05

open Set

/-! ## 5.11. Trigonometrikus függvények -/

/-- A `tg x = sin x / cos x` tangensfüggvény (ott értelmezve, ahol `cos x ≠ 0`). -/
noncomputable def tg (x : ℝ) : ℝ := Real.sin x / Real.cos x

/-- A `ctg x = cos x / sin x` kotangensfüggvény (ott értelmezve, ahol `sin x ≠ 0`). -/
noncomputable def ctg (x : ℝ) : ℝ := Real.cos x / Real.sin x

theorem tg_eq_tan (x : ℝ) : tg x = Real.tan x := (Real.tan_eq_sin_div_cos x).symm

/-- **5.11.** A definícióból következik, hogy a `sin x` függvény `2π` szerint periodikus. -/
theorem sin_periodikus (x : ℝ) : Real.sin (x + 2 * Real.pi) = Real.sin x :=
  Real.sin_add_two_pi x

/-- **5.11.** A `cos x` függvény `2π` szerint periodikus. -/
theorem cos_periodikus (x : ℝ) : Real.cos (x + 2 * Real.pi) = Real.cos x :=
  Real.cos_add_two_pi x

/-- **5.11.** A `tg x` függvény `π` szerint periodikus. -/
theorem tg_periodikus (x : ℝ) : tg (x + Real.pi) = tg x := by
  simp [tg, Real.sin_add_pi, Real.cos_add_pi, neg_div_neg_eq]

/-- **5.11.** A `ctg x` függvény `π` szerint periodikus. -/
theorem ctg_periodikus (x : ℝ) : ctg (x + Real.pi) = ctg x := by
  simp [ctg, Real.sin_add_pi, Real.cos_add_pi, neg_div_neg_eq]

/-- **5.11.1. Definíció (trigonometrikus polinom).** A trigonometrikus polinomok
általános alakja `a₀ + ∑_{k=1}^{n} (aₖ cos kx + bₖ sin kx)`. -/
noncomputable def trigPolinom (a b : ℕ → ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  a 0 + ∑ k ∈ Finset.Icc 1 n, (a k * Real.cos (k * x) + b k * Real.sin (k * x))

/-- **5.11.1. Definíció.** A fenti trigonometrikus polinom *`n`-edrendű*, ha
`aₙ² + bₙ² ≠ 0`. -/
def NedrenduTrigPolinom (a b : ℕ → ℝ) (n : ℕ) : Prop := a n ^ 2 + b n ^ 2 ≠ 0

/-- **5.11.2. Tétel (első lépés).** A `sin x` függvény az `x = 0` pontban folytonos.

*Bizonyítás.* Ha adott `ε > 0`, akkor legyen `δ := ε`. Ha `|x - 0| < δ`, akkor
(a könyv 5.12. ábrája szerinti elemi becsléssel) `|sin x| ≤ |x| < ε`, azaz a
Cauchy-féle definíció szerint a `sin` az `x = 0` pontban folytonos. -/
theorem sin_folytonos_nullaban : CauchyFolytonos Real.sin 0 := by
  intro ε hε
  refine ⟨ε, hε, fun x hx => ?_⟩
  rw [Real.sin_zero, sub_zero]
  calc |Real.sin x| ≤ |x| := Real.abs_sin_le_abs
    _ < ε := by simpa using hx

/-- A könyv bizonyításában használt `cos x = 1 - 2 sin²(x/2)` összefüggés. -/
theorem cos_eq_one_sub_two_sin_sq_half (x : ℝ) :
    Real.cos x = 1 - 2 * Real.sin (x / 2) ^ 2 := by
  have h := Real.cos_two_mul (x / 2)
  rw [show 2 * (x / 2) = x by ring] at h
  have h2 := Real.sin_sq_add_cos_sq (x / 2)
  linarith

/-- Konstans sorozat határértéke. -/
theorem hatarErtek_konstans (c : ℝ) : Ch04.HatarErtek (fun _ => c) c :=
  fun ε hε => ⟨0, fun n _ => by simpa using hε⟩

/-- **5.11.2. Tétel (második lépés).** A `cos x` függvény az `x = 0` pontban folytonos.

*Bizonyítás.* A `cos x = 1 - 2 sin²(x/2)` kapcsolat, az összetett függvényekre
vonatkozó folytonossági tételünk és a `sin` `0`-beli folytonossága szerint azonnal
adódik. -/
theorem cos_folytonos_nullaban : CauchyFolytonos Real.cos 0 := by
  rw [← heineFolytonos_iff_cauchyFolytonos]
  have hsin : HeineFolytonos Real.sin 0 :=
    (heineFolytonos_iff_cauchyFolytonos _ _).2 sin_folytonos_nullaban
  intro x hx
  have hhalf : Ch04.HatarErtek (fun n => x n / 2) 0 := by
    have := Ch04.hatarErtek_const_mul (2 : ℝ)⁻¹ hx
    simpa [div_eq_mul_inv, mul_comm] using this
  have hs : Ch04.HatarErtek (fun n => Real.sin (x n / 2)) 0 := by
    have := hsin (fun n => x n / 2) hhalf
    simpa using this
  have hsq : Ch04.HatarErtek (fun n => 2 * (Real.sin (x n / 2) * Real.sin (x n / 2))) 0 := by
    have := Ch04.hatarErtek_const_mul (2 : ℝ) (Ch04.hatarErtek_mul hs hs)
    simpa using this
  have hres := Ch04.hatarErtek_sub (hatarErtek_konstans (1 : ℝ)) hsq
  have hfun : ∀ y : ℝ, Real.cos y = 1 - 2 * (Real.sin (y / 2) * Real.sin (y / 2)) := by
    intro y; rw [cos_eq_one_sub_two_sin_sq_half y]; ring
  simp only [hfun]
  simpa using hres

/-- **5.11.2. Tétel.** A `sin x` függvény mindenütt folytonos.

*Bizonyítás.* Ha `xₙ → x₀`, akkor `xₙ = x₀ + hₙ` alakban írható, ahol `hₙ → 0`, így
az addíciós tétel szerint
`sin xₙ = sin x₀ cos hₙ + cos x₀ sin hₙ → sin x₀ · 1 + cos x₀ · 0 = sin x₀`,
tehát a Heine-féle folytonossági definíció szerint a `sin` folytonos. -/
theorem sin_folytonos (x₀ : ℝ) : CauchyFolytonos Real.sin x₀ := by
  rw [← heineFolytonos_iff_cauchyFolytonos]
  have hsin0 : HeineFolytonos Real.sin 0 :=
    (heineFolytonos_iff_cauchyFolytonos _ _).2 sin_folytonos_nullaban
  have hcos0 : HeineFolytonos Real.cos 0 :=
    (heineFolytonos_iff_cauchyFolytonos _ _).2 cos_folytonos_nullaban
  intro x hx
  have hh : Ch04.HatarErtek (fun n => x n - x₀) 0 := by
    have := Ch04.hatarErtek_sub hx (hatarErtek_konstans x₀)
    simpa using this
  have hc : Ch04.HatarErtek (fun n => Real.cos (x n - x₀)) 1 := by
    have := hcos0 (fun n => x n - x₀) hh
    simpa using this
  have hs : Ch04.HatarErtek (fun n => Real.sin (x n - x₀)) 0 := by
    have := hsin0 (fun n => x n - x₀) hh
    simpa using this
  have hres := Ch04.hatarErtek_add (Ch04.hatarErtek_const_mul (Real.sin x₀) hc)
    (Ch04.hatarErtek_const_mul (Real.cos x₀) hs)
  have hfun : ∀ n, Real.sin (x n) =
      Real.sin x₀ * Real.cos (x n - x₀) + Real.cos x₀ * Real.sin (x n - x₀) := by
    intro n
    rw [← Real.sin_add]
    ring_nf
  simp only [hfun]
  simpa using hres

/-- **5.11.2. Tétel.** A `cos x` függvény mindenütt folytonos.

*Bizonyítás.* Az előzővel azonos módon, `cos xₙ = cos (x₀ + hₙ)
= cos x₀ cos hₙ - sin x₀ sin hₙ → cos x₀ · 1 - sin x₀ · 0 = cos x₀`. -/
theorem cos_folytonos (x₀ : ℝ) : CauchyFolytonos Real.cos x₀ := by
  rw [← heineFolytonos_iff_cauchyFolytonos]
  have hsin0 : HeineFolytonos Real.sin 0 :=
    (heineFolytonos_iff_cauchyFolytonos _ _).2 sin_folytonos_nullaban
  have hcos0 : HeineFolytonos Real.cos 0 :=
    (heineFolytonos_iff_cauchyFolytonos _ _).2 cos_folytonos_nullaban
  intro x hx
  have hh : Ch04.HatarErtek (fun n => x n - x₀) 0 := by
    have := Ch04.hatarErtek_sub hx (hatarErtek_konstans x₀)
    simpa using this
  have hc : Ch04.HatarErtek (fun n => Real.cos (x n - x₀)) 1 := by
    have := hcos0 (fun n => x n - x₀) hh
    simpa using this
  have hs : Ch04.HatarErtek (fun n => Real.sin (x n - x₀)) 0 := by
    have := hsin0 (fun n => x n - x₀) hh
    simpa using this
  have hres := Ch04.hatarErtek_sub (Ch04.hatarErtek_const_mul (Real.cos x₀) hc)
    (Ch04.hatarErtek_const_mul (Real.sin x₀) hs)
  have hfun : ∀ n, Real.cos (x n) =
      Real.cos x₀ * Real.cos (x n - x₀) - Real.sin x₀ * Real.sin (x n - x₀) := by
    intro n
    rw [← Real.cos_add]
    ring_nf
  simp only [hfun]
  simpa using hres

/-- **5.11.2. Tétel következménye.** Bármely trigonometrikus polinom mindenütt
folytonos. -/
theorem trigPolinom_folytonos (a b : ℕ → ℝ) (n : ℕ) (x₀ : ℝ) :
    CauchyFolytonos (trigPolinom a b n) x₀ := by
  rw [cauchyFolytonos_iff_continuousAt]
  refine Continuous.continuousAt ?_
  refine continuous_const.add (continuous_finset_sum _ fun k _ => ?_)
  exact (continuous_const.mul (Real.continuous_cos.comp (continuous_const.mul continuous_id))).add
    (continuous_const.mul (Real.continuous_sin.comp (continuous_const.mul continuous_id)))

/-- **5.11.3. Tétel.** A `tg x` függvény az `x = (2k+1)π/2` (`k = 0, ±1, ±2, …`) pontok
kivételével mindenütt folytonos.

*Bizonyítás.* A fentiekből a folytonos függvények hányadosára vonatkozó tétel
felhasználásával adódik. -/
theorem tg_folytonos {x₀ : ℝ} (h : ∀ k : ℤ, x₀ ≠ (2 * k + 1) * Real.pi / 2) :
    CauchyFolytonos tg x₀ := by
  have hcos : Real.cos x₀ ≠ 0 := Real.cos_ne_zero_iff.2 h
  rw [← heineFolytonos_iff_cauchyFolytonos]
  exact folytonos_div ((heineFolytonos_iff_cauchyFolytonos _ _).2 (sin_folytonos x₀))
    ((heineFolytonos_iff_cauchyFolytonos _ _).2 (cos_folytonos x₀)) hcos

/-- **5.11.3. Tétel (kotangens).** A `ctg x` függvény az `x = kπ` pontok kivételével
mindenütt folytonos. -/
theorem ctg_folytonos {x₀ : ℝ} (h : ∀ k : ℤ, x₀ ≠ k * Real.pi) :
    CauchyFolytonos ctg x₀ := by
  have hsin : Real.sin x₀ ≠ 0 := Real.sin_ne_zero_iff.2 fun k hk => h k hk.symm
  rw [← heineFolytonos_iff_cauchyFolytonos]
  exact folytonos_div ((heineFolytonos_iff_cauchyFolytonos _ _).2 (cos_folytonos x₀))
    ((heineFolytonos_iff_cauchyFolytonos _ _).2 (sin_folytonos x₀)) hsin

/-! ## 5.12. Ciklometrikus függvények -/

/-- **5.12/4.** Az `arcctg x := π/2 - arctg x` függvény: az a `0` és `π` közötti szög,
amelynek kotangense `x`. -/
noncomputable def arcctg (x : ℝ) : ℝ := Real.pi / 2 - Real.arctan x

/-! ### 1. Az `y = arcsin x` függvény -/

/-- **5.12/1.** `arcsin x` az a `-π/2` és `π/2` közötti szög, amelynek szinusza `x`
(`x ∈ [-1,1]`). -/
theorem sin_arcsin_eq {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) : Real.sin (Real.arcsin x) = x :=
  Real.sin_arcsin hx.1 hx.2

/-- **5.12/1.** Az `arcsin` értékkészlete a `[-π/2, π/2]` intervallum. -/
theorem arcsin_ertekkeszlet :
    Ertekkeszlet Real.arcsin (Icc (-1) 1) = Icc (-(Real.pi / 2)) (Real.pi / 2) := by
  apply Subset.antisymm
  · rintro _ ⟨y, _, rfl⟩
    exact Real.arcsin_mem_Icc y
  · intro y hy
    refine ⟨Real.sin y, ⟨Real.neg_one_le_sin y, Real.sin_le_one y⟩, ?_⟩
    exact Real.arcsin_sin hy.1 hy.2

/-- **5.12/1.** Mivel `sin x` a `[-π/2, π/2]` intervallumon szigorúan növekedő és
folytonos, az inverz függvényre vonatkozó 5.6.2. Tétel szerint az `arcsin x` a
`[-1,1]` intervallumon szigorúan növekedő. -/
theorem arcsin_szigNovekedo : SzigNovekedo Real.arcsin (Icc (-1) 1) :=
  (szigNovekedo_iff_strictMonoOn).2 Real.strictMonoOn_arcsin

/-- **5.12/1.** Az `arcsin x` függvény folytonos. -/
theorem arcsin_folytonos (x₀ : ℝ) : CauchyFolytonos Real.arcsin x₀ :=
  (cauchyFolytonos_iff_continuousAt _ _).2 Real.continuous_arcsin.continuousAt

/-! ### 2. Az `y = arccos x` függvény -/

/-- **5.12/2.** `arccos x` az a `0` és `π` közötti szög, amelynek koszinusza `x`. -/
theorem cos_arccos_eq {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) : Real.cos (Real.arccos x) = x :=
  Real.cos_arccos hx.1 hx.2

/-- **5.12/2.** Az `arccos` értékkészlete a `[0, π]` intervallum. -/
theorem arccos_ertekkeszlet :
    Ertekkeszlet Real.arccos (Icc (-1) 1) = Icc 0 Real.pi := by
  apply Subset.antisymm
  · rintro _ ⟨y, _, rfl⟩
    exact ⟨Real.arccos_nonneg y, Real.arccos_le_pi y⟩
  · intro y hy
    refine ⟨Real.cos y, ⟨Real.neg_one_le_cos y, Real.cos_le_one y⟩, ?_⟩
    exact Real.arccos_cos hy.1 hy.2

/-- **5.12/2.** Az `y = arccos x` függvény (szigorúan) monoton csökkenő. -/
theorem arccos_szigCsokkeno : SzigCsokkeno Real.arccos (Icc (-1) 1) := by
  intro x₁ h₁ x₂ h₂ h
  exact Real.strictAntiOn_arccos h₁ h₂ h

/-- **5.12/2.** Az `arccos x` függvény folytonos. -/
theorem arccos_folytonos (x₀ : ℝ) : CauchyFolytonos Real.arccos x₀ :=
  (cauchyFolytonos_iff_continuousAt _ _).2 Real.continuous_arccos.continuousAt

/-! ### 3. Az `y = arctg x` függvény -/

/-- **5.12/3.** `arctg x` az a `-π/2` és `π/2` közötti szög, amelyre `tg (arctg x) = x`;
értelmezési tartománya minden valós szám. -/
theorem tg_arctan_eq (x : ℝ) : tg (Real.arctan x) = x := by
  rw [tg_eq_tan, Real.tan_arctan]

/-- **5.12/3.** Az `arctg` értékkészlete a `(-π/2, π/2)` nyílt intervallum. -/
theorem arctan_ertekkeszlet :
    Ertekkeszlet Real.arctan univ = Ioo (-(Real.pi / 2)) (Real.pi / 2) := by
  rw [Ertekkeszlet, image_univ, Real.range_arctan]

/-- **5.12/3.** Az `arctg x` függvény szigorúan növekedő. -/
theorem arctan_szigNovekedo : SzigNovekedo Real.arctan univ :=
  fun _ _ _ _ h => Real.arctan_strictMono h

/-- **5.12/3.** Az `arctg x` függvény mindenütt folytonos. -/
theorem arctan_folytonos (x₀ : ℝ) : CauchyFolytonos Real.arctan x₀ :=
  (cauchyFolytonos_iff_continuousAt _ _).2 Real.continuous_arctan.continuousAt

/-! ### 4. Az `y = arcctg x` függvény -/

/-- **5.12/4.** `arcctg x` az a `0` és `π` közötti szög, amelyre `ctg (arcctg x) = x`. -/
theorem ctg_arcctg (x : ℝ) : ctg (arcctg x) = x := by
  rw [ctg, arcctg, Real.cos_pi_div_two_sub, Real.sin_pi_div_two_sub,
    ← Real.tan_eq_sin_div_cos, Real.tan_arctan]

/-- **5.12/4.** Az `arcctg` értelmezési tartománya a `(-∞, ∞)` intervallum,
értékkészlete a `(0, π)` intervallum. -/
theorem arcctg_ertekkeszlet : Ertekkeszlet arcctg univ = Ioo 0 Real.pi := by
  apply Subset.antisymm
  · rintro _ ⟨y, -, rfl⟩
    constructor
    · have := Real.arctan_lt_pi_div_two y
      simp only [arcctg]; linarith
    · have := Real.neg_pi_div_two_lt_arctan y
      simp only [arcctg]; linarith
  · intro y hy
    refine ⟨Real.tan (Real.pi / 2 - y), mem_univ _, ?_⟩
    rw [arcctg, Real.arctan_tan (by linarith [hy.2]) (by linarith [hy.1])]
    ring

/-- **5.12/4.** Az `arcctg x` szigorúan csökkenő függvény. -/
theorem arcctg_szigCsokkeno : SzigCsokkeno arcctg univ := by
  intro x₁ _ x₂ _ h
  have := Real.arctan_strictMono h
  simp only [arcctg]
  linarith

/-- **5.12/4.** Az `arcctg x` mindenütt folytonos függvény. -/
theorem arcctg_folytonos (x₀ : ℝ) : CauchyFolytonos arcctg x₀ :=
  (cauchyFolytonos_iff_continuousAt _ _).2
    (continuousAt_const.sub Real.continuous_arctan.continuousAt)

/-! ## 5.12.1. Definíció: transzcendens függvények -/

/-- **5.12.1. Definíció.** Az irracionális kitevőjű hatványfüggvényt, az exponenciális,
a logaritmus-, a trigonometrikus és a ciklometrikus függvényeket, valamint az ezekből
összetett függvényeket közös néven *transzcendens függvényeknek* nevezzük. -/
inductive TranszcendensFuggveny : (ℝ → ℝ) → Prop
  | irrHatvany (al : ℝ) : TranszcendensFuggveny (irrHatvany al)
  | exponencialis (a : ℝ) : TranszcendensFuggveny (fun x => a ^ x)
  | logaritmus (a : ℝ) : TranszcendensFuggveny (logA a)
  | sin : TranszcendensFuggveny Real.sin
  | cos : TranszcendensFuggveny Real.cos
  | tg : TranszcendensFuggveny tg
  | ctg : TranszcendensFuggveny ctg
  | arcsin : TranszcendensFuggveny Real.arcsin
  | arccos : TranszcendensFuggveny Real.arccos
  | arctg : TranszcendensFuggveny Real.arctan
  | arcctg : TranszcendensFuggveny arcctg
  | osszetett {f g : ℝ → ℝ} : TranszcendensFuggveny f → TranszcendensFuggveny g →
      TranszcendensFuggveny (fun x => f (g x))

/-! ## 5.13. Elemi függvények -/

/-- **5.13.1. Definíció.** Az elemi függvények körébe az algebrai és a transzcendens
függvényeket számítjuk: az elemi függvények olyan függvények, amelyek olyan képlettel
adhatók meg, amely a független változóból és konstansokból véges sok összeadás,
kivonás, szorzás, osztás, hatványozás, gyökvonás, logaritmus, trigonometrikus és
ciklometrikus függvény segítségével felírható. -/
inductive ElemiFuggveny : (ℝ → ℝ) → Prop
  /-- konstans függvény -/
  | konstans (c : ℝ) : ElemiFuggveny (fun _ => c)
  /-- a független változó -/
  | valtozo : ElemiFuggveny (fun x => x)
  | add {f g : ℝ → ℝ} : ElemiFuggveny f → ElemiFuggveny g → ElemiFuggveny (fun x => f x + g x)
  | sub {f g : ℝ → ℝ} : ElemiFuggveny f → ElemiFuggveny g → ElemiFuggveny (fun x => f x - g x)
  | mul {f g : ℝ → ℝ} : ElemiFuggveny f → ElemiFuggveny g → ElemiFuggveny (fun x => f x * g x)
  | div {f g : ℝ → ℝ} : ElemiFuggveny f → ElemiFuggveny g → ElemiFuggveny (fun x => f x / g x)
  /-- hatványozás (tetszőleges valós kitevővel) -/
  | hatvany {f : ℝ → ℝ} (al : ℝ) : ElemiFuggveny f → ElemiFuggveny (fun x => f x ^ al)
  /-- gyökvonás -/
  | gyokvonas {f : ℝ → ℝ} (n : ℕ) : ElemiFuggveny f → ElemiFuggveny (fun x => gyok n (f x))
  /-- logaritmus -/
  | logaritmus {f : ℝ → ℝ} (a : ℝ) : ElemiFuggveny f → ElemiFuggveny (fun x => logA a (f x))
  /-- trigonometrikus és ciklometrikus függvények -/
  | transzcendens {f g : ℝ → ℝ} : TranszcendensFuggveny f → ElemiFuggveny g →
      ElemiFuggveny (fun x => f (g x))

/-- **5.13.1.** Példa: `y = x · sin (x+1)` elemi függvény. -/
theorem elemi_pelda_1 : ElemiFuggveny (fun x => x * Real.sin (x + 1)) :=
  ElemiFuggveny.mul ElemiFuggveny.valtozo
    (ElemiFuggveny.transzcendens TranszcendensFuggveny.sin
      (ElemiFuggveny.add ElemiFuggveny.valtozo (ElemiFuggveny.konstans 1)))

/-- **5.13.1.** Példa: `y = (x² + 1)·³√x + 3` elemi függvény. -/
theorem elemi_pelda_2 : ElemiFuggveny (fun x => (x ^ (2 : ℝ) + 1) * gyok 3 x + 3) :=
  ElemiFuggveny.add
    (ElemiFuggveny.mul
      (ElemiFuggveny.add (ElemiFuggveny.hatvany 2 ElemiFuggveny.valtozo)
        (ElemiFuggveny.konstans 1))
      (ElemiFuggveny.gyokvonas 3 ElemiFuggveny.valtozo))
    (ElemiFuggveny.konstans 3)

/-- **5.13.1.** Példa: `y = log (arccos (x·√x) + 1)` elemi függvény. -/
theorem elemi_pelda_3 :
    ElemiFuggveny (fun x => logA 10 (Real.arccos (x * gyok 2 x) + 1)) :=
  ElemiFuggveny.logaritmus 10
    (ElemiFuggveny.add
      (ElemiFuggveny.transzcendens TranszcendensFuggveny.arccos
        (ElemiFuggveny.mul ElemiFuggveny.valtozo
          (ElemiFuggveny.gyokvonas 2 ElemiFuggveny.valtozo)))
      (ElemiFuggveny.konstans 1))

/-! ### Megjegyzés: hiperbolikus függvények

A könyv záró megjegyzése szerint a hiperbolikus függvényekkel — mivel azok az `eˣ`
függvényből egyszerű módon állnak elő — részletesen nem foglalkozunk, csupán
definiáljuk azokat és néhány tulajdonságukat felsoroljuk. -/

/-- `sh x := (eˣ - e⁻ˣ)/2`, a hiperbolikus szinuszfüggvény. -/
noncomputable def sh (x : ℝ) : ℝ := (Real.exp x - Real.exp (-x)) / 2

/-- `ch x := (eˣ + e⁻ˣ)/2`, a hiperbolikus koszinuszfüggvény. -/
noncomputable def ch (x : ℝ) : ℝ := (Real.exp x + Real.exp (-x)) / 2

/-- `th x := (eˣ - e⁻ˣ)/(eˣ + e⁻ˣ)`, a hiperbolikus tangensfüggvény. -/
noncomputable def th (x : ℝ) : ℝ := (Real.exp x - Real.exp (-x)) / (Real.exp x + Real.exp (-x))

/-- `cth x := (eˣ + e⁻ˣ)/(eˣ - e⁻ˣ)`, a hiperbolikus kotangensfüggvény (az origó
kivételével mindenütt értelmezve). -/
noncomputable def cth (x : ℝ) : ℝ := (Real.exp x + Real.exp (-x)) / (Real.exp x - Real.exp (-x))

theorem sh_eq_sinh (x : ℝ) : sh x = Real.sinh x := by rw [Real.sinh_eq, sh]

theorem ch_eq_cosh (x : ℝ) : ch x = Real.cosh x := by rw [Real.cosh_eq, ch]

/-- A `th` a `sh` és a `ch` hányadosa. -/
theorem th_eq_sh_div_ch (x : ℝ) : th x = sh x / ch x := by
  rw [th, sh, ch, div_div_div_cancel_right₀]
  norm_num

/-- A `cth` a `ch` és a `sh` hányadosa. -/
theorem cth_eq_ch_div_sh (x : ℝ) : cth x = ch x / sh x := by
  rw [cth, sh, ch, div_div_div_cancel_right₀]
  norm_num

/-- A `ch x` sehol sem tűnik el, ezért a `th` mindenütt értelmezve van. -/
theorem ch_pos (x : ℝ) : 0 < ch x := by
  rw [ch]; positivity

/-- A `sh x` csak az origóban tűnik el, ezért a `cth` az origó kivételével mindenütt
értelmezve van. -/
theorem sh_eq_zero_iff {x : ℝ} : sh x = 0 ↔ x = 0 := by
  rw [sh_eq_sinh, Real.sinh_eq_zero]

theorem sh_zero : sh 0 = 0 := by rw [sh]; simp

theorem ch_zero : ch 0 = 1 := by rw [ch]; norm_num

theorem th_zero : th 0 = 0 := by rw [th]; simp

theorem sh_neg (x : ℝ) : sh (-x) = -sh x := by simp only [sh_eq_sinh, Real.sinh_neg]

theorem ch_neg (x : ℝ) : ch (-x) = ch x := by simp only [ch_eq_cosh, Real.cosh_neg]

theorem sh_add (x y : ℝ) : sh (x + y) = sh x * ch y + ch x * sh y := by
  simp only [sh_eq_sinh, ch_eq_cosh, Real.sinh_add]

theorem ch_add (x y : ℝ) : ch (x + y) = ch x * ch y + sh x * sh y := by
  simp only [sh_eq_sinh, ch_eq_cosh, Real.cosh_add]

theorem ch_sq_sub_sh_sq (x : ℝ) : ch x ^ 2 - sh x ^ 2 = 1 := by
  simp only [sh_eq_sinh, ch_eq_cosh]
  exact Real.cosh_sq_sub_sinh_sq x

theorem sh_two_mul (x : ℝ) : sh (2 * x) = 2 * sh x * ch x := by
  simp only [sh_eq_sinh, ch_eq_cosh, Real.sinh_two_mul]

theorem ch_two_mul (x : ℝ) : ch (2 * x) = ch x ^ 2 + sh x ^ 2 := by
  simp only [sh_eq_sinh, ch_eq_cosh]
  rw [Real.cosh_two_mul]

theorem th_eq_tanh (x : ℝ) : th x = Real.tanh x := by
  rw [th_eq_sh_div_ch, sh_eq_sinh, ch_eq_cosh, ← Real.tanh_eq_sinh_div_cosh]

/-! ### Megjegyzés: area (inverz hiperbolikus) függvények

A könyv megjegyzése szerint az `sh x` függvény inverze mindenhol, a `ch x`-é az
`[1, ∞)`, a `th x`-é a `(-1, 1)`, a `cth x`-é pedig az `(1, ∞)` intervallumon
definiálható; ezeket az inverzfüggvényeket rendre `arsh x`, `arch x`, `arth x`
és `arcth x` jelöli. -/

/-- Az `arsh` (area szinusz hiperbolikusz) függvény: az `sh` inverze `ℝ`-en. -/
noncomputable def arsh (x : ℝ) : ℝ := Real.arsinh x

/-- Az `arch` (area koszinusz hiperbolikusz) függvény: a `ch` inverze az `[1, ∞)`
intervallumon (értékkészlete a `[0, ∞)`). -/
noncomputable def arch (x : ℝ) : ℝ := Real.arcosh x

/-- Az `arth` (area tangens hiperbolikusz) függvény: a `th` inverze a `(-1, 1)`
intervallumon. -/
noncomputable def arth (x : ℝ) : ℝ := Real.artanh x

/-- Az `arcth` (area kotangens hiperbolikusz) függvény: a `cth` inverze az `(1, ∞)`
intervallumon. -/
noncomputable def arcth (x : ℝ) : ℝ := Real.artanh (1 / x)

theorem sh_arsh (x : ℝ) : sh (arsh x) = x := by
  rw [sh_eq_sinh, arsh, Real.sinh_arsinh]

theorem arsh_sh (x : ℝ) : arsh (sh x) = x := by
  rw [sh_eq_sinh, arsh, Real.arsinh_sinh]

theorem ch_arch {x : ℝ} (hx : 1 ≤ x) : ch (arch x) = x := by
  rw [ch_eq_cosh, arch, Real.cosh_arcosh hx]

theorem arch_ch {x : ℝ} (hx : 0 ≤ x) : arch (ch x) = x := by
  rw [ch_eq_cosh, arch, Real.arcosh_cosh hx]

theorem th_arth {x : ℝ} (hx : x ∈ Ioo (-1 : ℝ) 1) : th (arth x) = x := by
  rw [th_eq_tanh, arth, Real.tanh_artanh hx]

theorem arth_th (x : ℝ) : arth (th x) = x := by
  rw [th_eq_tanh, arth, Real.artanh_tanh]

theorem cth_arcth {x : ℝ} (hx : 1 < x) : cth (arcth x) = x := by
  have hx0 : 0 < x := lt_trans zero_lt_one hx
  have h1 : 1 / x ∈ Ioo (-1 : ℝ) 1 := by
    constructor
    · have : 0 < 1 / x := by positivity
      linarith
    · rw [div_lt_one hx0]; exact hx
  have hth : th (arcth x) = 1 / x := by
    rw [th_eq_tanh, arcth, Real.tanh_artanh h1]
  have hchpos := ch_pos (arcth x)
  have hsh : sh (arcth x) = ch (arcth x) / x := by
    rw [th_eq_sh_div_ch] at hth
    field_simp at hth ⊢
    linarith
  rw [cth_eq_ch_div_sh, hsh, div_div_eq_mul_div]
  field_simp

end Leindler.Ch05
