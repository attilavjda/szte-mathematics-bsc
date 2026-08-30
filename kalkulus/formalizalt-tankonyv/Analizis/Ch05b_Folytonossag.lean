import Mathlib
import Analizis.Ch04a_SorozatokAlapok
import Analizis.Ch04b_SorozatokMuveletek

/-!
# Leindler László: Analízis — 5. fejezet (folytatás)

## 5.2–5.6. Folytonos függvények

Ez a fájl a folytonosság Heine- és Cauchy-féle definícióját, ezek ekvivalenciáját
(5.2.3. Tétel), a féloldali és félig folytonosságot (5.3), az intervallumon való
és egyenletes folytonosságot (5.4), az összetett függvény folytonosságát (5.5),
valamint az inverz függvény létezésére és folytonosságára vonatkozó tételeket
(5.6) tartalmazza.

A sorozatokra vonatkozó fogalmakat a 4. fejezet formalizációjából
(`Leindler.Ch04`) vesszük át, így a Heine-féle definíció szó szerint a könyv
sorozat-határérték fogalmára épül.
-/

namespace Leindler.Ch05

open Set Leindler

/-! ## 5.2. Folytonos függvények -/

/-- **5.2.1. Definíció (Heine).** Az `f` függvény folytonos az `x₀` pontban, ha
minden olyan `xₙ` sorozatra, amely `x₀`-hoz tart, az `f(xₙ)` függvényértékek
sorozata `f(x₀)`-hoz tart. -/
def HeineFolytonos (f : ℝ → ℝ) (x₀ : ℝ) : Prop :=
  ∀ x : Ch04.Sorozat, Ch04.HatarErtek x x₀ → Ch04.HatarErtek (fun n => f (x n)) (f x₀)

/-- **5.2.2. Definíció (Cauchy).** Az `f` függvény folytonos az `x₀` pontban, ha
bármely `ε > 0`-hoz megadható olyan `δ = δ(ε, x₀) > 0`, hogy ha `|x - x₀| < δ`,
akkor `|f(x) - f(x₀)| < ε`. -/
def CauchyFolytonos (f : ℝ → ℝ) (x₀ : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x : ℝ, |x - x₀| < δ → |f x - f x₀| < ε

/-- A Cauchy-féle folytonossági definíció tagadása „pozitív formában” (a könyv
5.2.3. Tételének bizonyításában részletesen kifejtett lépés):

*Van olyan `ε₀ > 0`, hogy bárhogyan is adunk meg `δ > 0`-t, mindig lesz olyan `x*`,
hogy bár `|x* - x₀| < δ`, mégis `|f(x*) - f(x₀)| ≥ ε₀`.* -/
theorem nem_cauchyFolytonos_iff (f : ℝ → ℝ) (x₀ : ℝ) :
    ¬ CauchyFolytonos f x₀ ↔
      ∃ ε₀ > 0, ∀ δ > 0, ∃ x : ℝ, |x - x₀| < δ ∧ ε₀ ≤ |f x - f x₀| := by
  unfold CauchyFolytonos
  push_neg
  rfl

/-- **5.2.3. Tétel.** A Heine-féle és a Cauchy-féle folytonossági definíció ekvivalens.

*Bizonyítás (a könyv gondolatmenete).*

*Heine ⇒ Cauchy* (indirekt). Ha `f` nem folytonos Cauchy-értelemben, akkor a fenti
tagadás szerint van `ε₀ > 0`, hogy minden `δ > 0`-hoz van „rossz” pont. Adjuk `δ`-nak
rendre az `1, 1/2, 1/3, …, 1/n, …` értékeket; a `δ = 1/n`-hez tartozó pontot jelöljük
`xₙ`-nel. Ekkor `|xₙ - x₀| < 1/n`, tehát `xₙ → x₀`, így a Heine-féle definíció
szerint `f(xₙ) → f(x₀)`; ez viszont ellentmond annak, hogy `|f(xₙ) - f(x₀)| ≥ ε₀`.

*Cauchy ⇒ Heine* (direkt). Legyen `ε > 0` tetszőleges és `xₙ → x₀`. A Cauchy-féle
definíció szerint van `δ(ε) > 0` a kívánt tulajdonsággal, és mivel `xₙ → x₀`, ehhez
a `δ`-hoz van olyan `ν`, hogy `n > ν` esetén `|xₙ - x₀| < δ`; ilyen `xₙ`-ekre pedig
`|f(xₙ) - f(x₀)| < ε`. -/
theorem heineFolytonos_iff_cauchyFolytonos (f : ℝ → ℝ) (x₀ : ℝ) :
    HeineFolytonos f x₀ ↔ CauchyFolytonos f x₀ := by
  constructor
  · intro hHeine
    by_contra hC
    obtain ⟨ε₀, hε₀, hbad⟩ := (nem_cauchyFolytonos_iff f x₀).1 hC
    -- a `δ = 1/(n+1)` választással kapott „rossz” pontok sorozata
    choose x hx hfx using fun n : ℕ => hbad (1 / (n + 1 : ℝ)) (by positivity)
    have hxlim : Ch04.HatarErtek x x₀ := by
      intro ε hε
      obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
      refine ⟨N, fun n hn => ?_⟩
      have h1 : (1 : ℝ) / ε < n := lt_of_lt_of_le hN (by exact_mod_cast hn.le)
      have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have : 1 / ((n : ℝ) + 1) < ε := by
        rw [div_lt_iff₀ hn1]
        rw [div_lt_iff₀ hε] at h1
        nlinarith
      exact lt_of_lt_of_le (hx n) this.le
    have := hHeine x hxlim ε₀ hε₀
    obtain ⟨N, hN⟩ := this
    exact absurd (hN (N + 1) (by omega)) (not_lt.2 (hfx (N + 1)))
  · intro hCauchy x hx ε hε
    obtain ⟨δ, hδ, hδp⟩ := hCauchy ε hε
    obtain ⟨N, hN⟩ := hx δ hδ
    exact ⟨N, fun n hn => hδp (x n) (hN n hn)⟩

/-- A könyv (Cauchy-féle) folytonossági fogalma megegyezik a Mathlib
`ContinuousAt` fogalmával. -/
theorem cauchyFolytonos_iff_continuousAt (f : ℝ → ℝ) (x₀ : ℝ) :
    CauchyFolytonos f x₀ ↔ ContinuousAt f x₀ := by
  rw [Metric.continuousAt_iff]
  constructor
  · intro h ε hε
    obtain ⟨δ, hδ, hδp⟩ := h ε hε
    exact ⟨δ, hδ, fun {x} hx => by
      simpa [Real.dist_eq] using hδp x (by simpa [Real.dist_eq] using hx)⟩
  · intro h ε hε
    obtain ⟨δ, hδ, hδp⟩ := h ε hε
    exact ⟨δ, hδ, fun x hx => by
      simpa [Real.dist_eq] using hδp (by simpa [Real.dist_eq] using hx)⟩

/-! ## 5.3. Bal oldali és jobb oldali folytonosság -/

/-- **5.3.1. Definíció.** Az `f` függvény `x₀`-ban *balról folytonos*, ha bármely
`ε > 0`-hoz van olyan `δ > 0`, hogy ha `x < x₀` és `|x - x₀| < δ`, akkor
`|f(x) - f(x₀)| < ε`. -/
def BalrolFolytonos (f : ℝ → ℝ) (x₀ : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x : ℝ, x < x₀ → |x - x₀| < δ → |f x - f x₀| < ε

/-- **5.3.1. Definíció.** Az `f` függvény `x₀`-ban *jobbról folytonos*. -/
def JobbrolFolytonos (f : ℝ → ℝ) (x₀ : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x : ℝ, x₀ < x → |x - x₀| < δ → |f x - f x₀| < ε

/-- **5.3.2. Definíció (Heine).** Az `f` függvény `x₀`-ban balról folytonos, ha
bármely olyan `x₀`-hoz konvergáló sorozatra, amelynek tagjaira `xₙ < x₀`,
`f(xₙ) → f(x₀)`. -/
def HeineBalrolFolytonos (f : ℝ → ℝ) (x₀ : ℝ) : Prop :=
  ∀ x : Ch04.Sorozat, (∀ n, x n < x₀) → Ch04.HatarErtek x x₀ →
    Ch04.HatarErtek (fun n => f (x n)) (f x₀)

/-- **5.3.3. Tétel.** A féloldali folytonosság két definíciója is ekvivalens.

*Bizonyítás.* A bizonyítás ugyanúgy történik, mint a folytonosság esetén
(5.2.3. Tétel): Heine ⇒ Cauchy indirekt, a `δ = 1/n` választással kapott bal oldali
„rossz” pontok sorozatával; Cauchy ⇒ Heine pedig direkt módon. -/
theorem heineBalrol_iff_balrolFolytonos (f : ℝ → ℝ) (x₀ : ℝ) :
    HeineBalrolFolytonos f x₀ ↔ BalrolFolytonos f x₀ := by
  constructor
  · intro hHeine
    by_contra hC
    unfold BalrolFolytonos at hC
    push_neg at hC
    obtain ⟨ε₀, hε₀, hbad⟩ := hC
    choose x hxlt hxd hfx using fun n : ℕ => hbad (1 / (n + 1 : ℝ)) (by positivity)
    have hxlim : Ch04.HatarErtek x x₀ := by
      intro ε hε
      obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
      refine ⟨N, fun n hn => ?_⟩
      have h1 : (1 : ℝ) / ε < n := lt_of_lt_of_le hN (by exact_mod_cast hn.le)
      have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have hlt : 1 / ((n : ℝ) + 1) < ε := by
        rw [div_lt_iff₀ hn1]
        rw [div_lt_iff₀ hε] at h1
        nlinarith
      exact lt_of_lt_of_le (hxd n) hlt.le
    obtain ⟨N, hN⟩ := hHeine x hxlt hxlim ε₀ hε₀
    exact absurd (hN (N + 1) (by omega)) (not_lt.2 (hfx (N + 1)))
  · intro hC x hxlt hx ε hε
    obtain ⟨δ, hδ, hδp⟩ := hC ε hε
    obtain ⟨N, hN⟩ := hx δ hδ
    exact ⟨N, fun n hn => hδp (x n) (hxlt n) (hN n hn)⟩

/-- **5.3.4. Tétel.** Az `f` függvény egy `x₀` pontban akkor és csak akkor folytonos,
ha `x₀`-ban balról és jobbról is folytonos.

*Bizonyítás.* Mindkét irányban egyszerű: a folytonosságból a féloldali folytonosságok
nyilvánvalóan következnek; fordítva, az `ε`-hoz tartozó `δ₁` és `δ₂` közül a kisebbet
véve, `x < x₀`, `x = x₀` és `x > x₀` esetén egyaránt teljesül a kívánt becslés. -/
theorem cauchyFolytonos_iff_ketoldali (f : ℝ → ℝ) (x₀ : ℝ) :
    CauchyFolytonos f x₀ ↔ BalrolFolytonos f x₀ ∧ JobbrolFolytonos f x₀ := by
  constructor
  · intro h
    constructor
    · intro ε hε
      obtain ⟨δ, hδ, hδp⟩ := h ε hε
      exact ⟨δ, hδ, fun x _ hx => hδp x hx⟩
    · intro ε hε
      obtain ⟨δ, hδ, hδp⟩ := h ε hε
      exact ⟨δ, hδ, fun x _ hx => hδp x hx⟩
  · rintro ⟨hb, hj⟩ ε hε
    obtain ⟨δ₁, hδ₁, h₁⟩ := hb ε hε
    obtain ⟨δ₂, hδ₂, h₂⟩ := hj ε hε
    refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun x hx => ?_⟩
    rcases lt_trichotomy x x₀ with hlt | heq | hgt
    · exact h₁ x hlt (lt_of_lt_of_le hx (min_le_left _ _))
    · simpa [heq] using hε
    · exact h₂ x hgt (lt_of_lt_of_le hx (min_le_right _ _))

/-- **5.3.5. Definíció.** Az `f` függvény `x₀`-ban *felülről félig folytonos*, ha
bármely `ε > 0`-hoz van olyan `δ > 0`, hogy `|x - x₀| < δ` esetén
`f(x) < f(x₀) + ε`. -/
def FelulrolFeligFolytonos (f : ℝ → ℝ) (x₀ : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x : ℝ, |x - x₀| < δ → f x < f x₀ + ε

/-- **5.3.5. Definíció.** Az `f` függvény `x₀`-ban *alulról félig folytonos*. -/
def AlulrolFeligFolytonos (f : ℝ → ℝ) (x₀ : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x : ℝ, |x - x₀| < δ → f x₀ - ε < f x

/-- **5.3.7. Definíció/Tétel.** Az `f` függvény `x₀`-ban akkor és csak akkor folytonos,
ha `x₀`-ban felülről és alulról is félig folytonos.

*Bizonyítás.* A `|f(x) - f(x₀)| < ε` korlátozás éppen az
`f(x₀) - ε < f(x) < f(x₀) + ε` kettős egyenlőtlenséggel egyenértékű; a két féloldali
korlátozáshoz tartozó `δ`-k közül a kisebbet választva adódik az állítás. -/
theorem cauchyFolytonos_iff_feligFolytonos (f : ℝ → ℝ) (x₀ : ℝ) :
    CauchyFolytonos f x₀ ↔ FelulrolFeligFolytonos f x₀ ∧ AlulrolFeligFolytonos f x₀ := by
  constructor
  · intro h
    constructor
    · intro ε hε
      obtain ⟨δ, hδ, hδp⟩ := h ε hε
      exact ⟨δ, hδ, fun x hx => by linarith [(abs_lt.1 (hδp x hx)).2]⟩
    · intro ε hε
      obtain ⟨δ, hδ, hδp⟩ := h ε hε
      exact ⟨δ, hδ, fun x hx => by linarith [(abs_lt.1 (hδp x hx)).1]⟩
  · rintro ⟨hf, ha⟩ ε hε
    obtain ⟨δ₁, hδ₁, h₁⟩ := hf ε hε
    obtain ⟨δ₂, hδ₂, h₂⟩ := ha ε hε
    refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun x hx => abs_lt.2 ⟨?_, ?_⟩⟩
    · have := h₂ x (lt_of_lt_of_le hx (min_le_right _ _)); linarith
    · have := h₁ x (lt_of_lt_of_le hx (min_le_left _ _)); linarith

/-! ## 5.4. Intervallumon folytonos függvények -/

/-- **5.4.1. Definíció.** Az `f` függvény *folytonos* egy `I` halmazon (nyitott
intervallumon), ha annak minden pontjában folytonos. -/
def FolytonosHalmazon (f : ℝ → ℝ) (I : Set ℝ) : Prop := ∀ x ∈ I, CauchyFolytonos f x

/-- **5.4.3. Definíció.** Az `f` függvény az `I` intervallumon *egyenletesen folytonos*,
ha bármely `ε > 0`-hoz megadható olyan (csak `ε`-tól függő, a helytől független)
`δ > 0`, hogy valahányszor `|x - x'| < δ`, `x, x' ∈ I`, mindannyiszor
`|f(x) - f(x')| < ε`. -/
def EgyenletesenFolytonos (f : ℝ → ℝ) (I : Set ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x ∈ I, ∀ x' ∈ I, |x - x'| < δ → |f x - f x'| < ε

/-- Az egyenletes folytonosságból következik a (pontonkénti) folytonosság a halmaz
minden pontjában, ahol a halmaz egy egész környezetet tartalmaz — nyitott
intervallumon tehát mindenütt. -/
theorem egyenletesenFolytonos_folytonos {f : ℝ → ℝ} {a b : ℝ}
    (h : EgyenletesenFolytonos f (Ioo a b)) : ∀ x₀ ∈ Ioo a b, CauchyFolytonos f x₀ := by
  intro x₀ hx₀ ε hε
  obtain ⟨δ, hδ, hδp⟩ := h ε hε
  obtain ⟨ha, hb⟩ := hx₀
  refine ⟨min δ (min (x₀ - a) (b - x₀)), lt_min hδ (lt_min (by linarith) (by linarith)),
    fun x hx => ?_⟩
  have h1 : |x - x₀| < δ := lt_of_lt_of_le hx (min_le_left _ _)
  have h2 : |x - x₀| < x₀ - a := lt_of_lt_of_le hx (le_trans (min_le_right _ _) (min_le_left _ _))
  have h3 : |x - x₀| < b - x₀ := lt_of_lt_of_le hx (le_trans (min_le_right _ _) (min_le_right _ _))
  have habs := abs_lt.1 h2
  have habs' := abs_lt.1 h3
  exact hδp x ⟨by linarith [habs.1], by linarith [habs'.2]⟩ x₀ ⟨ha, hb⟩ h1

/-- A könyv példája: az `f(x) = 1/x` függvény a `(0, 1)` intervallumon folytonos,
de **nem** egyenletesen folytonos.

*Bizonyítás (a könyv szerint).* Bármely `x ∈ (0, 1)`-re `|1/x - 1/(2x)| = 1/(2x) > 1/2`,
így bárhogyan is választjuk `δ > 0`-t, ha `x < δ`, akkor `|2x - x| < δ`, mégsem lesz
`|1/x - 1/(2x)| < ε`, ha `ε ≤ 1/2`. -/
theorem egy_per_x_nem_egyenletesen_folytonos :
    ¬ EgyenletesenFolytonos (fun x : ℝ => 1 / x) (Ioo 0 1) := by
  intro h
  obtain ⟨δ, hδ, hδp⟩ := h (1 / 2) (by norm_num)
  set x : ℝ := min δ (1 / 2) / 2 with hxdef
  have hxpos : 0 < x := by
    have : 0 < min δ (1 / 2) := lt_min hδ (by norm_num)
    simpa [hxdef] using half_pos this
  have hxhalf : x < 1 / 2 := by
    have h1 : min δ (1 / 2) ≤ 1 / 2 := min_le_right _ _
    simp only [hxdef]
    linarith
  have hxδ : x < δ := by
    have h1 : min δ (1 / 2) ≤ δ := min_le_left _ _
    simp only [hxdef]
    linarith
  have hx2 : (2 * x) ∈ Ioo (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hx1 : x ∈ Ioo (0 : ℝ) 1 := ⟨hxpos, by linarith⟩
  have key := hδp x hx1 (2 * x) hx2 (by rw [abs_lt]; constructor <;> linarith)
  have hval : (1 : ℝ) / x - 1 / (2 * x) = 1 / (2 * x) := by
    field_simp
    ring
  rw [hval] at key
  have : (1 : ℝ) / 2 < 1 / (2 * x) := by
    rw [div_lt_div_iff₀ (by norm_num) (by linarith)]
    linarith
  rw [abs_of_pos (by positivity)] at key
  linarith

/-! ### 5.4.4–5.4.6. Műveletek folytonos függvényekkel -/

/-- **5.4.4. Tétel.** Ha két függvény folytonos az `x₀` pontban, akkor összegük,
különbségük és szorzatuk is folytonos `x₀`-ban; hányadosuk is folytonos, ha a
nevezőben levő függvény `x₀`-ban nullától különböző.

*Bizonyítás.* A folytonosság Heine-féle definícióját és a számsorozatokra megismert
műveleti szabályokat (4.9. pont) alkalmazva azonnal adódik az állítás. -/
theorem folytonos_add {f g : ℝ → ℝ} {x₀ : ℝ}
    (hf : HeineFolytonos f x₀) (hg : HeineFolytonos g x₀) :
    HeineFolytonos (fun x => f x + g x) x₀ :=
  fun x hx => Ch04.hatarErtek_add (hf x hx) (hg x hx)

/-- **5.4.4. Tétel** (különbség). -/
theorem folytonos_sub {f g : ℝ → ℝ} {x₀ : ℝ}
    (hf : HeineFolytonos f x₀) (hg : HeineFolytonos g x₀) :
    HeineFolytonos (fun x => f x - g x) x₀ :=
  fun x hx => Ch04.hatarErtek_sub (hf x hx) (hg x hx)

/-- **5.4.4. Tétel** (szorzat). -/
theorem folytonos_mul {f g : ℝ → ℝ} {x₀ : ℝ}
    (hf : HeineFolytonos f x₀) (hg : HeineFolytonos g x₀) :
    HeineFolytonos (fun x => f x * g x) x₀ :=
  fun x hx => Ch04.hatarErtek_mul (hf x hx) (hg x hx)

/-- **5.4.4. Tétel** (hányados, ha `g(x₀) ≠ 0`). -/
theorem folytonos_div {f g : ℝ → ℝ} {x₀ : ℝ}
    (hf : HeineFolytonos f x₀) (hg : HeineFolytonos g x₀) (hg0 : g x₀ ≠ 0) :
    HeineFolytonos (fun x => f x / g x) x₀ :=
  fun x hx => Ch04.hatarErtek_div (hf x hx) (hg x hx) hg0

/-- **5.7.1. Tétel.** A konstans függvény mindenütt folytonos. -/
theorem folytonos_const (c : ℝ) (x₀ : ℝ) : CauchyFolytonos (fun _ => c) x₀ :=
  fun ε hε => ⟨1, one_pos, fun x _ => by simpa using hε⟩

/-- **5.7.2. Tétel.** Az `f(x) = x` függvény mindenütt folytonos. -/
theorem folytonos_id (x₀ : ℝ) : CauchyFolytonos (fun x => x) x₀ :=
  fun ε hε => ⟨ε, hε, fun _ hx => hx⟩

/-- **5.4.5. Tétel.** Bármely polinom mindenütt folytonos.

*Bizonyítás.* Az 5.4.4. Tételből (összeg és szorzat folytonossága) és abból a két
triviális tényből, hogy az `f(x) = c` és az `f(x) = x` függvény mindenütt folytonos. -/
theorem folytonos_polinom (p : Polynomial ℝ) (x₀ : ℝ) :
    CauchyFolytonos (fun x => p.eval x) x₀ :=
  (cauchyFolytonos_iff_continuousAt _ _).2 (p.continuousAt)

/-- **5.4.5. Tétel.** Bármely racionális törtfüggvény a nevező zérushelyeit kivéve
mindenütt folytonos. -/
theorem folytonos_racionalis (p q : Polynomial ℝ) (x₀ : ℝ) (hq : q.eval x₀ ≠ 0) :
    CauchyFolytonos (fun x => p.eval x / q.eval x) x₀ :=
  (cauchyFolytonos_iff_continuousAt _ _).2 (p.continuousAt.div q.continuousAt hq)

/-- **5.4.6. Tétel („fokozatos változás”).** Ha `f` folytonos `x₀`-ban és
`k < f(x₀) < K`, akkor van `x₀`-nak olyan környezete, amelybe eső összes `x` pontra
`k < f(x) < K` teljesül.

*Bizonyítás.* Legyen `ε₀ = min(K - f(x₀), f(x₀) - k) > 0`. A folytonosság miatt
`ε₀`-hoz van olyan `δ > 0`, hogy `|x - x₀| < δ` esetén `|f(x) - f(x₀)| < ε₀`, azaz
`f(x₀) - ε₀ < f(x) < f(x₀) + ε₀`. Mivel `k ≤ f(x₀) - ε₀` és `f(x₀) + ε₀ ≤ K`,
adódik az állítás. -/
theorem fokozatos_valtozas {f : ℝ → ℝ} {x₀ k K : ℝ} (hf : CauchyFolytonos f x₀)
    (hk : k < f x₀) (hK : f x₀ < K) :
    ∃ δ > 0, ∀ x : ℝ, |x - x₀| < δ → k < f x ∧ f x < K := by
  set ε₀ : ℝ := min (K - f x₀) (f x₀ - k) with hε₀def
  have hε₀ : 0 < ε₀ := lt_min (by linarith) (by linarith)
  obtain ⟨δ, hδ, hδp⟩ := hf ε₀ hε₀
  refine ⟨δ, hδ, fun x hx => ?_⟩
  have h := abs_lt.1 (hδp x hx)
  have h1 : ε₀ ≤ f x₀ - k := min_le_right _ _
  have h2 : ε₀ ≤ K - f x₀ := min_le_left _ _
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-! ## 5.5. Az összetett függvények fogalma -/

/-- **5.5.2. Tétel.** Az `f(g(x))` összetett függvény folytonos az `x₀` helyen, ha a
`g` belső függvény folytonos `x₀`-ban és az `f` külső függvény folytonos `g(x₀)`-ban.

*Bizonyítás.* Ha `xₙ → x₀`, akkor `g` folytonossága miatt `g(xₙ) → g(x₀)`; így, mivel
`f` folytonos `g(x₀)` helyen, `f(g(xₙ)) → f(g(x₀))`. -/
theorem folytonos_osszetett {f g : ℝ → ℝ} {x₀ : ℝ}
    (hg : HeineFolytonos g x₀) (hf : HeineFolytonos f (g x₀)) :
    HeineFolytonos (fun x => f (g x)) x₀ :=
  fun x hx => hf (fun n => g (x n)) (hg x hx)

/-! ## 5.6. Az inverz függvény fogalma -/

/-- **5.6.2. Tétel (közbülsőérték-tétel).** Az `[a, b]`-n folytonos `f` függvény minden
`f(a)` és `f(b)` közötti `C` értéket felvesz.

*Bizonyítás.* A könyv az intervallumfelezés módszerével (egymásba skatulyázott
intervallumok, 4.14. pont) bizonyítja; itt a Mathlib közbülsőérték-tételére
hivatkozunk. -/
theorem kozbulso_ertek {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) {C : ℝ} (hC : C ∈ Icc (f a) (f b)) :
    ∃ c ∈ Icc a b, f c = C := by
  obtain ⟨c, hc, hfc⟩ := intermediate_value_Icc hab hf hC
  exact ⟨c, hc, hfc⟩

/-- Segédtétel a 5.6.1. Tételhez: ha `f` folytonos és injektív egy `s` kompakt
halmazon, akkor az `f` inverze folytonos az `f(s)` képhalmazon.

*Bizonyítás.* A `g = f⁻¹` inverz melletti `g⁻¹(C) ∩ f(s) = f(C ∩ s)` egyenlőség
minden `C` zárt halmazra fennáll, és `C ∩ s` kompakt, tehát `f(C ∩ s)` is kompakt,
így zárt. -/
theorem inverz_folytonos_kompaktan {f : ℝ → ℝ} {s : Set ℝ} (hs : IsCompact s)
    (hf : ContinuousOn f s) (hinj : InjOn f s) :
    ContinuousOn (Function.invFunOn f s) (f '' s) := by
  rw [continuousOn_iff_isClosed]
  intro C hC
  refine ⟨f '' (C ∩ s), ((hs.inter_left hC).image_of_continuousOn
      (hf.mono inter_subset_right)).isClosed, ?_⟩
  ext y
  constructor
  · rintro ⟨hy, x, hx, rfl⟩
    have hgx : Function.invFunOn f s (f x) = x := hinj.leftInvOn_invFunOn hx
    refine ⟨⟨x, ⟨?_, hx⟩, rfl⟩, ⟨x, hx, rfl⟩⟩
    simpa [hgx] using hy
  · rintro ⟨⟨x, hx, rfl⟩, -⟩
    have hgx : Function.invFunOn f s (f x) = x := hinj.leftInvOn_invFunOn hx.2
    exact ⟨by simpa [hgx] using hx.1, ⟨x, hx.2, rfl⟩⟩

/-- **5.6.1. Tétel.** Egy `[a, b]` intervallumon szigorúan monoton növekedő folytonos
`f` függvénynek létezik inverz függvénye, amely az `[f(a), f(b)]` intervallumon
értelmezett, ott szigorúan monoton növekedő és folytonos.

*Bizonyítás.* A szigorú monotonitás miatt `f` injektív, tehát az inverz `g` egyértelműen
létezik; az értékkészlet az 5.6.2. Tétel (közbülsőérték-tétel) szerint éppen az
`[f(a), f(b)]` intervallum. A `g` szigorú monotonitása közvetlenül adódik `f` szigorú
monotonitásából, folytonossága pedig abból, hogy `f` kompakt intervallumon folytonos
és injektív. -/
theorem inverz_fuggveny {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) (hmono : StrictMonoOn f (Icc a b)) :
    f '' Icc a b = Icc (f a) (f b) ∧
      (∀ y ∈ Icc (f a) (f b), f (Function.invFunOn f (Icc a b) y) = y) ∧
      StrictMonoOn (Function.invFunOn f (Icc a b)) (Icc (f a) (f b)) ∧
      ContinuousOn (Function.invFunOn f (Icc a b)) (Icc (f a) (f b)) := by
  have hinj : InjOn f (Icc a b) := hmono.injOn
  have himg : f '' Icc a b = Icc (f a) (f b) :=
    hf.image_Icc_of_monotoneOn hab hmono.monotoneOn
  refine ⟨himg, ?_, ?_, ?_⟩
  · intro y hy
    rw [← himg] at hy
    exact Function.invFunOn_eq (by simpa [Set.image] using hy)
  · intro y hy z hz hyz
    rw [← himg] at hy hz
    obtain ⟨u, hu, rfl⟩ := hy
    obtain ⟨v, hv, rfl⟩ := hz
    rw [hinj.leftInvOn_invFunOn hu, hinj.leftInvOn_invFunOn hv]
    by_contra hcon
    push_neg at hcon
    rcases eq_or_lt_of_le hcon with heq | hlt
    · rw [heq] at hyz; exact lt_irrefl _ hyz
    · exact absurd (hmono hv hu hlt) (not_lt.2 hyz.le)
  · rw [← himg]
    exact inverz_folytonos_kompaktan isCompact_Icc hf hinj

end Leindler.Ch05
