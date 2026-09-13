import Analizis.Ch05a_FuggvenyekAlapfogalmak
import Analizis.Ch08a_MonotonitasSzelsoertek

/-!
# Leindler László: Analízis — 8.2.2., 8.4.2. és 8.4.3. Tétel

Ez a modul a 8. fejezet hátralévő tételeit tartalmazza (113., 116–117. oldal):

* **8.2.2. Tétel** ‑ ha `f'` folytonos `x₀`-ban és `f'(x₀) > 0` (`< 0`), akkor `f` az
  `x₀` valamely környezetében szigorúan növekvő (csökkenő),
* **8.4.2. Tétel** ‑ ha `f`-nek `x₀`-ban szigorú szélső értéke van, és `f'` az `x₀` bal,
  illetve jobb oldali környezetében jeltartó, akkor `f'` az `x₀` pontnál előjelet vált,
* **8.4.3. Tétel** ‑ jeltartó derivált esetén a szigorú szélső érték létezésének
  szükséges és elegendő feltétele a derivált előjelváltása.
-/

namespace Leindler.Ch08

open Set Leindler Leindler.Ch05 Leindler.Ch06

/-! ## Segédfogalmak -/

/-- Az `f` függvénynek az `x₀` pont `δ`-sugarú környezetében szigorú maximuma van. -/
def SzigoruMaximumKornyezetben (f : ℝ → ℝ) (x₀ δ : ℝ) : Prop :=
  ∀ x, |x - x₀| < δ → x ≠ x₀ → f x < f x₀

/-- Az `f` függvénynek az `x₀` pont `δ`-sugarú környezetében szigorú minimuma van. -/
def SzigoruMinimumKornyezetben (f : ℝ → ℝ) (x₀ δ : ℝ) : Prop :=
  ∀ x, |x - x₀| < δ → x ≠ x₀ → f x₀ < f x

/-- Az `f` függvénynek az `x₀` pont `δ`-sugarú környezetében szigorú szélső értéke van. -/
def SzigoruSzelsoertekKornyezetben (f : ℝ → ℝ) (x₀ δ : ℝ) : Prop :=
  SzigoruMaximumKornyezetben f x₀ δ ∨ SzigoruMinimumKornyezetben f x₀ δ

/-- A `δ`-környezetbeli szigorú maximum a könyv 5.1.4. Definíciója szerinti szigorú
helyi maximum. -/
theorem szigoruMaximumKornyezetben_szigoruHelyiMaximum {f : ℝ → ℝ} {x₀ δ : ℝ} (hδ : 0 < δ)
    (h : SzigoruMaximumKornyezetben f x₀ δ) : SzigoruHelyiMaximum f univ x₀ :=
  ⟨δ, hδ, fun x _ hne hxd => h x hxd hne⟩

/-- A derivált *jeltartó* az `x₀` bal oldali `δ`-környezetében, ha ott mindenütt
pozitív, mindenütt negatív, vagy mindenütt nulla. -/
def BalJeltarto (g : ℝ → ℝ) (x₀ δ : ℝ) : Prop :=
  (∀ x, |x - x₀| < δ → x < x₀ → 0 < g x) ∨ (∀ x, |x - x₀| < δ → x < x₀ → g x < 0) ∨
    (∀ x, |x - x₀| < δ → x < x₀ → g x = 0)

/-- A derivált jeltartó az `x₀` jobb oldali `δ`-környezetében. -/
def JobbJeltarto (g : ℝ → ℝ) (x₀ δ : ℝ) : Prop :=
  (∀ x, |x - x₀| < δ → x₀ < x → 0 < g x) ∨ (∀ x, |x - x₀| < δ → x₀ < x → g x < 0) ∨
    (∀ x, |x - x₀| < δ → x₀ < x → g x = 0)

/-- A `g` függvény az `x₀` pontnál *előjelet vált*: az egyik oldalon pozitív, a másikon
negatív. -/
def ElojeletValt (g : ℝ → ℝ) (x₀ δ : ℝ) : Prop :=
  ((∀ x, |x - x₀| < δ → x < x₀ → 0 < g x) ∧ (∀ x, |x - x₀| < δ → x₀ < x → g x < 0)) ∨
    ((∀ x, |x - x₀| < δ → x < x₀ → g x < 0) ∧ (∀ x, |x - x₀| < δ → x₀ < x → 0 < g x))

/-! ## Segédlemmák: a derivált előjele és a függvény viselkedése az `x₀` egyik oldalán -/

section Segedlemmak

variable {f f' : ℝ → ℝ} {x₀ δ : ℝ}

/-- Az `x` és `x₀` közötti pontok is az `x₀` `δ`-környezetében vannak. -/
private theorem kozbulso_pont (hx : |x - x₀| < δ) {y : ℝ} (h₁ : min x x₀ ≤ y)
    (h₂ : y ≤ max x x₀) : |y - x₀| < δ := by
  have h := abs_lt.1 hx
  rcases le_total x x₀ with hle | hle
  · rw [min_eq_left hle] at h₁
    rw [max_eq_right hle] at h₂
    rw [abs_lt]
    constructor <;> linarith [h.1, h.2]
  · rw [min_eq_right hle] at h₁
    rw [max_eq_left hle] at h₂
    rw [abs_lt]
    constructor <;> linarith [h.1, h.2]

private theorem folytonos_kornyezetben (hd : ∀ x, |x - x₀| < δ → Derivalt f x (f' x))
    {y : ℝ} (hy : |y - x₀| < δ) : ContinuousAt f y :=
  (cauchyFolytonos_iff_continuousAt f y).1 (differencialhato_folytonos (hd y hy))

/-- Ha a derivált az `x₀`-tól balra pozitív, akkor ott a függvényértékek kisebbek
`f(x₀)`-nál. -/
theorem bal_kisebb_ha_derivalt_pozitiv (hd : ∀ x, |x - x₀| < δ → Derivalt f x (f' x))
    (hbal : ∀ x, |x - x₀| < δ → x < x₀ → 0 < f' x) :
    ∀ x, |x - x₀| < δ → x < x₀ → f x < f x₀ := by
  intro x hx hlt
  have hsub : ∀ y ∈ Icc x x₀, |y - x₀| < δ := fun y hy =>
    kozbulso_pont hx (by rw [min_eq_left hlt.le]; exact hy.1)
      (by rw [max_eq_right hlt.le]; exact hy.2)
  have := szigoruan_novekedo_ha_derivalt_pozitiv (f := f) (f' := f') (a := x) (b := x₀)
    (fun y hy => (folytonos_kornyezetben hd (hsub y hy)).continuousWithinAt)
    (fun y hy => hd y (hsub y ⟨hy.1.le, hy.2.le⟩))
    (fun y hy => hbal y (hsub y ⟨hy.1.le, hy.2.le⟩) hy.2)
  exact this x ⟨le_rfl, hlt.le⟩ x₀ ⟨hlt.le, le_rfl⟩ hlt

/-- Ha a derivált az `x₀`-tól balra negatív, akkor ott a függvényértékek nagyobbak
`f(x₀)`-nál. -/
theorem bal_nagyobb_ha_derivalt_negativ (hd : ∀ x, |x - x₀| < δ → Derivalt f x (f' x))
    (hbal : ∀ x, |x - x₀| < δ → x < x₀ → f' x < 0) :
    ∀ x, |x - x₀| < δ → x < x₀ → f x₀ < f x := by
  have hdneg : ∀ x, |x - x₀| < δ → Derivalt (fun t => -f t) x (-f' x) := by
    intro x hx
    rw [derivalt_iff_hasDerivAt]
    exact ((derivalt_iff_hasDerivAt f x (f' x)).1 (hd x hx)).neg
  have h := bal_kisebb_ha_derivalt_pozitiv (f := fun t => -f t) (f' := fun t => -f' t)
    hdneg (fun x hx hlt => by have := hbal x hx hlt; linarith)
  intro x hx hlt
  have := h x hx hlt
  simp only at this
  linarith

/-- Ha a derivált az `x₀`-tól balra azonosan nulla, akkor a függvény ott konstans. -/
theorem bal_egyenlo_ha_derivalt_nulla (hd : ∀ x, |x - x₀| < δ → Derivalt f x (f' x))
    (hbal : ∀ x, |x - x₀| < δ → x < x₀ → f' x = 0) :
    ∀ x, |x - x₀| < δ → x < x₀ → f x = f x₀ := by
  intro x hx hlt
  have hsub : ∀ y ∈ Icc x x₀, |y - x₀| < δ := fun y hy =>
    kozbulso_pont hx (by rw [min_eq_left hlt.le]; exact hy.1)
      (by rw [max_eq_right hlt.le]; exact hy.2)
  have hcont : ContinuousOn f (Icc x x₀) := fun y hy =>
    (folytonos_kornyezetben hd (hsub y hy)).continuousWithinAt
  have hzero : ∀ y ∈ Ioo x x₀, Derivalt f y 0 := by
    intro y hy
    have hmem := hsub y ⟨hy.1.le, hy.2.le⟩
    have := hd y hmem
    rwa [hbal y hmem hy.2] at this
  have := derivalt_nulla_konstans hcont hzero x₀ ⟨hlt.le, le_rfl⟩
  exact this.symm

/-- Ha a derivált az `x₀`-tól jobbra pozitív, akkor ott a függvényértékek nagyobbak
`f(x₀)`-nál. -/
theorem jobb_nagyobb_ha_derivalt_pozitiv (hd : ∀ x, |x - x₀| < δ → Derivalt f x (f' x))
    (hjobb : ∀ x, |x - x₀| < δ → x₀ < x → 0 < f' x) :
    ∀ x, |x - x₀| < δ → x₀ < x → f x₀ < f x := by
  intro x hx hlt
  have hsub : ∀ y ∈ Icc x₀ x, |y - x₀| < δ := fun y hy =>
    kozbulso_pont hx (by rw [min_eq_right hlt.le]; exact hy.1)
      (by rw [max_eq_left hlt.le]; exact hy.2)
  have := szigoruan_novekedo_ha_derivalt_pozitiv (f := f) (f' := f') (a := x₀) (b := x)
    (fun y hy => (folytonos_kornyezetben hd (hsub y hy)).continuousWithinAt)
    (fun y hy => hd y (hsub y ⟨hy.1.le, hy.2.le⟩))
    (fun y hy => hjobb y (hsub y ⟨hy.1.le, hy.2.le⟩) hy.1)
  exact this x₀ ⟨le_rfl, hlt.le⟩ x ⟨hlt.le, le_rfl⟩ hlt

/-- Ha a derivált az `x₀`-tól jobbra negatív, akkor ott a függvényértékek kisebbek
`f(x₀)`-nál. -/
theorem jobb_kisebb_ha_derivalt_negativ (hd : ∀ x, |x - x₀| < δ → Derivalt f x (f' x))
    (hjobb : ∀ x, |x - x₀| < δ → x₀ < x → f' x < 0) :
    ∀ x, |x - x₀| < δ → x₀ < x → f x < f x₀ := by
  have hdneg : ∀ x, |x - x₀| < δ → Derivalt (fun t => -f t) x (-f' x) := by
    intro x hx
    rw [derivalt_iff_hasDerivAt]
    exact ((derivalt_iff_hasDerivAt f x (f' x)).1 (hd x hx)).neg
  have h := jobb_nagyobb_ha_derivalt_pozitiv (f := fun t => -f t) (f' := fun t => -f' t)
    hdneg (fun x hx hlt => by have := hjobb x hx hlt; linarith)
  intro x hx hlt
  have := h x hx hlt
  simp only at this
  linarith

/-- Ha a derivált az `x₀`-tól jobbra azonosan nulla, akkor a függvény ott konstans. -/
theorem jobb_egyenlo_ha_derivalt_nulla (hd : ∀ x, |x - x₀| < δ → Derivalt f x (f' x))
    (hjobb : ∀ x, |x - x₀| < δ → x₀ < x → f' x = 0) :
    ∀ x, |x - x₀| < δ → x₀ < x → f x = f x₀ := by
  intro x hx hlt
  have hsub : ∀ y ∈ Icc x₀ x, |y - x₀| < δ := fun y hy =>
    kozbulso_pont hx (by rw [min_eq_right hlt.le]; exact hy.1)
      (by rw [max_eq_left hlt.le]; exact hy.2)
  have hcont : ContinuousOn f (Icc x₀ x) := fun y hy =>
    (folytonos_kornyezetben hd (hsub y hy)).continuousWithinAt
  have hzero : ∀ y ∈ Ioo x₀ x, Derivalt f y 0 := by
    intro y hy
    have hmem := hsub y ⟨hy.1.le, hy.2.le⟩
    have := hd y hmem
    rwa [hjobb y hmem hy.1] at this
  exact derivalt_nulla_konstans hcont hzero x ⟨hlt.le, le_rfl⟩

end Segedlemmak

/-! ## 8.2.2. Tétel -/

/-- **8.2.2. Tétel.** Ha az `f'(x)` az `x₀` pontban folytonos és `f'(x₀) > 0`, akkor
`x₀` valamely környezetében `f(x)` szigorúan növekvő.

*Bizonyítás (a könyv gondolatmenete).* A folytonos függvények „fokozatos változás”
tulajdonsága szerint `x₀`-nak van olyan környezete, ahol `f'(x)` mindenütt pozitív, és
így a 8.1.2. Tétel szerint `f(x)` ott szigorúan növekvő. -/
theorem szigoruan_novekvo_kornyezetben {f f' : ℝ → ℝ} {x₀ δ₀ : ℝ} (hδ₀ : 0 < δ₀)
    (hd : ∀ x, |x - x₀| < δ₀ → Derivalt f x (f' x)) (hcont : CauchyFolytonos f' x₀)
    (hpos : 0 < f' x₀) :
    ∃ δ > 0, ∀ x y : ℝ, |x - x₀| < δ → |y - x₀| < δ → x < y → f x < f y := by
  obtain ⟨δ₁, hδ₁, h₁⟩ := hcont (f' x₀) hpos
  refine ⟨min δ₀ δ₁, lt_min hδ₀ hδ₁, fun x y hx hy hlt => ?_⟩
  have hxδ₀ : |x - x₀| < δ₀ := lt_of_lt_of_le hx (min_le_left _ _)
  have hyδ₀ : |y - x₀| < δ₀ := lt_of_lt_of_le hy (min_le_left _ _)
  have hpos' : ∀ z, |z - x₀| < min δ₀ δ₁ → 0 < f' z := by
    intro z hz
    have := h₁ z (lt_of_lt_of_le hz (min_le_right _ _))
    have h2 := abs_lt.1 this
    linarith [h2.1]
  have hsub : ∀ z ∈ Icc x y, |z - x₀| < min δ₀ δ₁ := by
    intro z hz
    have hax := abs_lt.1 hx
    have hay := abs_lt.1 hy
    rw [abs_lt]
    exact ⟨by linarith [hz.1, hax.1], by linarith [hz.2, hay.2]⟩
  have := szigoruan_novekedo_ha_derivalt_pozitiv (f := f) (f' := f') (a := x) (b := y)
    (fun z hz => (folytonos_kornyezetben (δ := δ₀) hd
      (lt_of_lt_of_le (hsub z hz) (min_le_left _ _))).continuousWithinAt)
    (fun z hz => hd z (lt_of_lt_of_le (hsub z ⟨hz.1.le, hz.2.le⟩) (min_le_left _ _)))
    (fun z hz => hpos' z (hsub z ⟨hz.1.le, hz.2.le⟩))
  exact this x ⟨le_rfl, hlt.le⟩ y ⟨hlt.le, le_rfl⟩ hlt

/-- **8.2.2. Tétel (a csökkenő eset).** Ha `f'` folytonos `x₀`-ban és `f'(x₀) < 0`,
akkor `f` az `x₀` valamely környezetében szigorúan csökkenő. -/
theorem szigoruan_csokkeno_kornyezetben {f f' : ℝ → ℝ} {x₀ δ₀ : ℝ} (hδ₀ : 0 < δ₀)
    (hd : ∀ x, |x - x₀| < δ₀ → Derivalt f x (f' x)) (hcont : CauchyFolytonos f' x₀)
    (hneg : f' x₀ < 0) :
    ∃ δ > 0, ∀ x y : ℝ, |x - x₀| < δ → |y - x₀| < δ → x < y → f y < f x := by
  have hdneg : ∀ x, |x - x₀| < δ₀ → Derivalt (fun t => -f t) x (-f' x) := by
    intro x hx
    rw [derivalt_iff_hasDerivAt]
    exact ((derivalt_iff_hasDerivAt f x (f' x)).1 (hd x hx)).neg
  have hcontneg : CauchyFolytonos (fun t => -f' t) x₀ := by
    intro ε hε
    obtain ⟨δ, hδ, h⟩ := hcont ε hε
    refine ⟨δ, hδ, fun x hx => ?_⟩
    have hxx := h x hx
    rwa [show -f' x - -f' x₀ = -(f' x - f' x₀) by ring, abs_neg]
  obtain ⟨δ, hδ, h⟩ := szigoruan_novekvo_kornyezetben (f := fun t => -f t)
    (f' := fun t => -f' t) hδ₀ hdneg hcontneg (by simpa using hneg)
  refine ⟨δ, hδ, fun x y hx hy hlt => ?_⟩
  have := h x y hx hy hlt
  simp only at this
  linarith

/-! ## 8.4.2. Tétel -/

/-- **8.4.2. Tétel.** Ha `f` az `x₀` pont valamely környezetében differenciálható,
`x₀`-ban szigorú szélső értéke van, és `x₀` valamely bal, illetve jobb oldali
környezetében `f'(x)` jeltartó, akkor `f'(x)` az `x₀` pontnál előjelet vált.

*Bizonyítás (a könyv gondolatmenete).* Ha `f'` nem váltana előjelet, akkor a könyv
táblázatában szereplő esetek valamelyike állna fenn: `f'` mindkét oldalon pozitív
(ekkor `f` átmenőleg növekedő), mindkét oldalon negatív (átmenőleg csökkenő), vagy
valamelyik oldalon azonosan nulla (ekkor `f` ott konstans).  Egyik esetben sincs
`x₀`-ban szigorú szélső érték, ami ellentmondás. -/
theorem derivalt_elojelet_valt_ha_szigoru_szelsoertek {f f' : ℝ → ℝ} {x₀ δ : ℝ}
    (hδ : 0 < δ) (hd : ∀ x, |x - x₀| < δ → Derivalt f x (f' x))
    (hext : SzigoruSzelsoertekKornyezetben f x₀ δ)
    (hbal : BalJeltarto f' x₀ δ) (hjobb : JobbJeltarto f' x₀ δ) :
    ElojeletValt f' x₀ δ := by
  -- két tanúpont az `x₀` két oldalán
  have hbalx : |(x₀ - δ / 2) - x₀| < δ := by
    rw [show x₀ - δ / 2 - x₀ = -(δ / 2) by ring, abs_neg, abs_of_pos (by linarith)]
    linarith
  have hjobbx : |(x₀ + δ / 2) - x₀| < δ := by
    rw [show x₀ + δ / 2 - x₀ = δ / 2 by ring, abs_of_pos (by linarith)]
    linarith
  have hbaLt : x₀ - δ / 2 < x₀ := by linarith
  have hjobbGt : x₀ < x₀ + δ / 2 := by linarith
  rcases hext with hmax | hmin
  · -- szigorú maximum: balra `f'` csak pozitív, jobbra csak negatív lehet
    have hbalpos : ∀ x, |x - x₀| < δ → x < x₀ → 0 < f' x := by
      rcases hbal with h | h | h
      · exact h
      · exfalso
        have := bal_nagyobb_ha_derivalt_negativ hd h (x₀ - δ / 2) hbalx hbaLt
        have := hmax (x₀ - δ / 2) hbalx (by intro hcon; linarith [hcon ▸ hbaLt])
        linarith
      · exfalso
        have heq := bal_egyenlo_ha_derivalt_nulla hd h (x₀ - δ / 2) hbalx hbaLt
        have := hmax (x₀ - δ / 2) hbalx (by intro hcon; linarith [hcon ▸ hbaLt])
        linarith
    have hjobbneg : ∀ x, |x - x₀| < δ → x₀ < x → f' x < 0 := by
      rcases hjobb with h | h | h
      · exfalso
        have := jobb_nagyobb_ha_derivalt_pozitiv hd h (x₀ + δ / 2) hjobbx hjobbGt
        have := hmax (x₀ + δ / 2) hjobbx (by intro hcon; linarith [hcon ▸ hjobbGt])
        linarith
      · exact h
      · exfalso
        have heq := jobb_egyenlo_ha_derivalt_nulla hd h (x₀ + δ / 2) hjobbx hjobbGt
        have := hmax (x₀ + δ / 2) hjobbx (by intro hcon; linarith [hcon ▸ hjobbGt])
        linarith
    exact Or.inl ⟨hbalpos, hjobbneg⟩
  · -- szigorú minimum: balra `f'` csak negatív, jobbra csak pozitív lehet
    have hbalneg : ∀ x, |x - x₀| < δ → x < x₀ → f' x < 0 := by
      rcases hbal with h | h | h
      · exfalso
        have := bal_kisebb_ha_derivalt_pozitiv hd h (x₀ - δ / 2) hbalx hbaLt
        have := hmin (x₀ - δ / 2) hbalx (by intro hcon; linarith [hcon ▸ hbaLt])
        linarith
      · exact h
      · exfalso
        have heq := bal_egyenlo_ha_derivalt_nulla hd h (x₀ - δ / 2) hbalx hbaLt
        have := hmin (x₀ - δ / 2) hbalx (by intro hcon; linarith [hcon ▸ hbaLt])
        linarith
    have hjobbpos : ∀ x, |x - x₀| < δ → x₀ < x → 0 < f' x := by
      rcases hjobb with h | h | h
      · exact h
      · exfalso
        have := jobb_kisebb_ha_derivalt_negativ hd h (x₀ + δ / 2) hjobbx hjobbGt
        have := hmin (x₀ + δ / 2) hjobbx (by intro hcon; linarith [hcon ▸ hjobbGt])
        linarith
      · exfalso
        have heq := jobb_egyenlo_ha_derivalt_nulla hd h (x₀ + δ / 2) hjobbx hjobbGt
        have := hmin (x₀ + δ / 2) hjobbx (by intro hcon; linarith [hcon ▸ hjobbGt])
        linarith
    exact Or.inr ⟨hbalneg, hjobbpos⟩

/-! ## 8.4.3. Tétel -/

/-- **8.4.1. Tétel (a minimum esete).** Ha a derivált `x₀`-nál negatívból pozitívba vált,
akkor `f`-nek `x₀`-ban szigorú helyi minimuma van. -/
theorem szigoru_minimum_ha_derivalt_jelet_valt {f f' : ℝ → ℝ} {x₀ δ : ℝ}
    (hd : ∀ x, |x - x₀| < δ → Derivalt f x (f' x))
    (hbal : ∀ x, |x - x₀| < δ → x < x₀ → f' x < 0)
    (hjobb : ∀ x, |x - x₀| < δ → x₀ < x → 0 < f' x) :
    ∀ x, |x - x₀| < δ → x ≠ x₀ → f x₀ < f x := by
  intro x hx hne
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact bal_nagyobb_ha_derivalt_negativ hd hbal x hx hlt
  · exact jobb_nagyobb_ha_derivalt_pozitiv hd hjobb x hx hgt

/-- **8.4.3. Tétel.** Ha `f` az `x₀` pont valamely környezetében differenciálható, és bal,
illetve jobb oldali környezetében `f'(x)` jeltartó, akkor annak, hogy `f(x)`-nek `x₀`-ban
szigorú szélső értéke legyen, szükséges és elegendő feltétele, hogy `f'(x)` előjelet
váltson `x₀`-nál.

*Bizonyítás.* Az elegendőség a 8.4.1. Tétel (előjelváltás ⇒ szigorú szélső érték), a
szükségesség pedig a 8.4.2. Tétel. -/
theorem szigoru_szelsoertek_iff_elojelvaltas {f f' : ℝ → ℝ} {x₀ δ : ℝ} (hδ : 0 < δ)
    (hd : ∀ x, |x - x₀| < δ → Derivalt f x (f' x))
    (hbal : BalJeltarto f' x₀ δ) (hjobb : JobbJeltarto f' x₀ δ) :
    SzigoruSzelsoertekKornyezetben f x₀ δ ↔ ElojeletValt f' x₀ δ := by
  constructor
  · intro hext
    exact derivalt_elojelet_valt_ha_szigoru_szelsoertek hδ hd hext hbal hjobb
  · rintro (⟨hb, hj⟩ | ⟨hb, hj⟩)
    · exact Or.inl (szigoru_maximum_ha_derivalt_jelet_valt hd hb hj)
    · exact Or.inr (szigoru_minimum_ha_derivalt_jelet_valt hd hb hj)

end Leindler.Ch08
