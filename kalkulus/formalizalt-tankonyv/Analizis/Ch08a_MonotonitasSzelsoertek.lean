import Mathlib
import Analizis.Ch06a_Differencialhatosag

/-!
# Leindler László: Analízis — 8. fejezet: Függvénydiszkusszió

## 8.1–8.5. Monotonitás, a derivált Bolzano–Darboux-tulajdonsága, szélső értékek

Ez a fájl a következő tételeket tartalmazza:

* 8.1.1. Tétel — a nulla derivált konstans függvényt jelent,
* 8.1.2. Tétel — a monotonitás szükséges és elegendő feltétele,
* 8.2.1–8.2.2. Tétel — a pontnál való növekedés/csökkenés feltétele,
* 8.3.1. Tétel — a derivált Bolzano–Darboux-tulajdonsága (Darboux-tétel),
* 8.3.2. Tétel — ha a deriváltnak van határértéke, akkor ott folytonos,
* 8.4.1. Tétel — a derivált előjelváltása szigorú helyi szélső értéket ad,
* 8.5.1. Tétel — a második derivált előjelével történő szélsőérték-vizsgálat.
-/

namespace Leindler.Ch08

open Set Leindler Leindler.Ch05 Leindler.Ch06

/-! ## 8.2. Pontban növekedés, illetve csökkenés feltétele -/

/-- **8.2.1. Tétel.** Ha `f'(x₀) > 0`, akkor létezik olyan `I = (x₀ - α, x₀ + α)`
intervallum, hogy ha `x₁, x₂ ∈ I` és `x₁ < x₀ < x₂`, akkor `f(x₁) < f(x₀) < f(x₂)`,
azaz az `f` függvény az `x₀` pontnál növekedő.

*Bizonyítás (a könyv gondolatmenete).* Mivel `f'(x₀)` létezik,
`(f(x) - f(x₀))/(x - x₀) = f'(x₀) + ω`, ahol `ω → 0`, ha `x → x₀`. Így van olyan
`α > 0`, hogy `|x - x₀| < α` esetén `|ω| < |f'(x₀)|`. Ezért `x₁ < x₀` esetén a
különbségi hányados pozitív, tehát `f(x₁) < f(x₀)`; `x₂ > x₀` esetén pedig
`f(x₂) > f(x₀)`. -/
theorem pontnal_novekedo_ha_derivalt_pozitiv {f : ℝ → ℝ} {x₀ L : ℝ}
    (hd : Derivalt f x₀ L) (hL : 0 < L) :
    ∃ α > 0, ∀ x₁ x₂ : ℝ, |x₁ - x₀| < α → |x₂ - x₀| < α → x₁ < x₀ → x₀ < x₂ →
      f x₁ < f x₀ ∧ f x₀ < f x₂ := by
  obtain ⟨α, hα, hp⟩ := hd L hL
  refine ⟨α, hα, fun x₁ x₂ h₁ h₂ hlt₁ hlt₂ => ?_⟩
  have hq₁ := abs_lt.1 (hp x₁ (ne_of_lt hlt₁) h₁)
  have hq₂ := abs_lt.1 (hp x₂ (ne_of_gt hlt₂) h₂)
  have hpos₁ : 0 < kulonbsegiHanyados f x₀ x₁ := by linarith [hq₁.1]
  have hpos₂ : 0 < kulonbsegiHanyados f x₀ x₂ := by linarith [hq₂.1]
  rw [kulonbsegiHanyados] at hpos₁ hpos₂
  constructor
  · rcases div_pos_iff.1 hpos₁ with ⟨h, h'⟩ | ⟨h, h'⟩
    · linarith
    · linarith
  · rcases div_pos_iff.1 hpos₂ with ⟨h, h'⟩ | ⟨h, h'⟩
    · linarith
    · linarith

/-- **8.2.1. Tétel** (csökkenő eset). Ha `f'(x₀) < 0`, akkor az `f` függvény az `x₀`
pontnál csökkenő. -/
theorem pontnal_csokkeno_ha_derivalt_negativ {f : ℝ → ℝ} {x₀ L : ℝ}
    (hd : Derivalt f x₀ L) (hL : L < 0) :
    ∃ α > 0, ∀ x₁ x₂ : ℝ, |x₁ - x₀| < α → |x₂ - x₀| < α → x₁ < x₀ → x₀ < x₂ →
      f x₀ < f x₁ ∧ f x₂ < f x₀ := by
  have hneg : Derivalt (fun x => -f x) x₀ (-L) := by
    rw [derivalt_iff_hasDerivAt] at hd ⊢
    exact hd.neg
  obtain ⟨α, hα, hp⟩ := pontnal_novekedo_ha_derivalt_pozitiv hneg (by linarith)
  refine ⟨α, hα, fun x₁ x₂ h₁ h₂ hlt₁ hlt₂ => ?_⟩
  obtain ⟨e₁, e₂⟩ := hp x₁ x₂ h₁ h₂ hlt₁ hlt₂
  exact ⟨by linarith, by linarith⟩

/-! ## 8.1. A növekedés és csökkenés feltétele -/

/-- **8.1.2. Tétel (elegendőség).** Ha `f` folytonos `[a, b]`-n, differenciálható
`(a, b)`-n, és `f' ≥ 0` az `(a, b)` intervallumon, akkor `f` növekedő `[a, b]`-n.

*Bizonyítás.* Bármely `x₁ < x₂` pontpárra az `[x₁, x₂]` intervallumon teljesülnek a
Lagrange-tétel feltételei, így `(f(x₂) - f(x₁))/(x₂ - x₁) = f'(ξ) ≥ 0`. -/
theorem novekedo_ha_derivalt_nemnegativ {f f' : ℝ → ℝ} {a b : ℝ}
    (hcont : ContinuousOn f (Icc a b)) (hd : ∀ x ∈ Ioo a b, Derivalt f x (f' x))
    (hpos : ∀ x ∈ Ioo a b, 0 ≤ f' x) :
    ∀ x₁ ∈ Icc a b, ∀ x₂ ∈ Icc a b, x₁ < x₂ → f x₁ ≤ f x₂ := by
  intro x₁ h₁ x₂ h₂ hlt
  have hsub : Icc x₁ x₂ ⊆ Icc a b := Icc_subset_Icc h₁.1 h₂.2
  obtain ⟨c, hc, hLc⟩ := lagrange hlt (hcont.mono hsub) (fun y hy =>
    ⟨f' y, hd y ⟨lt_of_le_of_lt h₁.1 hy.1, lt_of_lt_of_le hy.2 h₂.2⟩⟩)
  have hcmem : c ∈ Ioo a b := ⟨lt_of_le_of_lt h₁.1 hc.1, lt_of_lt_of_le hc.2 h₂.2⟩
  have heq : f' c = (f x₂ - f x₁) / (x₂ - x₁) := derivalt_unicitas (hd c hcmem) hLc
  have hx : 0 < x₂ - x₁ := sub_pos.2 hlt
  have := hpos c hcmem
  rw [heq] at this
  have := (div_nonneg_iff.1 this)
  rcases this with ⟨h, -⟩ | ⟨-, h'⟩
  · linarith
  · linarith

/-- **8.1.2. Tétel (szigorú eset).** Ha a derivált pozitív, akkor a függvény szigorúan
növekedő. -/
theorem szigoruan_novekedo_ha_derivalt_pozitiv {f f' : ℝ → ℝ} {a b : ℝ}
    (hcont : ContinuousOn f (Icc a b)) (hd : ∀ x ∈ Ioo a b, Derivalt f x (f' x))
    (hpos : ∀ x ∈ Ioo a b, 0 < f' x) :
    ∀ x₁ ∈ Icc a b, ∀ x₂ ∈ Icc a b, x₁ < x₂ → f x₁ < f x₂ := by
  intro x₁ h₁ x₂ h₂ hlt
  have hsub : Icc x₁ x₂ ⊆ Icc a b := Icc_subset_Icc h₁.1 h₂.2
  obtain ⟨c, hc, hLc⟩ := lagrange hlt (hcont.mono hsub) (fun y hy =>
    ⟨f' y, hd y ⟨lt_of_le_of_lt h₁.1 hy.1, lt_of_lt_of_le hy.2 h₂.2⟩⟩)
  have hcmem : c ∈ Ioo a b := ⟨lt_of_le_of_lt h₁.1 hc.1, lt_of_lt_of_le hc.2 h₂.2⟩
  have heq : f' c = (f x₂ - f x₁) / (x₂ - x₁) := derivalt_unicitas (hd c hcmem) hLc
  have hx : 0 < x₂ - x₁ := sub_pos.2 hlt
  have hp := hpos c hcmem
  rw [heq] at hp
  rcases div_pos_iff.1 hp with ⟨h, -⟩ | ⟨-, h'⟩
  · linarith
  · linarith

/-- **8.1.2. Tétel (szükségesség).** Ha `f` növekedő az `x₀` pont egy környezetében és
ott differenciálható, akkor `f'(x₀) ≥ 0`.

*Bizonyítás.* A különbségi hányados `(f(x) - f(x₀))/(x - x₀) ≥ 0` akár pozitív, akár
negatív `x - x₀` esetén, ezért a határértéke, `f'(x₀)` is nemnegatív. -/
theorem derivalt_nemnegativ_ha_novekedo {f : ℝ → ℝ} {x₀ L δ : ℝ} (hδ : 0 < δ)
    (hmon : ∀ x y : ℝ, |x - x₀| < δ → |y - x₀| < δ → x < y → f x ≤ f y)
    (hd : Derivalt f x₀ L) : 0 ≤ L := by
  by_contra hL
  push_neg at hL
  obtain ⟨α, hα, hp⟩ := pontnal_csokkeno_ha_derivalt_negativ hd hL
  set x₂ : ℝ := x₀ + min α δ / 2 with hx₂
  set x₁ : ℝ := x₀ - min α δ / 2 with hx₁
  have hm : 0 < min α δ := lt_min hα hδ
  have h₁ : |x₁ - x₀| < min α δ := by
    rw [hx₁]; simp only [sub_sub_cancel_left, abs_neg]
    rw [abs_of_pos (by linarith)]; linarith
  have h₂ : |x₂ - x₀| < min α δ := by
    rw [hx₂]; simp only [add_sub_cancel_left]
    rw [abs_of_pos (by linarith)]; linarith
  obtain ⟨e₁, e₂⟩ := hp x₁ x₂ (lt_of_lt_of_le h₁ (min_le_left _ _))
    (lt_of_lt_of_le h₂ (min_le_left _ _)) (by rw [hx₁]; linarith) (by rw [hx₂]; linarith)
  have := hmon x₁ x₂ (lt_of_lt_of_le h₁ (min_le_right _ _))
    (lt_of_lt_of_le h₂ (min_le_right _ _)) (by rw [hx₁, hx₂]; linarith)
  linarith

/-- **8.1.1. Tétel.** Ha az `(a, b)` nyitott intervallumon `f'(x) = 0`, akkor `f`
konstans `(a, b)`-n.

*Bizonyítás.* Ha `x₁, x₂ ∈ (a, b)`, akkor az `[x₁, x₂]`-n teljesülnek a Lagrange-tétel
feltételei, így `f(x₁) - f(x₂) = f'(ξ)(x₁ - x₂) = 0`. -/
theorem konstans_ha_derivalt_nulla {f : ℝ → ℝ} {a b : ℝ}
    (hd : ∀ x ∈ Ioo a b, Derivalt f x 0) :
    ∀ x₁ ∈ Ioo a b, ∀ x₂ ∈ Ioo a b, f x₁ = f x₂ := by
  have hcont : ∀ x ∈ Ioo a b, ContinuousAt f x := fun x hx =>
    (cauchyFolytonos_iff_continuousAt f x).1 (differencialhato_folytonos (hd x hx))
  intro x₁ h₁ x₂ h₂
  rcases lt_trichotomy x₁ x₂ with hlt | heq | hgt
  · have hsub : Icc x₁ x₂ ⊆ Ioo a b := fun y hy =>
      ⟨lt_of_lt_of_le h₁.1 hy.1, lt_of_le_of_lt hy.2 h₂.2⟩
    obtain ⟨c, hc, hLc⟩ := lagrange hlt
      (fun y hy => (hcont y (hsub hy)).continuousWithinAt)
      (fun y hy => ⟨0, hd y (hsub ⟨hy.1.le, hy.2.le⟩)⟩)
    have := derivalt_unicitas (hd c (hsub ⟨hc.1.le, hc.2.le⟩)) hLc
    have hx : x₂ - x₁ ≠ 0 := sub_ne_zero.2 (ne_of_gt hlt)
    field_simp at this
    linarith
  · rw [heq]
  · have hsub : Icc x₂ x₁ ⊆ Ioo a b := fun y hy =>
      ⟨lt_of_lt_of_le h₂.1 hy.1, lt_of_le_of_lt hy.2 h₁.2⟩
    obtain ⟨c, hc, hLc⟩ := lagrange hgt
      (fun y hy => (hcont y (hsub hy)).continuousWithinAt)
      (fun y hy => ⟨0, hd y (hsub ⟨hy.1.le, hy.2.le⟩)⟩)
    have := derivalt_unicitas (hd c (hsub ⟨hc.1.le, hc.2.le⟩)) hLc
    have hx : x₁ - x₂ ≠ 0 := sub_ne_zero.2 (ne_of_gt hgt)
    field_simp at this
    linarith

/-! ## 8.3. A derivált Bolzano–Darboux-tulajdonsága -/

/-- **8.3.1. Tétel (Darboux-tétel).** Ha `f` differenciálható `(a, b)`-ben,
`x₁, x₂ ∈ (a, b)`, `x₁ < x₂`, és `c` olyan érték, amelyre `f'(x₁) < c < f'(x₂)`,
akkor van olyan `ξ ∈ (x₁, x₂)`, hogy `f'(ξ) = c`.

*Bizonyítás (a könyv gondolatmenete).* Legyen `g(x) = f(x) - cx`. Ekkor `g`
differenciálható és `g'(x₁) < 0 < g'(x₂)`, tehát a 8.2.1. Tétel szerint `g` az `x₁`
pontnál csökkenő, az `x₂` pontnál növekedő; ezért a (folytonos `g` által az
`[x₁, x₂]`-n felvett) minimumot `g` egy belső pontban, `ξ`-ben veszi fel. Ott a
6.10.2. Következmény szerint `g'(ξ) = 0`, azaz `f'(ξ) = c`. -/
theorem darboux {f f' : ℝ → ℝ} {a b x₁ x₂ c : ℝ}
    (hd : ∀ x ∈ Ioo a b, Derivalt f x (f' x)) (h₁ : x₁ ∈ Ioo a b) (h₂ : x₂ ∈ Ioo a b)
    (hlt : x₁ < x₂) (hc₁ : f' x₁ < c) (hc₂ : c < f' x₂) :
    ∃ ξ ∈ Ioo x₁ x₂, f' ξ = c := by
  set g : ℝ → ℝ := fun x => f x - c * x with hg
  have hgd : ∀ x ∈ Ioo a b, Derivalt g x (f' x - c) := by
    intro x hx
    have h := (derivalt_iff_hasDerivAt f x (f' x)).1 (hd x hx)
    rw [derivalt_iff_hasDerivAt]
    simpa [hg] using h.sub ((hasDerivAt_id x).const_mul c)
  have hsub : Icc x₁ x₂ ⊆ Ioo a b := fun y hy =>
    ⟨lt_of_lt_of_le h₁.1 hy.1, lt_of_le_of_lt hy.2 h₂.2⟩
  have hgcont : ContinuousOn g (Icc x₁ x₂) := fun y hy =>
    ((cauchyFolytonos_iff_continuousAt g y).1
      (differencialhato_folytonos (hgd y (hsub hy)))).continuousWithinAt
  obtain ⟨ξ, hξ, hmin⟩ := isCompact_Icc.exists_isMinOn (nonempty_Icc.2 hlt.le) hgcont
  have hmin' : ∀ x ∈ Icc x₁ x₂, g ξ ≤ g x := fun x hx => hmin hx
  -- `ξ` nem lehet a bal végpont
  have hne₁ : ξ ≠ x₁ := by
    intro heq
    obtain ⟨α, hα, hp⟩ := pontnal_csokkeno_ha_derivalt_negativ (hgd x₁ h₁) (by linarith)
    set y : ℝ := x₁ + min α (x₂ - x₁) / 2 with hy
    have hm : 0 < min α (x₂ - x₁) := lt_min hα (by linarith)
    have hyd : |y - x₁| < α := by
      rw [hy]; simp only [add_sub_cancel_left]
      rw [abs_of_pos (by linarith)]
      have : min α (x₂ - x₁) ≤ α := min_le_left _ _
      linarith
    have hylt : y < x₂ := by
      have : min α (x₂ - x₁) ≤ x₂ - x₁ := min_le_right _ _
      rw [hy]; linarith
    have hzd : |x₁ - min α (x₂ - x₁) / 2 - x₁| < α := by
      have h1 : x₁ - min α (x₂ - x₁) / 2 - x₁ = -(min α (x₂ - x₁) / 2) := by ring
      rw [h1, abs_neg, abs_of_pos (by linarith)]
      have : min α (x₂ - x₁) ≤ α := min_le_left _ _
      linarith
    obtain ⟨-, e₂⟩ := hp (x₁ - min α (x₂ - x₁) / 2) y hzd hyd
      (by linarith) (by rw [hy]; linarith)
    have := hmin' y ⟨by rw [hy]; linarith, hylt.le⟩
    rw [heq] at this
    linarith
  -- `ξ` nem lehet a jobb végpont
  have hne₂ : ξ ≠ x₂ := by
    intro heq
    obtain ⟨α, hα, hp⟩ := pontnal_novekedo_ha_derivalt_pozitiv (hgd x₂ h₂) (by linarith)
    set y : ℝ := x₂ - min α (x₂ - x₁) / 2 with hy
    have hm : 0 < min α (x₂ - x₁) := lt_min hα (by linarith)
    have hyd : |y - x₂| < α := by
      rw [hy]; simp only [sub_sub_cancel_left, abs_neg]
      rw [abs_of_pos (by linarith)]
      have : min α (x₂ - x₁) ≤ α := min_le_left _ _
      linarith
    have hygt : x₁ < y := by
      have : min α (x₂ - x₁) ≤ x₂ - x₁ := min_le_right _ _
      rw [hy]; linarith
    have hzd : |x₂ + min α (x₂ - x₁) / 2 - x₂| < α := by
      have h1 : x₂ + min α (x₂ - x₁) / 2 - x₂ = min α (x₂ - x₁) / 2 := by ring
      rw [h1, abs_of_pos (by linarith)]
      have : min α (x₂ - x₁) ≤ α := min_le_left _ _
      linarith
    obtain ⟨e₁, -⟩ := hp y (x₂ + min α (x₂ - x₁) / 2) hyd hzd
      (by rw [hy]; linarith) (by linarith)
    have := hmin' y ⟨hygt.le, by rw [hy]; linarith⟩
    rw [heq] at this
    linarith
  have hξIoo : ξ ∈ Ioo x₁ x₂ :=
    ⟨lt_of_le_of_ne hξ.1 (Ne.symm hne₁), lt_of_le_of_ne hξ.2 hne₂⟩
  -- belső minimumhely: a derivált nulla
  set δ : ℝ := min (ξ - x₁) (x₂ - ξ) with hδdef
  have hδ : 0 < δ := lt_min (by linarith [hξIoo.1]) (by linarith [hξIoo.2])
  have hmem : ∀ x, |x - ξ| < δ → x ∈ Icc x₁ x₂ := by
    intro x hx
    have e1 : |x - ξ| < ξ - x₁ := lt_of_lt_of_le hx (min_le_left _ _)
    have e2 : |x - ξ| < x₂ - ξ := lt_of_lt_of_le hx (min_le_right _ _)
    exact ⟨by linarith [(abs_lt.1 e1).1], by linarith [(abs_lt.1 e2).2]⟩
  have hzero : f' ξ - c = 0 :=
    belso_minimum_derivalt_nulla hδ (fun x hx => hmin' x (hmem x hx)) (hgd ξ (hsub hξ))
  exact ⟨ξ, hξIoo, by linarith⟩

/-- **8.3.2. Tétel.** Ha egy függvény az `x₀` pont valamely környezetében mindenütt
differenciálható, és `x₀`-ban `f'`-nek létezik a határértéke, akkor
`lim_{x→x₀} f'(x) = f'(x₀)`, azaz `f'` az `x₀` pontban szükségképpen folytonos.

*Bizonyítás.* A könyv a derivált Bolzano–Darboux-tulajdonságával érvel; itt a
Lagrange-tételt használjuk: `x` és `x₀` között van olyan `ξ`, amelyre a különbségi
hányados `f'(ξ)`; `x → x₀` esetén `ξ → x₀`, tehát a különbségi hányados határértéke
`A`, azaz `f'(x₀) = A`. -/
theorem derivalt_hatarerteke {f f' : ℝ → ℝ} {x₀ A δ₀ : ℝ} (hδ₀ : 0 < δ₀)
    (hd : ∀ x, |x - x₀| < δ₀ → Derivalt f x (f' x))
    (hlim : CauchyHatarErtek f' x₀ A) : f' x₀ = A := by
  have hderivA : Derivalt f x₀ A := by
    intro ε hε
    obtain ⟨δ, hδ, hp⟩ := hlim ε hε
    refine ⟨min δ δ₀, lt_min hδ hδ₀, fun x hxne hxd => ?_⟩
    have hd1 : |x - x₀| < δ := lt_of_lt_of_le hxd (min_le_left _ _)
    have hd0 : |x - x₀| < δ₀ := lt_of_lt_of_le hxd (min_le_right _ _)
    have habs := abs_lt.1 hd0
    rcases lt_or_gt_of_ne hxne with hlt | hgt
    · -- `x < x₀`
      have hsub : ∀ y ∈ Icc x x₀, |y - x₀| < δ₀ := by
        intro y hy
        rw [abs_lt]
        constructor <;> [linarith [hy.1, habs.1]; linarith [hy.2]]
      obtain ⟨ξ, hξ, hLξ⟩ := lagrange hlt
        (fun y hy => ((cauchyFolytonos_iff_continuousAt f y).1
          (differencialhato_folytonos (hd y (hsub y hy)))).continuousWithinAt)
        (fun y hy => ⟨f' y, hd y (hsub y ⟨hy.1.le, hy.2.le⟩)⟩)
      have heq : f' ξ = (f x₀ - f x) / (x₀ - x) :=
        derivalt_unicitas (hd ξ (hsub ξ ⟨hξ.1.le, hξ.2.le⟩)) hLξ
      have hξne : ξ ≠ x₀ := ne_of_lt hξ.2
      have hξd : |ξ - x₀| < δ := by
        rw [abs_lt]
        constructor
        · have : x < ξ := hξ.1
          have := (abs_lt.1 hd1).1
          linarith
        · linarith [hξ.2]
      have := hp ξ hξne hξd
      rw [heq] at this
      have hquo : kulonbsegiHanyados f x₀ x = (f x₀ - f x) / (x₀ - x) := by
        rw [kulonbsegiHanyados]
        rw [div_eq_div_iff (sub_ne_zero.2 hxne) (sub_ne_zero.2 (ne_of_gt hlt))]
        ring
      rw [hquo]
      exact this
    · -- `x > x₀`
      have hsub : ∀ y ∈ Icc x₀ x, |y - x₀| < δ₀ := by
        intro y hy
        rw [abs_lt]
        constructor <;> [linarith [hy.1]; linarith [hy.2, habs.2]]
      obtain ⟨ξ, hξ, hLξ⟩ := lagrange hgt
        (fun y hy => ((cauchyFolytonos_iff_continuousAt f y).1
          (differencialhato_folytonos (hd y (hsub y hy)))).continuousWithinAt)
        (fun y hy => ⟨f' y, hd y (hsub y ⟨hy.1.le, hy.2.le⟩)⟩)
      have heq : f' ξ = (f x - f x₀) / (x - x₀) :=
        derivalt_unicitas (hd ξ (hsub ξ ⟨hξ.1.le, hξ.2.le⟩)) hLξ
      have hξne : ξ ≠ x₀ := ne_of_gt hξ.1
      have hξd : |ξ - x₀| < δ := by
        rw [abs_lt]
        constructor
        · linarith [hξ.1]
        · have : ξ < x := hξ.2
          have := (abs_lt.1 hd1).2
          linarith
      have := hp ξ hξne hξd
      rw [heq] at this
      rw [kulonbsegiHanyados]
      exact this
  exact derivalt_unicitas (hd x₀ (by simpa using hδ₀)) hderivA

/-! ## 8.4. Szélső érték létezésének elegendő feltétele -/

/-- **8.4.1. Tétel.** Ha `f` az `x₀` pont valamely környezetében mindenütt
differenciálható, és a differenciálhányados-függvény `x₀`-nál előjelet vált
(előtte pozitív, utána negatív), akkor `f`-nek `x₀`-ban szigorú helyi maximuma van.

*Bizonyítás.* A Lagrange-tétel (8.1.2. Tétel) szerint `f` az `x₀` előtti félintervallumon
szigorúan növekedő, az `x₀` utánin szigorúan csökkenő; mivel `f` folytonos `x₀`-ban,
ott szigorú helyi maximuma van. -/
theorem szigoru_maximum_ha_derivalt_jelet_valt {f f' : ℝ → ℝ} {x₀ δ : ℝ}
    (hd : ∀ x, |x - x₀| < δ → Derivalt f x (f' x))
    (hbal : ∀ x, |x - x₀| < δ → x < x₀ → 0 < f' x)
    (hjobb : ∀ x, |x - x₀| < δ → x₀ < x → f' x < 0) :
    ∀ x, |x - x₀| < δ → x ≠ x₀ → f x < f x₀ := by
  intro x hx hne
  have hcont : ∀ y, |y - x₀| < δ → ContinuousAt f y := fun y hy =>
    (cauchyFolytonos_iff_continuousAt f y).1 (differencialhato_folytonos (hd y hy))
  have habs := abs_lt.1 hx
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hsub : ∀ y ∈ Icc x x₀, |y - x₀| < δ := by
      intro y hy
      rw [abs_lt]
      exact ⟨by linarith [hy.1, habs.1], by linarith [hy.2]⟩
    have := szigoruan_novekedo_ha_derivalt_pozitiv
      (f := f) (f' := f') (a := x) (b := x₀)
      (fun y hy => (hcont y (hsub y hy)).continuousWithinAt)
      (fun y hy => hd y (hsub y ⟨hy.1.le, hy.2.le⟩))
      (fun y hy => hbal y (hsub y ⟨hy.1.le, hy.2.le⟩) hy.2)
    exact this x ⟨le_rfl, hlt.le⟩ x₀ ⟨hlt.le, le_rfl⟩ hlt
  · have hsub : ∀ y ∈ Icc x₀ x, |y - x₀| < δ := by
      intro y hy
      rw [abs_lt]
      exact ⟨by linarith [hy.1], by linarith [hy.2, habs.2]⟩
    have hneg : ∀ y ∈ Ioo x₀ x, 0 < -f' y := fun y hy => by
      have := hjobb y (hsub y ⟨hy.1.le, hy.2.le⟩) hy.1
      linarith
    have hdneg : ∀ y ∈ Ioo x₀ x, Derivalt (fun t => -f t) y (-f' y) := by
      intro y hy
      rw [derivalt_iff_hasDerivAt]
      exact ((derivalt_iff_hasDerivAt f y (f' y)).1 (hd y (hsub y ⟨hy.1.le, hy.2.le⟩))).neg
    have := szigoruan_novekedo_ha_derivalt_pozitiv
      (f := fun t => -f t) (f' := fun t => -f' t) (a := x₀) (b := x)
      (fun y hy => ((hcont y (hsub y hy)).neg).continuousWithinAt)
      hdneg hneg
    have h := this x₀ ⟨le_rfl, hgt.le⟩ x ⟨hgt.le, le_rfl⟩ hgt
    simp only at h
    linarith

/-! ## 8.5. Szélső érték meghatározása magasabb rendű deriváltakkal -/

/-- **8.5.1. Tétel.** Ha az `f` függvény az `x₀` pont valamely környezetében
differenciálható, `f'(x₀) = 0`, `f''(x₀)` létezik és `f''(x₀) > 0`, akkor az `f`
függvénynek `x₀`-ban (szigorú helyi) minimuma van.

*Bizonyítás (a könyv gondolatmenete).* Mivel `f''(x₀) > 0`, a 8.2.1. Tétel szerint
`f'` az `x₀` pontnál növekedő, tehát van `x₀`-nak olyan környezete, hogy `x₁ < x₀ < x₂`
esetén `f'(x₁) < f'(x₀) = 0 < f'(x₂)`; azaz `f'` az `x₀` előtt negatív, utána pozitív,
ezért `f` az `x₀` előtt csökkenő, utána növekvő, tehát `x₀`-ban veszi fel a minimumát. -/
theorem szigoru_minimum_masodik_derivalttal {f f' : ℝ → ℝ} {x₀ M δ : ℝ} (hδ : 0 < δ)
    (hd : ∀ x, |x - x₀| < δ → Derivalt f x (f' x)) (h1 : f' x₀ = 0)
    (h2 : Derivalt f' x₀ M) (hM : 0 < M) :
    ∃ δ' > 0, ∀ x, |x - x₀| < δ' → x ≠ x₀ → f x₀ < f x := by
  obtain ⟨α, hα, hp⟩ := pontnal_novekedo_ha_derivalt_pozitiv h2 hM
  refine ⟨min α δ, lt_min hα hδ, fun x hx hne => ?_⟩
  have hxα : |x - x₀| < α := lt_of_lt_of_le hx (min_le_left _ _)
  have hxδ : |x - x₀| < δ := lt_of_lt_of_le hx (min_le_right _ _)
  have habs := abs_lt.1 hxδ
  have hderivsign : ∀ y, |y - x₀| < min α δ → y < x₀ → f' y < 0 := by
    intro y hy hylt
    have hyα : |y - x₀| < α := lt_of_lt_of_le hy (min_le_left _ _)
    have hzd : |x₀ + min α δ / 2 - x₀| < α := by
      have h2 : x₀ + min α δ / 2 - x₀ = min α δ / 2 := by ring
      rw [h2, abs_of_pos (by linarith [lt_min hα hδ])]
      linarith [min_le_left α δ, lt_min hα hδ]
    obtain ⟨e₁, -⟩ := hp y (x₀ + min α δ / 2) hyα hzd hylt (by linarith [lt_min hα hδ])
    rw [h1] at e₁
    exact e₁
  have hderivsign' : ∀ y, |y - x₀| < min α δ → x₀ < y → 0 < f' y := by
    intro y hy hygt
    have hyα : |y - x₀| < α := lt_of_lt_of_le hy (min_le_left _ _)
    obtain ⟨-, e₂⟩ := hp (x₀ - min α δ / 2) y
      (by rw [sub_sub_cancel_left, abs_neg, abs_of_pos] <;>
        [linarith [min_le_left α δ]; linarith [lt_min hα hδ]])
      hyα (by linarith [lt_min hα hδ]) hygt
    rw [h1] at e₂
    exact e₂
  have hcont : ∀ y, |y - x₀| < δ → ContinuousAt f y := fun y hy =>
    (cauchyFolytonos_iff_continuousAt f y).1 (differencialhato_folytonos (hd y hy))
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · -- `x < x₀`: `f` szigorúan csökkenő `[x, x₀]`-n
    have hsub : ∀ y ∈ Icc x x₀, |y - x₀| < min α δ := by
      intro y hy
      rw [abs_lt]
      exact ⟨by linarith [hy.1, (abs_lt.1 hx).1], by linarith [hy.2, lt_min hα hδ]⟩
    have hdneg : ∀ y ∈ Ioo x x₀, Derivalt (fun t => -f t) y (-f' y) := by
      intro y hy
      rw [derivalt_iff_hasDerivAt]
      exact ((derivalt_iff_hasDerivAt f y (f' y)).1
        (hd y (lt_of_lt_of_le (hsub y ⟨hy.1.le, hy.2.le⟩) (min_le_right _ _)))).neg
    have := szigoruan_novekedo_ha_derivalt_pozitiv
      (f := fun t => -f t) (f' := fun t => -f' t) (a := x) (b := x₀)
      (fun y hy => ((hcont y (lt_of_lt_of_le (hsub y hy) (min_le_right _ _))).neg).continuousWithinAt)
      hdneg
      (fun y hy => by
        have := hderivsign y (hsub y ⟨hy.1.le, hy.2.le⟩) hy.2
        linarith)
    have h := this x ⟨le_rfl, hlt.le⟩ x₀ ⟨hlt.le, le_rfl⟩ hlt
    simp only at h
    linarith
  · -- `x > x₀`: `f` szigorúan növekedő `[x₀, x]`-n
    have hsub : ∀ y ∈ Icc x₀ x, |y - x₀| < min α δ := by
      intro y hy
      rw [abs_lt]
      exact ⟨by linarith [hy.1, lt_min hα hδ], by linarith [hy.2, (abs_lt.1 hx).2]⟩
    have := szigoruan_novekedo_ha_derivalt_pozitiv
      (f := f) (f' := f') (a := x₀) (b := x)
      (fun y hy => (hcont y (lt_of_lt_of_le (hsub y hy) (min_le_right _ _))).continuousWithinAt)
      (fun y hy => hd y (lt_of_lt_of_le (hsub y ⟨hy.1.le, hy.2.le⟩) (min_le_right _ _)))
      (fun y hy => hderivsign' y (hsub y ⟨hy.1.le, hy.2.le⟩) hy.1)
    exact this x₀ ⟨le_rfl, hgt.le⟩ x ⟨hgt.le, le_rfl⟩ hgt

end Leindler.Ch08
