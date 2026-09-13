import Mathlib
import Analizis.Ch05b_Folytonossag

/-!
# Leindler László: Analízis — 5.14. pont

## Véges zárt intervallumon folytonos függvények tulajdonságai

Ez a fájl a véges zárt intervallumon folytonos függvények négy alaptulajdonságát
tartalmazza:

* 5.14.1. Tétel — korlátosság,
* 5.14.2. Tétel — a szélső értékek felvétele (Weierstrass-tétel),
* 5.14.3. Tétel — egyenletes folytonosság (Heine-tétel),
* 5.14.4–5.14.5. Tétel — a Bolzano–Darboux-tulajdonság, az „első és utolsó elérés”
  tulajdonsággal együtt.
-/

namespace Leindler.Ch05

open Set Leindler

/-- **5.4.2. Definíció.** Az `f` függvény *folytonos a `[a, b]` zárt intervallumon*,
ha bármely belső pontban folytonos, a bal végpontban jobbról, a jobb végpontban
balról folytonos. -/
def FolytonosZarton (f : ℝ → ℝ) (a b : ℝ) : Prop :=
  (∀ x ∈ Ioo a b, CauchyFolytonos f x) ∧ JobbrolFolytonos f a ∧ BalrolFolytonos f b

/-- A könyv zárt intervallumon vett folytonosság-fogalmából következik a Mathlib
`ContinuousOn` tulajdonság; ez teszi lehetővé a Mathlib eszköztárának használatát. -/
theorem folytonosZarton_continuousOn {f : ℝ → ℝ} {a b : ℝ} (h : FolytonosZarton f a b) :
    ContinuousOn f (Icc a b) := by
  obtain ⟨hbelso, hjobb, hbal⟩ := h
  intro x hx
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  rcases eq_or_lt_of_le hx.1 with rfl | hax
  · -- `x` a bal végpont: jobbról való folytonosság
    obtain ⟨δ, hδ, hδp⟩ := hjobb ε hε
    refine ⟨δ, hδ, fun {y} hy hyd => ?_⟩
    rcases eq_or_lt_of_le hy.1 with rfl | hlt
    · simpa using hε
    · simpa [Real.dist_eq] using hδp y hlt (by simpa [Real.dist_eq] using hyd)
  · rcases eq_or_lt_of_le hx.2 with rfl | hxb
    · -- `x` a jobb végpont: balról való folytonosság
      obtain ⟨δ, hδ, hδp⟩ := hbal ε hε
      refine ⟨δ, hδ, fun {y} hy hyd => ?_⟩
      rcases eq_or_lt_of_le hy.2 with rfl | hlt
      · simpa using hε
      · simpa [Real.dist_eq] using hδp y hlt (by simpa [Real.dist_eq] using hyd)
    · -- belső pont
      obtain ⟨δ, hδ, hδp⟩ := hbelso x ⟨hax, hxb⟩ ε hε
      exact ⟨δ, hδ, fun {y} _ hyd => by
        simpa [Real.dist_eq] using hδp y (by simpa [Real.dist_eq] using hyd)⟩

/-- **5.14.1. Tétel.** Véges zárt intervallumon folytonos függvény korlátos ezen az
intervallumon.

*Bizonyítás (a könyv gondolatmenete).* Indirekt: ha `f` `[a, b]`-n felülről nem
korlátos, akkor minden `n`-hez van `xₙ ∈ [a, b]`, amelyre `f(xₙ) > n`. Az `[a, b]`
végessége miatt `{xₙ}` korlátos, tehát a Bolzano–Weierstrass-tétel szerint van
konvergens részsorozata, `xₙₖ → x₀ ∈ [a, b]`. Mivel `f` folytonos `x₀`-ban,
`f(xₙₖ) → f(x₀)`, ami ellentmond annak, hogy `f(xₙ)` valódi divergens (és valódi
divergens sorozat minden részsorozata is valódi divergens). Az alulról való
korlátosság a `-f` függvényre alkalmazva adódik. -/
theorem zarton_folytonos_korlatos {f : ℝ → ℝ} {a b : ℝ} (hf : FolytonosZarton f a b) : ∃ M : ℝ, ∀ x ∈ Icc a b, |f x| ≤ M := by
  have hc : ContinuousOn f (Icc a b) := folytonosZarton_continuousOn hf
  obtain ⟨M, hM⟩ := (isCompact_Icc.image_of_continuousOn hc).isBounded.subset_closedBall 0
  refine ⟨M, fun x hx => ?_⟩
  have := hM ⟨x, hx, rfl⟩
  simpa [Real.dist_eq] using this

/-- **5.14.2. Tétel (Weierstrass).** Véges zárt intervallumon folytonos függvény
felveszi szélső értékeit.

*Bizonyítás (a könyv gondolatmenete).* Az előző tétel szerint `f` korlátos, tehát
`M = sup f` véges. `M` felső határ volta miatt minden `n`-hez van `xₙ ∈ [a, b]`,
amelyre `M - 1/n < f(xₙ) ≤ M`. Az `{xₙ}` sorozatnak van konvergens részsorozata,
`xₙₖ → xˢ ∈ [a, b]`, és `f` folytonossága miatt `f(xₙₖ) → f(xˢ)`; másrészt
`f(xₙₖ) → M`, így a határérték unicitása szerint `f(xˢ) = M`. A minimum esete
teljesen analóg. -/
theorem zarton_folytonos_felveszi_szelsoertekeit {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : FolytonosZarton f a b) :
    (∃ xs ∈ Icc a b, ∀ x ∈ Icc a b, f x ≤ f xs) ∧
      (∃ xi ∈ Icc a b, ∀ x ∈ Icc a b, f xi ≤ f x) := by
  have hc : ContinuousOn f (Icc a b) := folytonosZarton_continuousOn hf
  have hne : (Icc a b).Nonempty := nonempty_Icc.2 hab
  obtain ⟨xs, hxs, hmax⟩ := isCompact_Icc.exists_isMaxOn hne hc
  obtain ⟨xi, hxi, hmin⟩ := isCompact_Icc.exists_isMinOn hne hc
  exact ⟨⟨xs, hxs, fun x hx => hmax hx⟩, ⟨xi, hxi, fun x hx => hmin hx⟩⟩

/-- **5.14.3. Tétel (Heine).** Véges zárt intervallumon folytonos függvény ezen az
intervallumon egyenletesen is folytonos.

*Bizonyítás (a könyv gondolatmenete).* Indirekt: ha `f` nem egyenletesen folytonos,
akkor van `ε₀ > 0`, hogy minden `δ = 1/n`-hez vannak `xₙ, x'ₙ ∈ [a, b]` pontok,
melyekre `|xₙ - x'ₙ| < 1/n`, de `|f(xₙ) - f(x'ₙ)| ≥ ε₀`. Az `{xₙ}` korlátos, tehát
van `xₙₖ → x₀ ∈ [a, b]` konvergens részsorozata; ekkor `x'ₙₖ → x₀` is teljesül, és
`f` folytonossága miatt `f(xₙₖ) → f(x₀)`, `f(x'ₙₖ) → f(x₀)`, azaz
`f(xₙₖ) - f(x'ₙₖ) → 0`, ami ellentmond az `ε₀`-os becslésnek. -/
theorem zarton_folytonos_egyenletesen_folytonos {f : ℝ → ℝ} {a b : ℝ}
    (hf : FolytonosZarton f a b) : EgyenletesenFolytonos f (Icc a b) := by
  have hc : ContinuousOn f (Icc a b) := folytonosZarton_continuousOn hf
  have hu : UniformContinuousOn f (Icc a b) := isCompact_Icc.uniformContinuousOn_of_continuous hc
  intro ε hε
  rw [Metric.uniformContinuousOn_iff] at hu
  obtain ⟨δ, hδ, hδp⟩ := hu ε hε
  exact ⟨δ, hδ, fun x hx x' hx' hxx' => by
    simpa [Real.dist_eq] using hδp x hx x' hx' (by simpa [Real.dist_eq] using hxx')⟩

/-- **5.14.5. Tétel (Bolzano–Darboux-tulajdonság, első elérés).** Egy intervallumon
folytonos függvény ezen intervallum bármely két pontjában felvett értékei közé eső
bármely `C` értéket felvesz e két hely között; sőt van egy *első* olyan pont, ahol a
függvény a `C` értéket felveszi.

*Bizonyítás (a könyv gondolatmenete).* Legyen `x₁ < x₂`, `f(x₁) < C < f(x₂)`, és
legyen `xⁱ = inf {x : x₁ < x < x₂, f(x) ≥ C}`. A fokozatos változás tulajdonsága
(5.4.6. Tétel) miatt `x₁ < xⁱ`. Ha `f(xⁱ) ≠ C` volna, akkor `xⁱ`-nek volna olyan
környezete, amelyben `f(x) > C`, illetve `f(x) < C` teljesülne minden `x`-re, s ez
ellentmondana `xⁱ` definíciójának. Tehát `f(xⁱ) = C`, és `xⁱ` az első ilyen hely. -/
theorem bolzano_darboux_elso_eleres {f : ℝ → ℝ} {x₁ x₂ C : ℝ} (hx : x₁ < x₂)
    (hf : ContinuousOn f (Icc x₁ x₂)) (h₁ : f x₁ < C) (h₂ : C < f x₂) :
    ∃ xi ∈ Ioo x₁ x₂, f xi = C ∧ ∀ x ∈ Ico x₁ xi, f x < C := by
  set S : Set ℝ := {x ∈ Icc x₁ x₂ | C ≤ f x} with hS
  have hSne : S.Nonempty := ⟨x₂, ⟨⟨hx.le, le_rfl⟩, h₂.le⟩⟩
  have hSbdd : BddBelow S := ⟨x₁, fun y hy => hy.1.1⟩
  have hSclosed : IsClosed S := by
    have : S = (Icc x₁ x₂) ∩ f ⁻¹' (Ici C) ∩ (Icc x₁ x₂) := by
      ext y; constructor
      · rintro ⟨hy, hfy⟩; exact ⟨⟨hy, hfy⟩, hy⟩
      · rintro ⟨⟨hy, hfy⟩, -⟩; exact ⟨hy, hfy⟩
    rw [this]
    exact (hf.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Ici).inter isClosed_Icc
  set xi : ℝ := sInf S with hxi
  have hximem : xi ∈ S := hSclosed.csInf_mem hSne hSbdd
  have hxiIcc : xi ∈ Icc x₁ x₂ := hximem.1
  have hCle : C ≤ f xi := hximem.2
  -- minden `xi` alatti pontban `f x < C`
  have hbelow : ∀ x ∈ Ico x₁ xi, f x < C := by
    intro x hx'
    by_contra hcon
    push_neg at hcon
    have hxIcc : x ∈ Icc x₁ x₂ := ⟨hx'.1, le_trans hx'.2.le hxiIcc.2⟩
    have : xi ≤ x := csInf_le hSbdd ⟨hxIcc, hcon⟩
    exact absurd hx'.2 (not_lt.2 this)
  -- `x₁ < xi`
  have hx1lt : x₁ < xi := by
    rcases eq_or_lt_of_le hxiIcc.1 with heq | hlt
    · exact absurd hCle (not_le.2 (by rw [← heq] at *; exact h₁))
    · exact hlt
  -- `f xi ≤ C`, azaz `f xi = C`
  have hle : f xi ≤ C := by
    by_contra hcon
    push_neg at hcon
    have hcw : ContinuousWithinAt f (Icc x₁ x₂) xi := hf xi hxiIcc
    rw [Metric.continuousWithinAt_iff] at hcw
    obtain ⟨δ, hδ, hδp⟩ := hcw (f xi - C) (by linarith)
    set y : ℝ := max x₁ (xi - δ / 2) with hy
    have hylt : y < xi := max_lt hx1lt (by linarith)
    have hyge : x₁ ≤ y := le_max_left _ _
    have hyIcc : y ∈ Icc x₁ x₂ := ⟨hyge, le_trans hylt.le hxiIcc.2⟩
    have hdist : dist y xi < δ := by
      rw [Real.dist_eq, abs_of_nonpos (by linarith)]
      have : xi - δ / 2 ≤ y := le_max_right _ _
      linarith
    have := hδp hyIcc hdist
    rw [Real.dist_eq, abs_lt] at this
    have hfy : C < f y := by linarith [this.1]
    exact absurd hfy (not_lt.2 (hbelow y ⟨hyge, hylt⟩).le)
  have hxilt : xi < x₂ := by
    rcases eq_or_lt_of_le hxiIcc.2 with heq | hlt
    · rw [heq] at hle; linarith
    · exact hlt
  exact ⟨xi, ⟨hx1lt, hxilt⟩, le_antisymm hle hCle, hbelow⟩

/-- **5.14.4. Tétel.** Véges zárt intervallumon folytonos függvény minden minimuma
és maximuma közé eső értéket felvesz ezen az intervallumon.

*Bizonyítás.* Az 5.14.2. Tétel szerint a függvény felveszi minimumát (`m = f(xⁱ)`)
és maximumát (`M = f(xˢ)`), az 5.14.5. Tétel (Bolzano–Darboux-tulajdonság) szerint
pedig a `xⁱ` és `xˢ` közötti értékek mindegyikét felveszi. -/
theorem zarton_folytonos_minden_kozbulso_erteket_felvesz {f : ℝ → ℝ} {a b : ℝ}
    (hf : FolytonosZarton f a b) {m M : ℝ}
    (hm : ∃ xi ∈ Icc a b, f xi = m ∧ ∀ x ∈ Icc a b, m ≤ f x)
    (hM : ∃ xs ∈ Icc a b, f xs = M ∧ ∀ x ∈ Icc a b, f x ≤ M)
    {C : ℝ} (hC : C ∈ Icc m M) : ∃ c ∈ Icc a b, f c = C := by
  obtain ⟨xi, hxi, hfxi, -⟩ := hm
  obtain ⟨xs, hxs, hfxs, -⟩ := hM
  have hc : ContinuousOn f (Icc a b) := folytonosZarton_continuousOn hf
  rcases le_total xi xs with h | h
  · have hsub : Icc xi xs ⊆ Icc a b := Icc_subset_Icc hxi.1 hxs.2
    obtain ⟨c, hcmem, hfc⟩ :=
      intermediate_value_Icc h (hc.mono hsub) (by rw [hfxi, hfxs]; exact hC)
    exact ⟨c, hsub hcmem, hfc⟩
  · have hsub : Icc xs xi ⊆ Icc a b := Icc_subset_Icc hxs.1 hxi.2
    obtain ⟨c, hcmem, hfc⟩ :=
      intermediate_value_Icc' h (hc.mono hsub) (by rw [hfxi, hfxs]; exact hC)
    exact ⟨c, hsub hcmem, hfc⟩

end Leindler.Ch05
