import Mathlib
import Analizis.Ch05b_Folytonossag

/-!
# Leindler László: Analízis — 5.15–5.19. pont

## Függvények határértéke

Ez a fájl a függvényhatárérték Heine- és Cauchy-féle definícióját és ezek
ekvivalenciáját (5.15), a féloldali határértékeket (5.15.4–5.15.6), a szakadási
helyek fajtáit (5.16), a végtelen határértékeket (5.17), valamint a végtelenben vett
határértékeket (5.18–5.19) tartalmazza.
-/

namespace Leindler.Ch05

open Set Leindler

/-! ## 5.15. Függvények határértéke -/

/-- **5.15.1. Definíció (Heine).** Az `f` függvénynek az `x₀` pontban létezik a
határértéke és az `c`, ha valahányszor `xₙ → x₀`, `xₙ ≠ x₀`, mindannyiszor
`f(xₙ) → c`. -/
def HeineHatarErtek (f : ℝ → ℝ) (x₀ c : ℝ) : Prop :=
  ∀ x : Ch04.Sorozat, (∀ n, x n ≠ x₀) → Ch04.HatarErtek x x₀ →
    Ch04.HatarErtek (fun n => f (x n)) c

/-- **5.15.2. Definíció (Cauchy).** Az `f` függvénynek `x₀`-ban létezik a határértéke
és az `c`, ha bármely `ε > 0`-hoz megadható olyan `δ > 0`, hogy ha `|x - x₀| < δ` és
`x ≠ x₀`, akkor `|f(x) - c| < ε`. -/
def CauchyHatarErtek (f : ℝ → ℝ) (x₀ c : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x : ℝ, x ≠ x₀ → |x - x₀| < δ → |f x - c| < ε

/-- **5.15. Tétel.** A határérték Heine-féle és Cauchy-féle definíciója ekvivalens.

*Bizonyítás.* Pontosan úgy, mint a folytonossági definíciók ekvivalenciája
(5.2.3. Tétel): Heine ⇒ Cauchy indirekt, a `δ = 1/n` választással kapott „rossz”
pontok sorozatával; Cauchy ⇒ Heine pedig direkt módon. -/
theorem heineHatarErtek_iff_cauchyHatarErtek (f : ℝ → ℝ) (x₀ c : ℝ) :
    HeineHatarErtek f x₀ c ↔ CauchyHatarErtek f x₀ c := by
  constructor
  · intro hHeine
    by_contra hC
    unfold CauchyHatarErtek at hC
    push_neg at hC
    obtain ⟨ε₀, hε₀, hbad⟩ := hC
    choose x hxne hxd hfx using fun n : ℕ => hbad (1 / (n + 1 : ℝ)) (by positivity)
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
    obtain ⟨N, hN⟩ := hHeine x hxne hxlim ε₀ hε₀
    exact absurd (hN (N + 1) (by omega)) (not_lt.2 (hfx (N + 1)))
  · intro hC x hxne hx ε hε
    obtain ⟨δ, hδ, hδp⟩ := hC ε hε
    obtain ⟨N, hN⟩ := hx δ hδ
    exact ⟨N, fun n hn => hδp (x n) (hxne n) (hN n hn)⟩

/-- A könyv határérték-fogalma megegyezik a Mathlib „kilyukasztott környezet szerinti”
határértékével (`Filter.Tendsto f (nhdsWithin x₀ {x₀}ᶜ) (nhds c)`). -/
theorem cauchyHatarErtek_iff_tendsto (f : ℝ → ℝ) (x₀ c : ℝ) :
    CauchyHatarErtek f x₀ c ↔ Filter.Tendsto f (nhdsWithin x₀ {x₀}ᶜ) (nhds c) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  constructor
  · intro h ε hε
    obtain ⟨δ, hδ, hδp⟩ := h ε hε
    exact ⟨δ, hδ, fun {x} hx hxd => by
      simpa [Real.dist_eq] using hδp x hx (by simpa [Real.dist_eq] using hxd)⟩
  · intro h ε hε
    obtain ⟨δ, hδ, hδp⟩ := h ε hε
    exact ⟨δ, hδ, fun x hx hxd => by
      simpa [Real.dist_eq] using hδp (x := x) hx (by simpa [Real.dist_eq] using hxd)⟩

/-- A határérték egyértelmű (a Heine-féle definícióból és a sorozatok határértékének
unicitásából adódik). -/
theorem hatarErtek_unicitas {f : ℝ → ℝ} {x₀ c c' : ℝ}
    (h : CauchyHatarErtek f x₀ c) (h' : CauchyHatarErtek f x₀ c') : c = c' := by
  by_contra hne
  set ρ : ℝ := |c - c'| with hρ
  have hρpos : 0 < ρ := abs_pos.2 (sub_ne_zero.2 hne)
  obtain ⟨δ₁, hδ₁, h₁⟩ := h (ρ / 2) (by linarith)
  obtain ⟨δ₂, hδ₂, h₂⟩ := h' (ρ / 2) (by linarith)
  set x : ℝ := x₀ + min δ₁ δ₂ / 2 with hx
  have hmin : 0 < min δ₁ δ₂ := lt_min hδ₁ hδ₂
  have hxne : x ≠ x₀ := by simp [hx]; linarith
  have hxd : |x - x₀| < min δ₁ δ₂ := by
    rw [hx]
    simp only [add_sub_cancel_left]
    rw [abs_of_pos (by linarith)]
    linarith
  have e₁ := h₁ x hxne (lt_of_lt_of_le hxd (min_le_left _ _))
  have e₂ := h₂ x hxne (lt_of_lt_of_le hxd (min_le_right _ _))
  have : ρ ≤ |f x - c| + |f x - c'| := by
    calc ρ = |(f x - c') - (f x - c)| := by rw [hρ]; congr 1; ring
      _ ≤ |f x - c'| + |f x - c| := abs_sub _ _
      _ = |f x - c| + |f x - c'| := by ring
  linarith

/-! ### 5.15.3. Tétel: a határérték tulajdonságai -/

/-- **5.15.3.2. Tétel** (összeg). -/
theorem hatarErtek_add {f g : ℝ → ℝ} {x₀ c d : ℝ}
    (hf : HeineHatarErtek f x₀ c) (hg : HeineHatarErtek g x₀ d) :
    HeineHatarErtek (fun x => f x + g x) x₀ (c + d) :=
  fun x hxne hx => Ch04.hatarErtek_add (hf x hxne hx) (hg x hxne hx)

/-- **5.15.3.2. Tétel** (különbség). -/
theorem hatarErtek_sub {f g : ℝ → ℝ} {x₀ c d : ℝ}
    (hf : HeineHatarErtek f x₀ c) (hg : HeineHatarErtek g x₀ d) :
    HeineHatarErtek (fun x => f x - g x) x₀ (c - d) :=
  fun x hxne hx => Ch04.hatarErtek_sub (hf x hxne hx) (hg x hxne hx)

/-- **5.15.3.2. Tétel** (szorzat). -/
theorem hatarErtek_mul {f g : ℝ → ℝ} {x₀ c d : ℝ}
    (hf : HeineHatarErtek f x₀ c) (hg : HeineHatarErtek g x₀ d) :
    HeineHatarErtek (fun x => f x * g x) x₀ (c * d) :=
  fun x hxne hx => Ch04.hatarErtek_mul (hf x hxne hx) (hg x hxne hx)

/-- **5.15.3.2. Tétel** (hányados, ha a nevező határértéke nem `0`). -/
theorem hatarErtek_div {f g : ℝ → ℝ} {x₀ c d : ℝ}
    (hf : HeineHatarErtek f x₀ c) (hg : HeineHatarErtek g x₀ d) (hd : d ≠ 0) :
    HeineHatarErtek (fun x => f x / g x) x₀ (c / d) :=
  fun x hxne hx => Ch04.hatarErtek_div (hf x hxne hx) (hg x hxne hx) hd

/-- **5.15.3.5. Tétel.** Az `f` függvény `x₀`-ban akkor és csak akkor folytonos, ha
létezik határértéke, és `lim_{x→x₀} f(x) = f(x₀)`. -/
theorem cauchyFolytonos_iff_hatarErtek (f : ℝ → ℝ) (x₀ : ℝ) :
    CauchyFolytonos f x₀ ↔ CauchyHatarErtek f x₀ (f x₀) := by
  constructor
  · intro h ε hε
    obtain ⟨δ, hδ, hδp⟩ := h ε hε
    exact ⟨δ, hδ, fun x _ hxd => hδp x hxd⟩
  · intro h ε hε
    obtain ⟨δ, hδ, hδp⟩ := h ε hε
    refine ⟨δ, hδ, fun x hxd => ?_⟩
    rcases eq_or_ne x x₀ with rfl | hne
    · simpa using hε
    · exact hδp x hne hxd

/-! ### 5.15.4–5.15.6. Féloldali határértékek -/

/-- **5.15.5. Definíció (Cauchy).** Az `f`-nek `x₀`-ban létezik a *jobb oldali*
határértéke és az `c`. -/
def JobbHatarErtek (f : ℝ → ℝ) (x₀ c : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x : ℝ, x₀ < x → |x - x₀| < δ → |f x - c| < ε

/-- **5.15.5. Definíció (Cauchy).** Az `f`-nek `x₀`-ban létezik a *bal oldali*
határértéke és az `c`. -/
def BalHatarErtek (f : ℝ → ℝ) (x₀ c : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x : ℝ, x < x₀ → |x - x₀| < δ → |f x - c| < ε

/-- **5.15.6. Tétel.** Az `f` függvénynek `x₀`-ban akkor és csak akkor létezik
határértéke, ha létezik a jobb és bal oldali határértéke, és ezek egyenlők.

*Bizonyítás.* Ha a határérték létezik, akkor a féloldali határértékek nyilvánvalóan
léteznek és egyenlők vele. Fordítva: bármely `xₙ → x₀`, `xₙ ≠ x₀` sorozat felbontható
két olyan részsorozatra, amelyek tagjai `x₀`-nál nagyobbak, illetve kisebbek — az
`ε`-hoz tartozó két `δ` közül a kisebbet választva a becslés mindkét esetben
teljesül. -/
theorem cauchyHatarErtek_iff_feloldali (f : ℝ → ℝ) (x₀ c : ℝ) :
    CauchyHatarErtek f x₀ c ↔ JobbHatarErtek f x₀ c ∧ BalHatarErtek f x₀ c := by
  constructor
  · intro h
    constructor
    · intro ε hε
      obtain ⟨δ, hδ, hδp⟩ := h ε hε
      exact ⟨δ, hδ, fun x hlt hxd => hδp x (ne_of_gt hlt) hxd⟩
    · intro ε hε
      obtain ⟨δ, hδ, hδp⟩ := h ε hε
      exact ⟨δ, hδ, fun x hlt hxd => hδp x (ne_of_lt hlt) hxd⟩
  · rintro ⟨hj, hb⟩ ε hε
    obtain ⟨δ₁, hδ₁, h₁⟩ := hj ε hε
    obtain ⟨δ₂, hδ₂, h₂⟩ := hb ε hε
    refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun x hxne hxd => ?_⟩
    rcases lt_trichotomy x x₀ with hlt | heq | hgt
    · exact h₂ x hlt (lt_of_lt_of_le hxd (min_le_right _ _))
    · exact absurd heq hxne
    · exact h₁ x hgt (lt_of_lt_of_le hxd (min_le_left _ _))

/-! ## 5.16. Szakadási helyek fajai -/

/-- **5.16.1. Definíció.** *Megszüntethető szakadási helye* van `f`-nek `x₀`-ban, ha
itt létezik a határértéke, de az nem egyenlő az `f(x₀)` helyettesítési értékkel. -/
def MegszuntethetoSzakadas (f : ℝ → ℝ) (x₀ : ℝ) : Prop :=
  ∃ c, CauchyHatarErtek f x₀ c ∧ c ≠ f x₀

/-- **5.16.2. Definíció.** *Elsőfajú szakadási helye* van `f`-nek `x₀`-ban, ha létezik
a jobb és bal oldali határértéke, de ezek különbözők. -/
def ElsofajuSzakadas (f : ℝ → ℝ) (x₀ : ℝ) : Prop :=
  ∃ cj cb, JobbHatarErtek f x₀ cj ∧ BalHatarErtek f x₀ cb ∧ cj ≠ cb

/-- **5.16.3. Definíció.** *Másodfajú szakadási helye* van `f`-nek `x₀`-ban, ha vagy a
jobb, vagy a bal oldali, vagy egyik féloldali határértéke sem létezik. -/
def MasodfajuSzakadas (f : ℝ → ℝ) (x₀ : ℝ) : Prop :=
  (¬ ∃ c, JobbHatarErtek f x₀ c) ∨ (¬ ∃ c, BalHatarErtek f x₀ c)

/-- A szignumfüggvény: `sign x = -1` (`x < 0`), `0` (`x = 0`), `1` (`x > 0`). -/
noncomputable def szignum (x : ℝ) : ℝ := if x < 0 then -1 else if x = 0 then 0 else 1

/-- A szignumfüggvény jobb oldali határértéke a `0` helyen `1`. -/
theorem szignum_jobb : JobbHatarErtek szignum 0 1 := by
  intro ε hε
  refine ⟨1, one_pos, fun x hx _ => ?_⟩
  have : szignum x = 1 := by
    simp [szignum, not_lt.2 hx.le, ne_of_gt hx]
  simpa [this] using hε

/-- A szignumfüggvény bal oldali határértéke a `0` helyen `-1`. -/
theorem szignum_bal : BalHatarErtek szignum 0 (-1) := by
  intro ε hε
  refine ⟨1, one_pos, fun x hx _ => ?_⟩
  have : szignum x = -1 := by simp [szignum, hx]
  simpa [this] using hε

/-- **5.16.2. Példa.** A szignumfüggvénynek a `0` helyen elsőfajú szakadása van. -/
theorem szignum_elsofaju : ElsofajuSzakadas szignum 0 :=
  ⟨1, -1, szignum_jobb, szignum_bal, by norm_num⟩

/-! ## 5.17. Végtelen határértékek -/

/-- **5.17.1. Definíció (Heine).** Az `f` függvénynek `x₀`-ban a határértéke `+∞`, ha
valahányszor `xₙ → x₀`, `xₙ ≠ x₀`, mindannyiszor `f(xₙ) → +∞`. -/
def HeinePlusVegtelenHatarErtek (f : ℝ → ℝ) (x₀ : ℝ) : Prop :=
  ∀ x : Ch04.Sorozat, (∀ n, x n ≠ x₀) → Ch04.HatarErtek x x₀ →
    Ch04.PlusVegtelenbeDivergal (fun n => f (x n))

/-- **5.17.2. Definíció (Cauchy).** Az `f`-nek `x₀`-ban a határértéke `+∞`, ha bármely
`M` számhoz megadható olyan `δ > 0`, hogy ha `|x - x₀| < δ`, `x ≠ x₀`, akkor
`f(x) ≥ M`. -/
def CauchyPlusVegtelenHatarErtek (f : ℝ → ℝ) (x₀ : ℝ) : Prop :=
  ∀ M : ℝ, ∃ δ > 0, ∀ x : ℝ, x ≠ x₀ → |x - x₀| < δ → M ≤ f x

/-- **5.17. Tétel.** A végtelen határérték két definíciója egyenértékű.

*Bizonyítás.* Ugyanaz a séma, mint az 5.2.3. Tételnél: Heine ⇒ Cauchy indirekt
(a `δ = 1/n` választással kapott „rossz” pontok sorozatával), Cauchy ⇒ Heine direkt
módon. -/
theorem heinePlusVegtelen_iff_cauchyPlusVegtelen (f : ℝ → ℝ) (x₀ : ℝ) :
    HeinePlusVegtelenHatarErtek f x₀ ↔ CauchyPlusVegtelenHatarErtek f x₀ := by
  constructor
  · intro hHeine
    by_contra hC
    unfold CauchyPlusVegtelenHatarErtek at hC
    push_neg at hC
    obtain ⟨M₀, hbad⟩ := hC
    choose x hxne hxd hfx using fun n : ℕ => hbad (1 / (n + 1 : ℝ)) (by positivity)
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
    obtain ⟨N, hN⟩ := hHeine x hxne hxlim M₀
    exact absurd (hN (N + 1) (by omega)) (not_lt.2 (hfx (N + 1)).le)
  · intro hC x hxne hx M
    obtain ⟨δ, hδ, hδp⟩ := hC (M + 1)
    obtain ⟨N, hN⟩ := hx δ hδ
    exact ⟨N, fun n hn => lt_of_lt_of_le (by linarith) (hδp (x n) (hxne n) (hN n hn))⟩

/-- **5.17. Példa.** Az `f(x) = 1/x²` függvénynek a `0` helyen a határértéke `+∞`. -/
theorem egy_per_x_negyzet_vegtelen :
    CauchyPlusVegtelenHatarErtek (fun x : ℝ => 1 / x ^ 2) 0 := by
  intro M
  refine ⟨1 / (|M| + 1), by positivity, fun x hx hxd => ?_⟩
  have hx0 : x ≠ 0 := by simpa using hx
  have habs : 0 < |x| := abs_pos.2 hx0
  have hM : (0 : ℝ) < |M| + 1 := by positivity
  have h1 : |x| < 1 / (|M| + 1) := by simpa using hxd
  have h2 : |M| + 1 < 1 / |x| := by
    rw [lt_div_iff₀ habs]
    rw [lt_div_iff₀ hM] at h1
    linarith
  have hsq : (1 : ℝ) / x ^ 2 = (1 / |x|) ^ 2 := by
    rw [div_pow, one_pow, sq_abs]
  show M ≤ 1 / x ^ 2
  rw [hsq]
  nlinarith [abs_nonneg M, le_abs_self M]

/-! ## 5.18–5.19. Határérték a végtelenben -/

/-- **5.18. Definíció.** Az `f` függvénynek a `+∞`-ben a határértéke `c`, ha bármely
`ε > 0`-hoz van olyan `K`, hogy `x > K` esetén `|f(x) - c| < ε`. -/
def HatarErtekVegtelenben (f : ℝ → ℝ) (c : ℝ) : Prop :=
  ∀ ε > 0, ∃ K : ℝ, ∀ x : ℝ, K < x → |f x - c| < ε

/-- **5.19. Definíció.** Az `f` függvénynek a `+∞`-ben a határértéke `+∞`, ha bármely
`M`-hez van olyan `K`, hogy `x > K` esetén `f(x) ≥ M`. -/
def VegtelenHatarErtekVegtelenben (f : ℝ → ℝ) : Prop :=
  ∀ M : ℝ, ∃ K : ℝ, ∀ x : ℝ, K < x → M ≤ f x

/-- **5.18. Példa.** `lim_{x→∞} 1/x = 0`. -/
theorem egy_per_x_vegtelenben : HatarErtekVegtelenben (fun x : ℝ => 1 / x) 0 := by
  intro ε hε
  refine ⟨1 / ε, fun x hx => ?_⟩
  have hxpos : 0 < x := lt_trans (by positivity) hx
  have : 1 / x < ε := by
    rw [div_lt_iff₀ hxpos]
    rw [div_lt_iff₀ hε] at hx
    linarith
  rw [sub_zero, abs_of_pos (by positivity)]
  exact this

/-- **5.19. Példa.** `lim_{x→∞} x² = +∞`. -/
theorem x_negyzet_vegtelenben : VegtelenHatarErtekVegtelenben (fun x : ℝ => x ^ 2) := by
  intro M
  refine ⟨|M| + 1, fun x hx => ?_⟩
  have h0 : (0 : ℝ) < x := lt_of_le_of_lt (by positivity) hx
  nlinarith [abs_nonneg M, le_abs_self M]

end Leindler.Ch05
