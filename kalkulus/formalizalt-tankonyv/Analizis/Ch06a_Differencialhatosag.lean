import Mathlib
import Analizis.Ch05c_ZartIntervallum
import Analizis.Ch05d_FuggvenyHatarertek

/-!
# Leindler László: Analízis — 6. fejezet: Függvények differenciálása

## 6.1–6.2. A differenciálhatóság fogalma, műveleti szabályok
## 6.10. Középértéktételek

Ebben a fájlban a differenciálhányados fogalmát a könyv 6.1.3. Definíciója szerint
adjuk meg (a különbségi hányados határértéke), majd a Rolle-, Lagrange- és
Cauchy-féle középértéktételeket bizonyítjuk a könyv gondolatmenetét követve:
a Rolle-tételt a Weierstrass-tételre (5.14.2) és a belső szélsőérték szükséges
feltételére (6.10.2) építve, a Lagrange- és Cauchy-tételt pedig a könyvben szereplő
segédfüggvényekkel visszavezetve a Rolle-tételre.
-/

namespace Leindler.Ch06

open Set Leindler Leindler.Ch05

/-! ## 6.1. Függvények differenciálhatósága -/

/-- **6.1.1. Definíció.** Az `f` függvény *különbségi hányadosa* az `x₀` pontban:
`(f(x) - f(x₀))/(x - x₀)`. -/
noncomputable def kulonbsegiHanyados (f : ℝ → ℝ) (x₀ x : ℝ) : ℝ := (f x - f x₀) / (x - x₀)

/-- **6.1.3. Definíció (Cauchy).** Az `f` függvény az `x₀` pontban *differenciálható*,
és differenciálhányadosa `c`, ha bármely `ε > 0`-hoz megadható olyan `δ > 0`, hogy
`|x - x₀| < δ`, `x ≠ x₀` esetén `|(f(x) - f(x₀))/(x - x₀) - c| < ε`; azaz ha a
különbségi hányadosnak `x₀`-ban `c` a határértéke. -/
def Derivalt (f : ℝ → ℝ) (x₀ c : ℝ) : Prop :=
  CauchyHatarErtek (kulonbsegiHanyados f x₀) x₀ c

/-- **6.1.2. Definíció (Heine).** A differenciálhatóság sorozatokkal megfogalmazott
alakja ekvivalens a 6.1.3. Definícióval (az 5.15. pont ekvivalenciatétele szerint). -/
theorem derivalt_iff_heine (f : ℝ → ℝ) (x₀ c : ℝ) :
    Derivalt f x₀ c ↔ HeineHatarErtek (kulonbsegiHanyados f x₀) x₀ c :=
  (heineHatarErtek_iff_cauchyHatarErtek _ _ _).symm

/-- A könyv differenciálhányados-fogalma megegyezik a Mathlib `HasDerivAt`
fogalmával. -/
theorem derivalt_iff_hasDerivAt (f : ℝ → ℝ) (x₀ c : ℝ) :
    Derivalt f x₀ c ↔ HasDerivAt f c x₀ := by
  rw [Derivalt, cauchyHatarErtek_iff_tendsto, hasDerivAt_iff_tendsto_slope]
  have : kulonbsegiHanyados f x₀ = slope f x₀ := by
    funext x
    rw [slope_def_field, kulonbsegiHanyados]
  rw [this]

/-- A differenciálhányados egyértelmű. -/
theorem derivalt_unicitas {f : ℝ → ℝ} {x₀ c c' : ℝ} (h : Derivalt f x₀ c)
    (h' : Derivalt f x₀ c') : c = c' :=
  hatarErtek_unicitas h h'

/-- **6.1.8. Tétel (a differenciálhatóság szükséges feltétele).** Ha `f`
differenciálható az `x₀` pontban, akkor ott folytonos is.

*Bizonyítás.* A 6.1.4. Definícióban felírt `f(x) - f(x₀) = f'(x₀)(x - x₀) + ω(x - x₀)`
alak alapján `xₙ → x₀` esetén `f(xₙ) - f(x₀) → 0`, azaz `f(xₙ) → f(x₀)`. -/
theorem differencialhato_folytonos {f : ℝ → ℝ} {x₀ c : ℝ} (h : Derivalt f x₀ c) :
    CauchyFolytonos f x₀ :=
  (cauchyFolytonos_iff_continuousAt f x₀).2 ((derivalt_iff_hasDerivAt f x₀ c).1 h).continuousAt

/-- **6.1.9. Tétel (rendőrelv a differenciálhányadosra).** Ha az `f`, `g`, `h`
függvények az `x₀` pont valamely környezetében értelmezve vannak és ott
`f(x) ≤ g(x) ≤ h(x)`, továbbá `f(x₀) = g(x₀) = h(x₀)` és `f'(x₀) = h'(x₀)`, akkor
`g` differenciálható az `x₀` helyen, és `g'(x₀) = f'(x₀)`.

*Bizonyítás (a könyv gondolatmenete).* A feltételekből `x > x₀` esetén
`(f(x)-f(x₀))/(x-x₀) ≤ (g(x)-g(x₀))/(x-x₀) ≤ (h(x)-h(x₀))/(x-x₀)`, `x < x₀` esetén
pedig fordított irányú egyenlőtlenségek állnak fenn. Mivel a két szélső különbségi
hányados határértéke ugyanaz, a rendőrelv szerint a középsőé is. -/
theorem derivalt_rendorelv {f g h : ℝ → ℝ} {x₀ c : ℝ} {δ₀ : ℝ} (hδ₀ : 0 < δ₀)
    (hfg : ∀ x, |x - x₀| < δ₀ → f x ≤ g x) (hgh : ∀ x, |x - x₀| < δ₀ → g x ≤ h x)
    (hfx : f x₀ = g x₀) (hhx : h x₀ = g x₀)
    (hf : Derivalt f x₀ c) (hh : Derivalt h x₀ c) : Derivalt g x₀ c := by
  intro ε hε
  obtain ⟨δ₁, hδ₁, h₁⟩ := hf ε hε
  obtain ⟨δ₂, hδ₂, h₂⟩ := hh ε hε
  refine ⟨min δ₀ (min δ₁ δ₂), lt_min hδ₀ (lt_min hδ₁ hδ₂), fun x hxne hxd => ?_⟩
  have hd0 : |x - x₀| < δ₀ := lt_of_lt_of_le hxd (min_le_left _ _)
  have hd1 : |x - x₀| < δ₁ := lt_of_lt_of_le hxd (le_trans (min_le_right _ _) (min_le_left _ _))
  have hd2 : |x - x₀| < δ₂ := lt_of_lt_of_le hxd (le_trans (min_le_right _ _) (min_le_right _ _))
  have e₁ := abs_lt.1 (h₁ x hxne hd1)
  have e₂ := abs_lt.1 (h₂ x hxne hd2)
  have hfle : f x ≤ g x := hfg x hd0
  have hgle : g x ≤ h x := hgh x hd0
  rcases lt_or_gt_of_ne (sub_ne_zero.2 hxne) with hneg | hpos
  · -- `x < x₀`: a nevező negatív, az egyenlőtlenségek megfordulnak
    have hlt : x - x₀ < 0 := hneg
    have h1 : kulonbsegiHanyados h x₀ x ≤ kulonbsegiHanyados g x₀ x := by
      rw [kulonbsegiHanyados, kulonbsegiHanyados, hhx]
      exact div_le_div_of_nonpos_of_le hlt.le (by linarith)
    have h2 : kulonbsegiHanyados g x₀ x ≤ kulonbsegiHanyados f x₀ x := by
      rw [kulonbsegiHanyados, kulonbsegiHanyados, hfx]
      exact div_le_div_of_nonpos_of_le hlt.le (by linarith)
    rw [abs_lt]
    constructor <;> linarith [e₁.1, e₁.2, e₂.1, e₂.2]
  · -- `x > x₀`
    have hgt : 0 < x - x₀ := hpos
    have h1 : kulonbsegiHanyados f x₀ x ≤ kulonbsegiHanyados g x₀ x := by
      rw [kulonbsegiHanyados, kulonbsegiHanyados, hfx]
      gcongr
    have h2 : kulonbsegiHanyados g x₀ x ≤ kulonbsegiHanyados h x₀ x := by
      rw [kulonbsegiHanyados, kulonbsegiHanyados, hhx]
      gcongr
    rw [abs_lt]
    constructor <;> linarith [e₁.1, e₁.2, e₂.1, e₂.2]

/-! ## 6.2. Műveleti szabályok -/

/-- **6.2.3. Tétel** = **6.3.1. Tétel.** Ha `f(x) = c`, akkor `f'(x) = 0`, azaz `(c)' = 0`:
konstans differenciálhányadosa mindenütt nulla. -/
theorem derivalt_const (c x₀ : ℝ) : Derivalt (fun _ => c) x₀ 0 :=
  (derivalt_iff_hasDerivAt _ _ _).2 (hasDerivAt_const x₀ c)

/-- **6.3.2. Tétel.** Az `f(x) = x` függvény differenciálhányadosa `1`. -/
theorem derivalt_id (x₀ : ℝ) : Derivalt (fun x => x) x₀ 1 :=
  (derivalt_iff_hasDerivAt _ _ _).2 (hasDerivAt_id x₀)

/-- **6.2.4. Tétel** (összeg). -/
theorem derivalt_add {f g : ℝ → ℝ} {x₀ c d : ℝ} (hf : Derivalt f x₀ c)
    (hg : Derivalt g x₀ d) : Derivalt (fun x => f x + g x) x₀ (c + d) :=
  (derivalt_iff_hasDerivAt _ _ _).2
    (((derivalt_iff_hasDerivAt f x₀ c).1 hf).add ((derivalt_iff_hasDerivAt g x₀ d).1 hg))

/-- **6.2.4. Tétel** (különbség). -/
theorem derivalt_sub {f g : ℝ → ℝ} {x₀ c d : ℝ} (hf : Derivalt f x₀ c)
    (hg : Derivalt g x₀ d) : Derivalt (fun x => f x - g x) x₀ (c - d) :=
  (derivalt_iff_hasDerivAt _ _ _).2
    (((derivalt_iff_hasDerivAt f x₀ c).1 hf).sub ((derivalt_iff_hasDerivAt g x₀ d).1 hg))

/-- **6.2.4. Tétel** (szorzat): `(fg)'(x₀) = f'(x₀)g(x₀) + f(x₀)g'(x₀)`. -/
theorem derivalt_mul {f g : ℝ → ℝ} {x₀ c d : ℝ} (hf : Derivalt f x₀ c)
    (hg : Derivalt g x₀ d) :
    Derivalt (fun x => f x * g x) x₀ (c * g x₀ + f x₀ * d) :=
  (derivalt_iff_hasDerivAt _ _ _).2
    (((derivalt_iff_hasDerivAt f x₀ c).1 hf).mul ((derivalt_iff_hasDerivAt g x₀ d).1 hg))

/-- **6.2.4. Tétel** (hányados): ha `g(x₀) ≠ 0`, akkor
`(f/g)'(x₀) = (f'(x₀)g(x₀) - f(x₀)g'(x₀))/g(x₀)²`. -/
theorem derivalt_div {f g : ℝ → ℝ} {x₀ c d : ℝ} (hf : Derivalt f x₀ c)
    (hg : Derivalt g x₀ d) (hg0 : g x₀ ≠ 0) :
    Derivalt (fun x => f x / g x) x₀ ((c * g x₀ - f x₀ * d) / g x₀ ^ 2) :=
  (derivalt_iff_hasDerivAt _ _ _).2
    (((derivalt_iff_hasDerivAt f x₀ c).1 hf).div ((derivalt_iff_hasDerivAt g x₀ d).1 hg) hg0)

/-- **6.4.1. Tétel (láncszabály).** Ha `g` differenciálható `x₀`-ban és `f`
differenciálható `g(x₀)`-ban, akkor `f ∘ g` differenciálható `x₀`-ban, és
`(f(g(x)))'|_{x₀} = f'(g(x₀))·g'(x₀)`. -/
theorem derivalt_osszetett {f g : ℝ → ℝ} {x₀ c d : ℝ} (hg : Derivalt g x₀ d)
    (hf : Derivalt f (g x₀) c) : Derivalt (fun x => f (g x)) x₀ (c * d) :=
  (derivalt_iff_hasDerivAt _ _ _).2
    (HasDerivAt.comp x₀ ((derivalt_iff_hasDerivAt f (g x₀) c).1 hf)
      ((derivalt_iff_hasDerivAt g x₀ d).1 hg))

/-! ## 6.10. Középértéktételek -/

/-- **6.10.2. Következmény.** Ha egy függvény olyan belső pontban veszi fel (helyi)
szélső értékét, ahol differenciálható, akkor a differenciálhányadosa e pontban zérus.

*Bizonyítás (a könyv gondolatmenete).* Ha `f(c)` maximum, akkor
`(f(x) - f(c))/(x - c) ≥ 0`, ha `x < c`, és `≤ 0`, ha `x > c`; ezért a bal oldali
differenciálhányados `≥ 0`, a jobb oldali `≤ 0`, tehát a (létező) `f'(c)` csak nulla
lehet. Formálisan: ha `f'(c) = L > 0` volna, akkor `ε = L/2`-höz tartozó `δ` mellett
a különbségi hányados pozitív, így `x > c` esetén `f(x) > f(c)` volna; ha `L < 0`,
akkor `x < c` esetén adódna `f(x) > f(c)`. -/
theorem belso_szelsoertek_derivalt_nulla {f : ℝ → ℝ} {c L δ : ℝ} (hδ : 0 < δ)
    (hmax : ∀ x, |x - c| < δ → f x ≤ f c) (hderiv : Derivalt f c L) : L = 0 := by
  by_contra hL
  rcases lt_or_gt_of_ne hL with hneg | hpos
  · -- `L < 0`: bal oldalról jutunk ellentmondásra
    obtain ⟨δ', hδ', hd⟩ := hderiv (-L / 2) (by linarith)
    set x : ℝ := c - min δ δ' / 2 with hx
    have hm : 0 < min δ δ' := lt_min hδ hδ'
    have hxne : x ≠ c := by simp [hx]; linarith
    have hxd : |x - c| < min δ δ' := by
      rw [hx]
      simp only [sub_sub_cancel_left, abs_neg]
      rw [abs_of_pos (by linarith)]
      linarith
    have h1 := abs_lt.1 (hd x hxne (lt_of_lt_of_le hxd (min_le_right _ _)))
    have hquo : kulonbsegiHanyados f c x < 0 := by
      have := h1.2; linarith
    have hxlt : x - c < 0 := by rw [hx]; linarith
    have hfx : f c < f x := by
      rw [kulonbsegiHanyados] at hquo
      have := (div_neg_iff.1 hquo)
      rcases this with ⟨hpos', hneg'⟩ | ⟨hneg', hpos'⟩
      · linarith
      · linarith
    exact absurd (hmax x (lt_of_lt_of_le hxd (min_le_left _ _))) (not_le.2 hfx)
  · -- `L > 0`: jobb oldalról jutunk ellentmondásra
    obtain ⟨δ', hδ', hd⟩ := hderiv (L / 2) (by linarith)
    set x : ℝ := c + min δ δ' / 2 with hx
    have hm : 0 < min δ δ' := lt_min hδ hδ'
    have hxne : x ≠ c := by simp [hx]; linarith
    have hxd : |x - c| < min δ δ' := by
      rw [hx]
      simp only [add_sub_cancel_left]
      rw [abs_of_pos (by linarith)]
      linarith
    have h1 := abs_lt.1 (hd x hxne (lt_of_lt_of_le hxd (min_le_right _ _)))
    have hquo : 0 < kulonbsegiHanyados f c x := by have := h1.1; linarith
    have hxgt : 0 < x - c := by rw [hx]; linarith
    have hfx : f c < f x := by
      rw [kulonbsegiHanyados] at hquo
      have := (div_pos_iff.1 hquo)
      rcases this with ⟨hpos', hpos''⟩ | ⟨hneg', hneg''⟩
      · linarith
      · linarith
    exact absurd (hmax x (lt_of_lt_of_le hxd (min_le_left _ _))) (not_le.2 hfx)

/-- A minimumhelyre vonatkozó megfelelő állítás (a `-f` függvényre alkalmazva). -/
theorem belso_minimum_derivalt_nulla {f : ℝ → ℝ} {c L δ : ℝ} (hδ : 0 < δ)
    (hmin : ∀ x, |x - c| < δ → f c ≤ f x) (hderiv : Derivalt f c L) : L = 0 := by
  have hneg : Derivalt (fun x => -f x) c (-L) := by
    rw [derivalt_iff_hasDerivAt] at hderiv ⊢
    exact hderiv.neg
  have := belso_szelsoertek_derivalt_nulla hδ (fun x hx => by
    simpa using neg_le_neg (hmin x hx)) hneg
  linarith

/-- **6.10.1. Tétel (Rolle-tétel).** Ha `f` folytonos a véges zárt `[a, b]`-n, és
differenciálható a nyitott `(a, b)`-n, továbbá `f(a) = f(b)`, akkor létezik legalább
egy belső pont, ahol a differenciálhányados nulla.

*Bizonyítás (a könyv gondolatmenete).* Véges zárt intervallumon folytonos függvény
felveszi maximumát (`M`) és minimumát (`m`) is. Ha `M = m`, akkor `f` konstans, így
differenciálhányadosa minden belső pontban nulla. Ha `M > m`, akkor valamelyik érték
különbözik az `f(a) = f(b)` értéktől, tehát a függvény azt egy belső `c` pontban veszi
fel; ott a 6.10.2. Következmény szerint `f'(c) = 0`. -/
theorem rolle {f : ℝ → ℝ} {a b : ℝ} (hab : a < b) (hcont : ContinuousOn f (Icc a b))
    (hderiv : ∀ x ∈ Ioo a b, ∃ L, Derivalt f x L) (hfab : f a = f b) :
    ∃ c ∈ Ioo a b, Derivalt f c 0 := by
  have hne : (Icc a b).Nonempty := nonempty_Icc.2 hab.le
  obtain ⟨xs, hxs, hmax⟩ := isCompact_Icc.exists_isMaxOn hne hcont
  obtain ⟨xi, hxi, hmin⟩ := isCompact_Icc.exists_isMinOn hne hcont
  have hmax' : ∀ x ∈ Icc a b, f x ≤ f xs := fun x hx => hmax hx
  have hmin' : ∀ x ∈ Icc a b, f xi ≤ f x := fun x hx => hmin hx
  by_cases hconst : f xs = f xi
  · -- `M = m`: a függvény konstans `[a, b]`-n
    set c : ℝ := (a + b) / 2 with hc
    have hcmem : c ∈ Ioo a b := ⟨by rw [hc]; linarith, by rw [hc]; linarith⟩
    refine ⟨c, hcmem, ?_⟩
    have hfconst : ∀ x ∈ Icc a b, f x = f c := by
      intro x hx
      have h1 := hmax' x hx
      have h2 := hmin' x hx
      have h3 := hmax' c ⟨hcmem.1.le, hcmem.2.le⟩
      have h4 := hmin' c ⟨hcmem.1.le, hcmem.2.le⟩
      rw [hconst] at h1 h3
      linarith
    intro ε hε
    refine ⟨min (c - a) (b - c), lt_min (by linarith [hcmem.1]) (by linarith [hcmem.2]),
      fun x _ hxd => ?_⟩
    have h1 : |x - c| < c - a := lt_of_lt_of_le hxd (min_le_left _ _)
    have h2 : |x - c| < b - c := lt_of_lt_of_le hxd (min_le_right _ _)
    have hx1 := (abs_lt.1 h1).1
    have hx2 := (abs_lt.1 h2).2
    have hxmem : x ∈ Icc a b := ⟨by linarith, by linarith⟩
    rw [kulonbsegiHanyados, hfconst x hxmem]
    simpa using hε
  · -- `M > m`: valamelyik szélső értéket belső pontban veszi fel
    have hkey : ∃ c ∈ Ioo a b, (∀ x ∈ Icc a b, f x ≤ f c) ∨ (∀ x ∈ Icc a b, f c ≤ f x) := by
      by_cases hxsa : f xs = f a
      · -- ekkor a minimum különbözik `f(a)`-tól, tehát belső pontban van
        have hxia : f xi ≠ f a := fun h => hconst (by rw [hxsa, h])
        have hxiIoo : xi ∈ Ioo a b := by
          rcases eq_or_lt_of_le hxi.1 with heq | hlt
          · exact absurd (by rw [← heq]) hxia
          · rcases eq_or_lt_of_le hxi.2 with heq' | hlt'
            · exact absurd (by rw [heq', hfab]) hxia
            · exact ⟨hlt, hlt'⟩
        exact ⟨xi, hxiIoo, Or.inr hmin'⟩
      · have hxsIoo : xs ∈ Ioo a b := by
          rcases eq_or_lt_of_le hxs.1 with heq | hlt
          · exact absurd (by rw [← heq]) hxsa
          · rcases eq_or_lt_of_le hxs.2 with heq' | hlt'
            · exact absurd (by rw [heq', hfab]) hxsa
            · exact ⟨hlt, hlt'⟩
        exact ⟨xs, hxsIoo, Or.inl hmax'⟩
    obtain ⟨c, hcIoo, hc⟩ := hkey
    obtain ⟨L, hL⟩ := hderiv c hcIoo
    set δ : ℝ := min (c - a) (b - c) with hδdef
    have hδ : 0 < δ := lt_min (by linarith [hcIoo.1]) (by linarith [hcIoo.2])
    have hmem : ∀ x, |x - c| < δ → x ∈ Icc a b := by
      intro x hx
      have h1 : |x - c| < c - a := lt_of_lt_of_le hx (min_le_left _ _)
      have h2 : |x - c| < b - c := lt_of_lt_of_le hx (min_le_right _ _)
      exact ⟨by linarith [(abs_lt.1 h1).1], by linarith [(abs_lt.1 h2).2]⟩
    have hL0 : L = 0 := by
      rcases hc with hc | hc
      · exact belso_szelsoertek_derivalt_nulla hδ (fun x hx => hc x (hmem x hx)) hL
      · exact belso_minimum_derivalt_nulla hδ (fun x hx => hc x (hmem x hx)) hL
    exact ⟨c, hcIoo, hL0 ▸ hL⟩

/-- **6.10.3. Tétel (Lagrange-tétel).** Ha `f` folytonos a véges zárt `[a, b]`-n és
differenciálható a nyitott `(a, b)`-n, akkor van olyan `c` belső pont, ahol
`f'(c) = (f(b) - f(a))/(b - a)`.

*Bizonyítás (a könyv gondolatmenete).* Az `F(x) = f(x) + λx` alakú segédfüggvényben
válasszuk `λ = -(f(b) - f(a))/(b - a)`-t; ekkor `F(a) = F(b)`, tehát a Rolle-tétel
szerint van olyan `c` belső pont, ahol `F'(c) = 0`, azaz
`f'(c) - (f(b) - f(a))/(b - a) = 0`. -/
theorem lagrange {f : ℝ → ℝ} {a b : ℝ} (hab : a < b) (hcont : ContinuousOn f (Icc a b))
    (hderiv : ∀ x ∈ Ioo a b, ∃ L, Derivalt f x L) :
    ∃ c ∈ Ioo a b, Derivalt f c ((f b - f a) / (b - a)) := by
  set lam : ℝ := (f b - f a) / (b - a) with hlam
  set F : ℝ → ℝ := fun x => f x - lam * x with hF
  have hFcont : ContinuousOn F (Icc a b) :=
    hcont.sub ((continuousOn_const).mul continuousOn_id)
  have hFderiv : ∀ x ∈ Ioo a b, ∃ L, Derivalt F x L := by
    intro x hx
    obtain ⟨L, hL⟩ := hderiv x hx
    refine ⟨L - lam, ?_⟩
    rw [derivalt_iff_hasDerivAt] at hL ⊢
    simpa using hL.sub ((hasDerivAt_id x).const_mul lam)
  have hFab : F a = F b := by
    have hba : b - a ≠ 0 := sub_ne_zero.2 (ne_of_gt hab)
    simp only [hF, hlam]
    field_simp
    ring
  obtain ⟨c, hc, hFc⟩ := rolle hab hFcont hFderiv hFab
  refine ⟨c, hc, ?_⟩
  rw [derivalt_iff_hasDerivAt] at hFc ⊢
  have hlin : HasDerivAt (fun x : ℝ => lam * x) lam c := by
    simpa using (hasDerivAt_id c).const_mul lam
  have : HasDerivAt (fun x => F x + lam * x) (0 + lam) c := hFc.add hlin
  simpa [hF] using this

/-- **6.10.4. Következmény.** Ha `f` folytonos `[a, b]`-n, differenciálható `(a, b)`-n,
és deriváltja mindenütt nulla, akkor `f` konstans `[a, b]`-n.

*Bizonyítás.* A Lagrange-tétel feltételei bármely `[a, x]` intervallumon teljesülnek,
így van olyan `ξ ∈ (a, x)`, amelyre `(f(x) - f(a))/(x - a) = f'(ξ) = 0`. -/
theorem derivalt_nulla_konstans {f : ℝ → ℝ} {a b : ℝ}
    (hcont : ContinuousOn f (Icc a b)) (hderiv : ∀ x ∈ Ioo a b, Derivalt f x 0) :
    ∀ x ∈ Icc a b, f x = f a := by
  intro x hx
  rcases eq_or_lt_of_le hx.1 with heq | hlt
  · rw [← heq]
  · have hsub : Icc a x ⊆ Icc a b := Icc_subset_Icc le_rfl hx.2
    obtain ⟨c, hc, hLc⟩ := lagrange hlt (hcont.mono hsub) (fun y hy => by
      obtain hd := hderiv y ⟨hy.1, lt_of_lt_of_le hy.2 hx.2⟩
      exact ⟨0, hd⟩)
    have hcIoo : c ∈ Ioo a b := ⟨hc.1, lt_of_lt_of_le hc.2 hx.2⟩
    have := derivalt_unicitas hLc (hderiv c hcIoo)
    have hxa : x - a ≠ 0 := sub_ne_zero.2 (ne_of_gt hlt)
    field_simp at this
    linarith

/-- **6.10.6. Tétel (Cauchy-féle középértéktétel).** Ha `f` és `g` folytonos `[a, b]`-n,
differenciálható `(a, b)`-n, továbbá `g'` a belső pontokban nem nulla, akkor létezik
olyan `c` belső pont, ahol `f'(c)/g'(c) = (f(b) - f(a))/(g(b) - g(a))`.

*Bizonyítás (a könyv gondolatmenete).* A bizonyítás szinte szó szerint követi a
Lagrange-tételét, csak `λx` helyett `λg(x)`-et írunk: legyen
`F(x) = f(x) - ((f(b) - f(a))/(g(b) - g(a)))·g(x)`. Itt `g(b) - g(a) ≠ 0`, hiszen a
Lagrange-tétel szerint `g(b) - g(a) = g'(ξ)(b - a)` valamely `ξ ∈ (a, b)`-re, és
`g'(ξ) ≠ 0`. Az `F` függvényre teljesülnek a Rolle-tétel feltételei, így van olyan `c`
belső pont, ahol `F'(c) = 0`, ami éppen az állítás. -/
theorem cauchy_kozepertek {f g : ℝ → ℝ} {f' g' : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hfc : ContinuousOn f (Icc a b)) (hgc : ContinuousOn g (Icc a b))
    (hfd : ∀ x ∈ Ioo a b, Derivalt f x (f' x)) (hgd : ∀ x ∈ Ioo a b, Derivalt g x (g' x))
    (hg0 : ∀ x ∈ Ioo a b, g' x ≠ 0) :
    g b - g a ≠ 0 ∧ ∃ c ∈ Ioo a b, f' c * (g b - g a) = (f b - f a) * g' c := by
  -- először: `g(b) - g(a) ≠ 0`
  have hgab : g b - g a ≠ 0 := by
    intro hzero
    obtain ⟨ξ, hξ, hLξ⟩ := lagrange hab hgc (fun x hx => ⟨g' x, hgd x hx⟩)
    have : g' ξ = (g b - g a) / (b - a) := derivalt_unicitas (hgd ξ hξ) hLξ
    rw [hzero] at this
    simp at this
    exact hg0 ξ hξ this
  refine ⟨hgab, ?_⟩
  set lam : ℝ := (f b - f a) / (g b - g a) with hlam
  set F : ℝ → ℝ := fun x => f x - lam * g x with hF
  have hFcont : ContinuousOn F (Icc a b) := hfc.sub (continuousOn_const.mul hgc)
  have hFderiv : ∀ x ∈ Ioo a b, ∃ L, Derivalt F x L := by
    intro x hx
    refine ⟨f' x - lam * g' x, ?_⟩
    have h1 := (derivalt_iff_hasDerivAt f x (f' x)).1 (hfd x hx)
    have h2 := (derivalt_iff_hasDerivAt g x (g' x)).1 (hgd x hx)
    rw [derivalt_iff_hasDerivAt]
    exact h1.sub (h2.const_mul lam)
  have hFab : F a = F b := by
    simp only [hF, hlam]
    field_simp
    ring
  obtain ⟨c, hc, hFc⟩ := rolle hab hFcont hFderiv hFab
  refine ⟨c, hc, ?_⟩
  have h1 := (derivalt_iff_hasDerivAt f c (f' c)).1 (hfd c hc)
  have h2 := (derivalt_iff_hasDerivAt g c (g' c)).1 (hgd c hc)
  have hFc' := (derivalt_iff_hasDerivAt F c 0).1 hFc
  have huniq : (0 : ℝ) = f' c - lam * g' c := by
    have : HasDerivAt F (f' c - lam * g' c) c := h1.sub (h2.const_mul lam)
    exact hFc'.unique this
  have : f' c = lam * g' c := by linarith
  rw [this, hlam]
  field_simp

end Leindler.Ch06
