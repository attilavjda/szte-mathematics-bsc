import Analizis.Ch06b_ElemiDerivaltak

/-!
# Leindler László: Analízis — 6.1.4–6.2.2, 6.6.4 és 6.10.5

Ez a modul a 6. fejezet hátralévő alapfogalmait tartalmazza (84–87., 93., 99. oldal):

* **6.1.4. Definíció** ‑ a differenciál (`df = f'(x₀)(x - x₀)`) és a
  `f(x) - f(x₀) = df + ω·(x - x₀)` felbontás,
* **6.1.5. Definíció** ‑ jobb és bal oldali differenciálhányados,
* **6.1.6. Tétel** ‑ `f'(x₀)` akkor és csak akkor létezik, ha a két féloldali
  differenciálhányados létezik és egyenlő,
* **6.1.7. Definíció** ‑ zárt intervallumon differenciálható függvény,
* **6.2.1. Definíció** ‑ a differenciálhányados-függvény (deriváltfüggvény),
* **6.2.2. Definíció** ‑ folytonosan differenciálható függvény,
* **6.6.4. Tétel** ‑ `(arcctg x)' = -1/(1 + x²)`,
* **6.10.5. Következmény** ‑ ha `f' = g'`, akkor `f = g + C`.
-/

namespace Leindler.Ch06

open Set Leindler Leindler.Ch05

/-! ## 6.1.4. A differenciál -/

/-- **6.1.4. Definíció.** Ha `f` az `x₀` pontban differenciálható és
`f'(x₀) = c`, akkor a `df = c·(x - x₀)` lineáris kifejezést az `f` függvény
`x₀`-beli *differenciáljának* nevezzük. -/
def differencial (c x₀ x : ℝ) : ℝ := c * (x - x₀)

/-- **6.1.4. (a felbontás).** `f` akkor és csak akkor differenciálható `x₀`-ban `c`
differenciálhányadossal, ha
`f(x) - f(x₀) = df + ω(x)·(x - x₀)`, ahol `ω(x) → 0`, ha `x → x₀`.

*Bizonyítás.* Az `x ≠ x₀` pontokban `ω(x) := (f(x) - f(x₀))/(x - x₀) - c` választással a
felbontás azonosság, `x = x₀`-ban pedig mindkét oldal nulla; `ω(x) → 0` éppen azt
jelenti, hogy a különbségi hányados határértéke `c`. -/
theorem derivalt_iff_differencial (f : ℝ → ℝ) (x₀ c : ℝ) :
    Derivalt f x₀ c ↔
      ∃ ω : ℝ → ℝ, (∀ x, f x - f x₀ = differencial c x₀ x + ω x * (x - x₀)) ∧
        CauchyHatarErtek ω x₀ 0 := by
  constructor
  · intro h
    refine ⟨fun x => if x = x₀ then 0 else kulonbsegiHanyados f x₀ x - c, ?_, ?_⟩
    · intro x
      by_cases hx : x = x₀
      · simp [hx, differencial]
      · have hne : x - x₀ ≠ 0 := sub_ne_zero.2 hx
        simp only [hx, if_false, differencial, kulonbsegiHanyados]
        field_simp
        ring
    · intro ε hε
      obtain ⟨δ, hδ, hδp⟩ := h ε hε
      refine ⟨δ, hδ, fun x hxne hxd => ?_⟩
      simpa [hxne] using hδp x hxne hxd
  · rintro ⟨ω, hω, hlim⟩ ε hε
    obtain ⟨δ, hδ, hδp⟩ := hlim ε hε
    refine ⟨δ, hδ, fun x hxne hxd => ?_⟩
    have hne : x - x₀ ≠ 0 := sub_ne_zero.2 hxne
    have hrw : kulonbsegiHanyados f x₀ x - c = ω x := by
      rw [kulonbsegiHanyados, hω x, differencial]
      field_simp
      ring
    rw [hrw]
    simpa using hδp x hxne hxd

/-! ## 6.1.5–6.1.6. Féloldali differenciálhányadosok -/

/-- **6.1.5. Definíció.** Az `f` függvény *jobb oldali differenciálhányadosa* az `x₀`
pontban `c`, ha a különbségi hányadosnak `x₀`-ban a jobb oldali határértéke `c`. -/
def JobbDerivalt (f : ℝ → ℝ) (x₀ c : ℝ) : Prop :=
  JobbHatarErtek (kulonbsegiHanyados f x₀) x₀ c

/-- **6.1.5. Definíció.** Az `f` függvény *bal oldali differenciálhányadosa* az `x₀`
pontban `c`. -/
def BalDerivalt (f : ℝ → ℝ) (x₀ c : ℝ) : Prop :=
  BalHatarErtek (kulonbsegiHanyados f x₀) x₀ c

/-- **6.1.6. Tétel.** `f'(x₀)` akkor és csak akkor létezik, ha `f'₊(x₀)` és `f'₋(x₀)`
léteznek és egyenlők; ekkor `f'(x₀) = f'₊(x₀) = f'₋(x₀)`.

*Bizonyítás.* Ez az 5.15.6. Tétel (a határérték és a féloldali határértékek kapcsolata)
alkalmazása a különbségi hányados függvényre. -/
theorem derivalt_iff_feloldali (f : ℝ → ℝ) (x₀ c : ℝ) :
    Derivalt f x₀ c ↔ JobbDerivalt f x₀ c ∧ BalDerivalt f x₀ c :=
  cauchyHatarErtek_iff_feloldali _ _ _

/-- Példa: az `|x|` függvénynek a `0` helyen a jobb oldali differenciálhányadosa `1`. -/
theorem jobbDerivalt_abs : JobbDerivalt (fun x => |x|) 0 1 := by
  intro ε hε
  refine ⟨1, one_pos, fun x hx _ => ?_⟩
  have hrw : kulonbsegiHanyados (fun x => |x|) 0 x = 1 := by
    rw [kulonbsegiHanyados]
    simp [abs_of_pos hx, ne_of_gt hx]
  simpa [hrw] using hε

/-- Példa: az `|x|` függvénynek a `0` helyen a bal oldali differenciálhányadosa `-1`,
tehát `|x|` a `0` helyen nem differenciálható. -/
theorem balDerivalt_abs : BalDerivalt (fun x => |x|) 0 (-1) := by
  intro ε hε
  refine ⟨1, one_pos, fun x hx _ => ?_⟩
  have hx0 : x ≠ 0 := ne_of_lt hx
  have hrw : kulonbsegiHanyados (fun x => |x|) 0 x = -1 := by
    rw [kulonbsegiHanyados]
    simp only [abs_of_neg hx, abs_zero, sub_zero]
    field_simp
  simpa [hrw] using hε

theorem abs_nem_differencialhato_nullaban : ¬ ∃ c, Derivalt (fun x => |x|) 0 c := by
  rintro ⟨c, hc⟩
  obtain ⟨hj, hb⟩ := (derivalt_iff_feloldali _ _ _).1 hc
  -- a jobb oldali határérték `1`, a bal oldali `-1`, s a féloldali határérték egyértelmű
  have h1 : c = 1 := by
    by_contra hne
    obtain ⟨δ₁, hδ₁, h₁⟩ := hj (|c - 1| / 2) (by
      have : 0 < |c - 1| := abs_pos.2 (sub_ne_zero.2 hne)
      linarith)
    obtain ⟨δ₂, hδ₂, h₂⟩ := jobbDerivalt_abs (|c - 1| / 2) (by
      have : 0 < |c - 1| := abs_pos.2 (sub_ne_zero.2 hne)
      linarith)
    set x := min δ₁ δ₂ / 2 with hx
    have hxpos : 0 < x := by
      have := lt_min hδ₁ hδ₂
      simp only [hx]
      linarith
    have hxd : |x - 0| < min δ₁ δ₂ := by
      rw [sub_zero, abs_of_pos hxpos, hx]
      have := lt_min hδ₁ hδ₂
      linarith
    have hA := h₁ x hxpos (lt_of_lt_of_le hxd (min_le_left _ _))
    have hB := h₂ x hxpos (lt_of_lt_of_le hxd (min_le_right _ _))
    have := abs_sub_abs_le_abs_sub (kulonbsegiHanyados (fun x => |x|) 0 x - c)
      (kulonbsegiHanyados (fun x => |x|) 0 x - 1)
    have hcc : |c - 1| ≤ |kulonbsegiHanyados (fun x => |x|) 0 x - c| +
        |kulonbsegiHanyados (fun x => |x|) 0 x - 1| := by
      have hid : c - 1 = (kulonbsegiHanyados (fun x => |x|) 0 x - 1)
          - (kulonbsegiHanyados (fun x => |x|) 0 x - c) := by ring
      rw [hid]
      exact le_trans (abs_sub _ _) (by rw [add_comm])
    linarith
  have h2 : c = -1 := by
    by_contra hne
    obtain ⟨δ₁, hδ₁, h₁⟩ := hb (|c + 1| / 2) (by
      have : 0 < |c + 1| := abs_pos.2 (by
        intro hz
        exact hne (by linarith [eq_neg_of_add_eq_zero_left hz]))
      linarith)
    obtain ⟨δ₂, hδ₂, h₂⟩ := balDerivalt_abs (|c + 1| / 2) (by
      have : 0 < |c + 1| := abs_pos.2 (by
        intro hz
        exact hne (by linarith [eq_neg_of_add_eq_zero_left hz]))
      linarith)
    set x := -(min δ₁ δ₂ / 2) with hx
    have hxneg : x < 0 := by
      have := lt_min hδ₁ hδ₂
      simp only [hx]
      linarith
    have hxd : |x - 0| < min δ₁ δ₂ := by
      rw [sub_zero, abs_of_neg hxneg, hx]
      have := lt_min hδ₁ hδ₂
      linarith
    have hA := h₁ x hxneg (lt_of_lt_of_le hxd (min_le_left _ _))
    have hB := h₂ x hxneg (lt_of_lt_of_le hxd (min_le_right _ _))
    have hcc : |c + 1| ≤ |kulonbsegiHanyados (fun x => |x|) 0 x - c| +
        |kulonbsegiHanyados (fun x => |x|) 0 x - (-1)| := by
      have hid : c + 1 = (kulonbsegiHanyados (fun x => |x|) 0 x - (-1))
          - (kulonbsegiHanyados (fun x => |x|) 0 x - c) := by ring
      rw [hid]
      exact le_trans (abs_sub _ _) (by rw [add_comm])
    linarith
  rw [h1] at h2
  norm_num at h2

/-! ## 6.1.7. Zárt intervallumon differenciálható függvény -/

/-- **6.1.7. Definíció.** Az `f` függvényt akkor nevezzük az `[a, b]` zárt intervallumon
differenciálhatónak, ha minden belső pontban differenciálható, továbbá az `a` pontban a
jobb oldali, a `b` pontban a bal oldali differenciálhányadosa létezik. -/
def ZartIntervallumonDifferencialhato (f : ℝ → ℝ) (a b : ℝ) : Prop :=
  (∀ x ∈ Ioo a b, ∃ c, Derivalt f x c) ∧ (∃ c, JobbDerivalt f a c) ∧ (∃ c, BalDerivalt f b c)

/-! ## 6.2.1–6.2.2. A differenciálhányados-függvény -/

/-- Az `f` függvény az `x` pontban *differenciálható*, ha van differenciálhányadosa. -/
def Differencialhato (f : ℝ → ℝ) (x : ℝ) : Prop := ∃ c, Derivalt f x c

/-- **6.2.1. Definíció.** Az `f` függvény *differenciálhányados-függvénye* (deriváltja):
az a függvény, amely minden olyan `x` pontban, ahol `f` differenciálható, az `f`
`x`-beli differenciálhányadosát veszi fel értékül. -/
noncomputable def derivaltFuggveny (f : ℝ → ℝ) : ℝ → ℝ := deriv f

@[inherit_doc derivaltFuggveny]
notation:max f "′" => derivaltFuggveny f

/-- A deriváltfüggvény értéke a differenciálhányados. -/
theorem derivaltFuggveny_eq {f : ℝ → ℝ} {x c : ℝ} (h : Derivalt f x c) :
    derivaltFuggveny f x = c :=
  ((derivalt_iff_hasDerivAt f x c).1 h).deriv

/-- **6.2.2. Definíció.** Egy függvényt egy `I` halmazon (intervallumon) *folytonosan
differenciálhatónak* nevezünk, ha ott mindenütt differenciálható, és a
differenciálhányados-függvénye folytonos ezen az intervallumon. -/
def FolytonosanDifferencialhato (f : ℝ → ℝ) (I : Set ℝ) : Prop :=
  (∀ x ∈ I, Differencialhato f x) ∧ ContinuousOn (derivaltFuggveny f) I

/-- Példa: `x ↦ x²` az egész számegyenesen folytonosan differenciálható, deriváltja
`2x`. -/
theorem folytonosanDifferencialhato_negyzet :
    FolytonosanDifferencialhato (fun x : ℝ => x ^ 2) univ := by
  have hd : ∀ x : ℝ, Derivalt (fun x : ℝ => x ^ 2) x (2 * x) := by
    intro x
    rw [derivalt_iff_hasDerivAt]
    simpa using (hasDerivAt_pow 2 x)
  refine ⟨fun x _ => ⟨2 * x, hd x⟩, ?_⟩
  have heq : derivaltFuggveny (fun x : ℝ => x ^ 2) = fun x : ℝ => 2 * x := by
    funext x
    exact derivaltFuggveny_eq (hd x)
  rw [heq]
  exact (continuous_const.mul continuous_id).continuousOn

/-! ## 6.6.4. Tétel -/

/-- **6.6.4. Tétel.** `(arcctg x)' = -1/(1 + x²)`.

A könyv `arcctg x = π/2 - arctg x` alakban vezeti be az arkusz kotangens függvényt. -/
theorem derivalt_arcctg (x₀ : ℝ) :
    Derivalt (fun x => Real.pi / 2 - Real.arctan x) x₀ (-(1 / (1 + x₀ ^ 2))) := by
  rw [derivalt_iff_hasDerivAt]
  have h := Real.hasDerivAt_arctan x₀
  have := (hasDerivAt_const x₀ (Real.pi / 2)).sub h
  simpa using this

/-! ## 6.10.5. Következmény -/

/-- **6.10.5. Következmény.** Ha `f` és `g` folytonosak `[a, b]`-n, differenciálhatók
`(a, b)`-n, és `f'(x) = g'(x)` minden `x ∈ (a, b)`-re, akkor `f(x) = g(x) + C`.

*Bizonyítás.* Az `f - g` függvényre alkalmazva a 6.10.4. Következményt (a deriváltja
azonosan nulla, tehát konstans). -/
theorem azonos_derivalt_konstans_kulonbseg {f g f' g' : ℝ → ℝ} {a b : ℝ}
    (hfc : ContinuousOn f (Icc a b)) (hgc : ContinuousOn g (Icc a b))
    (hfd : ∀ x ∈ Ioo a b, Derivalt f x (f' x)) (hgd : ∀ x ∈ Ioo a b, Derivalt g x (g' x))
    (heq : ∀ x ∈ Ioo a b, f' x = g' x) :
    ∃ C : ℝ, ∀ x ∈ Icc a b, f x = g x + C := by
  refine ⟨f a - g a, ?_⟩
  have hd : ∀ x ∈ Ioo a b, Derivalt (fun y => f y - g y) x 0 := by
    intro x hx
    have h1 := (derivalt_iff_hasDerivAt f x (f' x)).1 (hfd x hx)
    have h2 := (derivalt_iff_hasDerivAt g x (g' x)).1 (hgd x hx)
    rw [derivalt_iff_hasDerivAt]
    have := h1.sub h2
    rwa [heq x hx, sub_self] at this
  have hcont : ContinuousOn (fun y => f y - g y) (Icc a b) := hfc.sub hgc
  intro x hx
  have := derivalt_nulla_konstans hcont hd x hx
  simp only at this
  linarith

end Leindler.Ch06
