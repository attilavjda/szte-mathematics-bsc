import Mathlib
import Analizis.Ch05a_FuggvenyekAlapfogalmak
import Analizis.Ch08a_MonotonitasSzelsoertek

/-!
# Leindler László: Analízis — 8. fejezet: Függvénydiszkusszió

## 8.6–8.8. Konvexség, konkávság, inflexiós pontok, a függvénydiszkusszió sémája

Ez a fájl a következő tételeket tartalmazza:

* 8.6.1. Tétel — a konvexség (konkávság) szükséges és elegendő feltétele a második
  differenciálhányados előjelével,
* 8.7.1. Tétel — inflexiós pontban `f''(x₀) = 0` (szükséges feltétel),
* 8.7.2. Tétel — ha `f''(x₀) = 0` és `f'''(x₀) ≠ 0`, akkor `x₀` inflexiós pont
  (elegendő feltétel),
* 8.8. A függvénydiszkusszió általános sémája (dokumentáció).
-/

namespace Leindler.Ch08

open Set Leindler Leindler.Ch05 Leindler.Ch06

/-! ## Segédeszközök: a húr alatt levés nem szigorú alakjai

Az 5.1.8. Tétel bizonyításában szereplő átalakítások nem szigorú (`≤`) változatai.
-/

/-- A görbe a húr alatt (vagy a húron) van az `x` pontban akkor és csak akkor, ha a bal
oldali szelőmeredekség legfeljebb akkora, mint a teljes húr meredeksége. -/
theorem le_hur_iff_slope {f : ℝ → ℝ} {c d x : ℝ} (hcx : c < x) (hxd : x < d) :
    f x ≤ hur f c d x ↔ (f x - f c) / (x - c) ≤ (f d - f c) / (d - c) := by
  have hxc : (0 : ℝ) < x - c := sub_pos.2 hcx
  have hdc : (0 : ℝ) < d - c := sub_pos.2 (hcx.trans hxd)
  rw [← sub_nonneg, hur_sub (hcx.trans hxd), le_div_iff₀ hdc, zero_mul,
    div_le_div_iff₀ hxc hdc]
  constructor <;> intro h <;> linarith

/-- A görbe a húr alatt (vagy a húron) van az `x` pontban akkor és csak akkor, ha a teljes
húr meredeksége legfeljebb akkora, mint a jobb oldali szelőmeredekség. -/
theorem le_hur_iff_slope_right {f : ℝ → ℝ} {c d x : ℝ} (hcx : c < x) (hxd : x < d) :
    f x ≤ hur f c d x ↔ (f d - f c) / (d - c) ≤ (f d - f x) / (d - x) := by
  have hdx : (0 : ℝ) < d - x := sub_pos.2 hxd
  have hdc : (0 : ℝ) < d - c := sub_pos.2 (hcx.trans hxd)
  rw [← sub_nonneg, hur_sub' (hcx.trans hxd), le_div_iff₀ hdc, zero_mul,
    div_le_div_iff₀ hdc hdx]
  constructor <;> intro h <;> linarith

/-- Az 5.1.8. Tétel (1) egyenlőtlenségének nem szigorú alakja: a görbe akkor és csak akkor
van a húr alatt az `x` pontban, ha a bal oldali szelőmeredekség legfeljebb akkora, mint a
jobb oldali. -/
theorem le_hur_iff_slopes {f : ℝ → ℝ} {c d x : ℝ} (hcx : c < x) (hxd : x < d) :
    f x ≤ hur f c d x ↔ (f x - f c) / (x - c) ≤ (f d - f x) / (d - x) := by
  have hp : (0 : ℝ) < x - c := sub_pos.2 hcx
  have hq : (0 : ℝ) < d - x := sub_pos.2 hxd
  have hdc : (0 : ℝ) < d - c := by linarith
  rw [← sub_nonneg, hur_sub (hcx.trans hxd), le_div_iff₀ hdc, zero_mul,
    div_le_div_iff₀ hp hq]
  constructor <;> intro h <;> nlinarith

/-- A konvexitás öröklődik részhalmazra. -/
theorem konvexGorbe_mono {f : ℝ → ℝ} {I J : Set ℝ} (h : KonvexGorbe f I) (hJI : J ⊆ I) :
    KonvexGorbe f J := fun c hc d hd hcd x hx => h c (hJI hc) d (hJI hd) hcd x hx

/-- A konkávság öröklődik részhalmazra. -/
theorem konkavGorbe_mono {f : ℝ → ℝ} {I J : Set ℝ} (h : KonkavGorbe f I) (hJI : J ⊆ I) :
    KonkavGorbe f J := fun c hc d hd hcd x hx => h c (hJI hc) d (hJI hd) hcd x hx

/-- A `-f` függvény húrja a `f` húrjának ellentettje. -/
theorem hur_neg (f : ℝ → ℝ) (c d x : ℝ) : hur (fun y => -f y) c d x = -hur f c d x := by
  simp only [hur]
  ring

/-- Az `f` görbe akkor és csak akkor konkáv, ha a `-f` görbe konvex. -/
theorem konkav_iff_konvex_neg (f : ℝ → ℝ) (I : Set ℝ) :
    KonkavGorbe f I ↔ KonvexGorbe (fun y => -f y) I := by
  constructor
  · intro h c hc d hdI hcd x hx
    have h' := h c hc d hdI hcd x hx
    show -f x ≤ hur (fun y => -f y) c d x
    rw [hur_neg]
    linarith
  · intro h c hc d hdI hcd x hx
    have h' : -f x ≤ hur (fun y => -f y) c d x := h c hc d hdI hcd x hx
    rw [hur_neg] at h'
    linarith

/-- Ha `g` differenciálható az `(a, b)` intervallum minden pontjában, akkor folytonos minden
`[u, v] ⊆ (a, b)` zárt részintervallumon. -/
theorem folytonos_Icc_of_derivalt {g g' : ℝ → ℝ} {a b u v : ℝ}
    (hd : ∀ x ∈ Ioo a b, Derivalt g x (g' x)) (hsub : Icc u v ⊆ Ioo a b) :
    ContinuousOn g (Icc u v) := fun y hy =>
  ((cauchyFolytonos_iff_continuousAt g y).1
    (differencialhato_folytonos (hd y (hsub hy)))).continuousWithinAt

/-! ## 8.6. Konvexség és konkávság eldöntése differenciálhányadosokkal -/

/-- Ha `f'' ≥ 0` az `(a, b)`-n, akkor `f'` növekedő `(a, b)`-n (a 8.1.2. Tétel
alkalmazása az `f'` függvényre). -/
theorem derivalt_novekedo_ha_masodik_derivalt_nemnegativ {f' f'' : ℝ → ℝ} {a b : ℝ}
    (hd2 : ∀ x ∈ Ioo a b, Derivalt f' x (f'' x)) (hnn : ∀ x ∈ Ioo a b, 0 ≤ f'' x) :
    ∀ u ∈ Ioo a b, ∀ v ∈ Ioo a b, u < v → f' u ≤ f' v := by
  intro u hu v hv huv
  have hsub : Icc u v ⊆ Ioo a b := fun y hy =>
    ⟨lt_of_lt_of_le hu.1 hy.1, lt_of_le_of_lt hy.2 hv.2⟩
  have hcont : ContinuousOn f' (Icc u v) := folytonos_Icc_of_derivalt hd2 hsub
  exact novekedo_ha_derivalt_nemnegativ hcont
    (fun x hx => hd2 x (hsub (Ioo_subset_Icc_self hx)))
    (fun x hx => hnn x (hsub (Ioo_subset_Icc_self hx)))
    u (left_mem_Icc.2 huv.le) v (right_mem_Icc.2 huv.le) huv

/-- **8.6.1. Tétel (elegendőség).** Ha az `f` függvény az `(a, b)` intervallumon kétszer
differenciálható, és `f''(x) ≥ 0` az `(a, b)`-n, akkor `f` konvex az `(a, b)`-n.

*Bizonyítás.* Mivel `f'' ≥ 0`, az `f'` függvény növekedő `(a, b)`-n. Legyen
`c < x < d` az `(a, b)`-ben. A Lagrange-tétel szerint van olyan `ξ₁ ∈ (c, x)` és
`ξ₂ ∈ (x, d)`, hogy `f'(ξ₁) = (f(x) - f(c))/(x - c)` és `f'(ξ₂) = (f(d) - f(x))/(d - x)`.
Mivel `ξ₁ < ξ₂`, `f'(ξ₁) ≤ f'(ξ₂)`, ami éppen az 5.1.8. Tételbeli (1) egyenlőtlenség nem
szigorú alakja, tehát a görbe a húr alatt (vagy a húron) van. -/
theorem konvex_ha_masodik_derivalt_nemnegativ {f f' f'' : ℝ → ℝ} {a b : ℝ}
    (hd : ∀ x ∈ Ioo a b, Derivalt f x (f' x))
    (hd2 : ∀ x ∈ Ioo a b, Derivalt f' x (f'' x))
    (hnn : ∀ x ∈ Ioo a b, 0 ≤ f'' x) :
    KonvexGorbe f (Ioo a b) := by
  intro c hc d hdI hcd x hx
  have hsub : Icc c d ⊆ Ioo a b := fun y hy =>
    ⟨lt_of_lt_of_le hc.1 hy.1, lt_of_le_of_lt hy.2 hdI.2⟩
  have hcont : ContinuousOn f (Icc c d) := folytonos_Icc_of_derivalt hd hsub
  have hcx := hx.1
  have hxd := hx.2
  have hsub1 : Icc c x ⊆ Icc c d := Icc_subset_Icc le_rfl hxd.le
  have hsub2 : Icc x d ⊆ Icc c d := Icc_subset_Icc hcx.le le_rfl
  obtain ⟨ξ₁, hξ₁, hL1⟩ := lagrange hcx (hcont.mono hsub1)
    (fun y hy => ⟨f' y, hd y (hsub (hsub1 (Ioo_subset_Icc_self hy)))⟩)
  obtain ⟨ξ₂, hξ₂, hL2⟩ := lagrange hxd (hcont.mono hsub2)
    (fun y hy => ⟨f' y, hd y (hsub (hsub2 (Ioo_subset_Icc_self hy)))⟩)
  have hm₁ : ξ₁ ∈ Ioo a b := hsub (hsub1 (Ioo_subset_Icc_self hξ₁))
  have hm₂ : ξ₂ ∈ Ioo a b := hsub (hsub2 (Ioo_subset_Icc_self hξ₂))
  have e1 : f' ξ₁ = (f x - f c) / (x - c) := derivalt_unicitas (hd ξ₁ hm₁) hL1
  have e2 : f' ξ₂ = (f d - f x) / (d - x) := derivalt_unicitas (hd ξ₂ hm₂) hL2
  have hmono := derivalt_novekedo_ha_masodik_derivalt_nemnegativ hd2 hnn
    ξ₁ hm₁ ξ₂ hm₂ (lt_trans hξ₁.2 hξ₂.1)
  rw [le_hur_iff_slopes hcx hxd, ← e1, ← e2]
  exact hmono

/-- **8.6.1. Tétel (szükségesség, első lépés).** Ha `f` konvex az `(a, b)`-n és ott
differenciálható, akkor `f'` növekedő `(a, b)`-n.

*Bizonyítás (a könyv gondolatmenete).* Rögzítsük `c < d`-t, és legyen
`m = (f(d) - f(c))/(d - c)`. Az 5.1.8. Tétel szerint minden `x ∈ (c, d)` pontra
`(f(x) - f(c))/(x - c) ≤ m ≤ (f(d) - f(x))/(d - x)`. Az `x → c`, illetve `x → d`
határátmenettel `f'(c) ≤ m` és `m ≤ f'(d)` adódik. -/
theorem konvex_derivalt_novekedo {f f' : ℝ → ℝ} {a b : ℝ}
    (hconv : KonvexGorbe f (Ioo a b)) (hd : ∀ x ∈ Ioo a b, Derivalt f x (f' x)) :
    ∀ c ∈ Ioo a b, ∀ d ∈ Ioo a b, c < d → f' c ≤ f' d := by
  intro c hc d hdI hcd
  set m : ℝ := (f d - f c) / (d - c) with hm
  have hleft : f' c ≤ m := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨δ, hδ, hδp⟩ := hd c hc (f' c - m) (by linarith)
    set y : ℝ := c + min δ (d - c) / 2 with hy
    have hmin : 0 < min δ (d - c) := lt_min hδ (by linarith)
    have hcy : c < y := by rw [hy]; linarith
    have hyd : |y - c| < δ := by
      rw [abs_of_pos (by linarith), hy]
      have : min δ (d - c) ≤ δ := min_le_left _ _
      linarith
    have hylt : y < d := by
      have : min δ (d - c) ≤ d - c := min_le_right _ _
      rw [hy]; linarith
    have hycd : y ∈ Ioo c d := ⟨hcy, hylt⟩
    have hb := abs_lt.1 (hδp y hcy.ne' hyd)
    have hkh : m < kulonbsegiHanyados f c y := by
      have := hb.1
      rw [kulonbsegiHanyados] at *
      linarith
    have hconv' := hconv c hc d hdI hcd y hycd
    rw [le_hur_iff_slope hcy hylt] at hconv'
    rw [kulonbsegiHanyados] at hkh
    linarith
  have hright : m ≤ f' d := by
    by_contra hcon
    push_neg at hcon
    obtain ⟨δ, hδ, hδp⟩ := hd d hdI (m - f' d) (by linarith)
    set y : ℝ := d - min δ (d - c) / 2 with hy
    have hmin : 0 < min δ (d - c) := lt_min hδ (by linarith)
    have hyd' : y < d := by rw [hy]; linarith
    have hyd : |y - d| < δ := by
      have h1 : y - d = -(min δ (d - c) / 2) := by rw [hy]; ring
      rw [h1, abs_neg, abs_of_pos (by linarith)]
      have : min δ (d - c) ≤ δ := min_le_left _ _
      linarith
    have hcy : c < y := by
      have : min δ (d - c) ≤ d - c := min_le_right _ _
      rw [hy]; linarith
    have hycd : y ∈ Ioo c d := ⟨hcy, hyd'⟩
    have hb := abs_lt.1 (hδp y hyd'.ne hyd)
    have heq : kulonbsegiHanyados f d y = (f d - f y) / (d - y) := by
      have h1 : y - d ≠ 0 := sub_ne_zero.2 hyd'.ne
      have h2 : d - y ≠ 0 := sub_ne_zero.2 hyd'.ne'
      rw [kulonbsegiHanyados, div_eq_div_iff h1 h2]
      ring
    have hkh : (f d - f y) / (d - y) < m := by
      have := hb.2
      rw [heq] at this
      linarith
    have hconv' := hconv c hc d hdI hcd y hycd
    rw [le_hur_iff_slope_right hcy hyd'] at hconv'
    linarith
  linarith

/-- **8.6.1. Tétel (szükségesség).** Ha `f` konvex az `(a, b)`-n és ott kétszer
differenciálható, akkor `f''(x) ≥ 0` az `(a, b)`-n.

*Bizonyítás.* Az előző lemma szerint `f'` növekedő, tehát a 8.1.2. Tétel szükségességi
része szerint a deriváltja, `f''`, nemnegatív. -/
theorem masodik_derivalt_nemnegativ_ha_konvex {f f' f'' : ℝ → ℝ} {a b : ℝ}
    (hconv : KonvexGorbe f (Ioo a b))
    (hd : ∀ x ∈ Ioo a b, Derivalt f x (f' x))
    (hd2 : ∀ x ∈ Ioo a b, Derivalt f' x (f'' x)) :
    ∀ x ∈ Ioo a b, 0 ≤ f'' x := by
  intro x₀ hx₀
  have hmono := konvex_derivalt_novekedo hconv hd
  set δ : ℝ := min (x₀ - a) (b - x₀) with hδdef
  have hδ : 0 < δ := lt_min (by linarith [hx₀.1]) (by linarith [hx₀.2])
  have hmem : ∀ y, |y - x₀| < δ → y ∈ Ioo a b := by
    intro y hy
    have h1 := abs_lt.1 hy
    have hl : δ ≤ x₀ - a := min_le_left _ _
    have hr : δ ≤ b - x₀ := min_le_right _ _
    exact ⟨by linarith [h1.1], by linarith [h1.2]⟩
  exact derivalt_nemnegativ_ha_novekedo hδ
    (fun u v hu hv huv => hmono u (hmem u hu) v (hmem v hv) huv) (hd2 x₀ hx₀)

/-- **8.6.1. Tétel.** Ha az `f(x)` függvény az `(a, b)` intervallumon kétszer
differenciálható, akkor annak, hogy `f` az `(a, b)`-n konvex legyen, szükséges és elegendő
feltétele, hogy `f''(x) ≥ 0` legyen `(a, b)`-ben. -/
theorem konvex_iff_masodik_derivalt_nemnegativ {f f' f'' : ℝ → ℝ} {a b : ℝ}
    (hd : ∀ x ∈ Ioo a b, Derivalt f x (f' x))
    (hd2 : ∀ x ∈ Ioo a b, Derivalt f' x (f'' x)) :
    KonvexGorbe f (Ioo a b) ↔ ∀ x ∈ Ioo a b, 0 ≤ f'' x :=
  ⟨fun h => masodik_derivalt_nemnegativ_ha_konvex h hd hd2,
   fun h => konvex_ha_masodik_derivalt_nemnegativ hd hd2 h⟩

/-- **8.6.1. Tétel (konkáv eset).** Ha az `f(x)` függvény az `(a, b)` intervallumon kétszer
differenciálható, akkor annak, hogy `f` az `(a, b)`-n konkáv legyen, szükséges és elegendő
feltétele, hogy `f''(x) ≤ 0` legyen `(a, b)`-ben.

*Bizonyítás.* A `-f` függvényre alkalmazzuk a konvex esetet. -/
theorem konkav_iff_masodik_derivalt_nempozitiv {f f' f'' : ℝ → ℝ} {a b : ℝ}
    (hd : ∀ x ∈ Ioo a b, Derivalt f x (f' x))
    (hd2 : ∀ x ∈ Ioo a b, Derivalt f' x (f'' x)) :
    KonkavGorbe f (Ioo a b) ↔ ∀ x ∈ Ioo a b, f'' x ≤ 0 := by
  have hdn : ∀ x ∈ Ioo a b, Derivalt (fun y => -f y) x ((fun y => -f' y) x) := by
    intro x hx
    rw [derivalt_iff_hasDerivAt]
    exact ((derivalt_iff_hasDerivAt f x (f' x)).1 (hd x hx)).neg
  have hd2n : ∀ x ∈ Ioo a b, Derivalt (fun y => -f' y) x ((fun y => -f'' y) x) := by
    intro x hx
    rw [derivalt_iff_hasDerivAt]
    exact ((derivalt_iff_hasDerivAt f' x (f'' x)).1 (hd2 x hx)).neg
  rw [konkav_iff_konvex_neg, konvex_iff_masodik_derivalt_nemnegativ hdn hd2n]
  constructor
  · intro h x hx
    have h' : 0 ≤ -f'' x := h x hx
    linarith
  · intro h x hx
    have h' : f'' x ≤ 0 := h x hx
    show 0 ≤ -f'' x
    linarith

/-! ## 8.7. Inflexiós pont kritériumai deriváltakkal -/

/-- A Darboux-tétel (8.3.1) "csökkenő" változata: ha `f'(x₂) < c < f'(x₁)` és `x₁ < x₂`,
akkor is van olyan `ξ ∈ (x₁, x₂)`, hogy `f'(ξ) = c`.

*Bizonyítás.* A `-f` függvényre alkalmazzuk a 8.3.1. Tételt a `-c` értékkel. -/
theorem darboux_csokkeno {f f' : ℝ → ℝ} {a b x₁ x₂ c : ℝ}
    (hd : ∀ x ∈ Ioo a b, Derivalt f x (f' x)) (h₁ : x₁ ∈ Ioo a b) (h₂ : x₂ ∈ Ioo a b)
    (hlt : x₁ < x₂) (hc₁ : f' x₂ < c) (hc₂ : c < f' x₁) :
    ∃ ξ ∈ Ioo x₁ x₂, f' ξ = c := by
  have hdn : ∀ x ∈ Ioo a b, Derivalt (fun y => -f y) x ((fun y => -f' y) x) := by
    intro x hx
    rw [derivalt_iff_hasDerivAt]
    exact ((derivalt_iff_hasDerivAt f x (f' x)).1 (hd x hx)).neg
  obtain ⟨ξ, hξ, hval⟩ := darboux hdn h₁ h₂ hlt (c := -c)
    (show -f' x₁ < -c by linarith) (show -c < -f' x₂ by linarith)
  refine ⟨ξ, hξ, ?_⟩
  have hval' : -f' ξ = -c := hval
  linarith

/-- Ha `f''` az `x₀` bal oldali környezetében nemnegatív, a jobb oldaliban nempozitív, és
`f''` az `f'` deriváltja, akkor `f''(x₀) = 0`.

*Bizonyítás (8.7.1 gondolatmenete).* Ha például `f''(x₀) = A > 0` volna, akkor egy `x₀`
utáni `x₂` pontra `f''(x₂) ≤ 0 < A/2 < A`, tehát a 8.3.1. Tétel szerint volna olyan
`ξ ∈ (x₀, x₂)`, hogy `f''(ξ) = A/2 > 0`; ez ellentmond annak, hogy `x₀` után `f'' ≤ 0`. -/
theorem masodik_derivalt_nulla_ha_nemnegativbol_nempozitivba {f' f'' : ℝ → ℝ} {x₀ r : ℝ}
    (hr : 0 < r) (hd2 : ∀ x ∈ Ioo (x₀ - r) (x₀ + r), Derivalt f' x (f'' x))
    (hL : ∀ x ∈ Ioo (x₀ - r) x₀, 0 ≤ f'' x)
    (hR : ∀ x ∈ Ioo x₀ (x₀ + r), f'' x ≤ 0) : f'' x₀ = 0 := by
  have hx₀ : x₀ ∈ Ioo (x₀ - r) (x₀ + r) := ⟨by linarith, by linarith⟩
  rcases lt_trichotomy (f'' x₀) 0 with h | h | h
  · exfalso
    set x₁ : ℝ := x₀ - r / 2 with hx₁
    have hm₁ : x₁ ∈ Ioo (x₀ - r) (x₀ + r) := ⟨by rw [hx₁]; linarith, by rw [hx₁]; linarith⟩
    have hL₁ : 0 ≤ f'' x₁ := hL x₁ ⟨by rw [hx₁]; linarith, by rw [hx₁]; linarith⟩
    obtain ⟨ξ, hξ, hval⟩ := darboux_csokkeno hd2 hm₁ hx₀ (by rw [hx₁]; linarith)
      (c := f'' x₀ / 2) (by linarith) (by linarith)
    have : 0 ≤ f'' ξ := hL ξ ⟨lt_trans hm₁.1 hξ.1, hξ.2⟩
    rw [hval] at this
    linarith
  · exact h
  · exfalso
    set x₂ : ℝ := x₀ + r / 2 with hx₂
    have hm₂ : x₂ ∈ Ioo (x₀ - r) (x₀ + r) := ⟨by rw [hx₂]; linarith, by rw [hx₂]; linarith⟩
    have hR₂ : f'' x₂ ≤ 0 := hR x₂ ⟨by rw [hx₂]; linarith, by rw [hx₂]; linarith⟩
    obtain ⟨ξ, hξ, hval⟩ := darboux_csokkeno hd2 hx₀ hm₂ (by rw [hx₂]; linarith)
      (c := f'' x₀ / 2) (by linarith) (by linarith)
    have : f'' ξ ≤ 0 := hR ξ ⟨hξ.1, lt_trans hξ.2 hm₂.2⟩
    rw [hval] at this
    linarith

/-- Az előző lemma tükrözött változata: ha `f''` a bal oldalon nempozitív, a jobb oldalon
nemnegatív, akkor is `f''(x₀) = 0`. -/
theorem masodik_derivalt_nulla_ha_nempozitivbol_nemnegativba {f' f'' : ℝ → ℝ} {x₀ r : ℝ}
    (hr : 0 < r) (hd2 : ∀ x ∈ Ioo (x₀ - r) (x₀ + r), Derivalt f' x (f'' x))
    (hL : ∀ x ∈ Ioo (x₀ - r) x₀, f'' x ≤ 0)
    (hR : ∀ x ∈ Ioo x₀ (x₀ + r), 0 ≤ f'' x) : f'' x₀ = 0 := by
  have hd2n : ∀ x ∈ Ioo (x₀ - r) (x₀ + r), Derivalt (fun y => -f' y) x ((fun y => -f'' y) x) := by
    intro x hx
    rw [derivalt_iff_hasDerivAt]
    exact ((derivalt_iff_hasDerivAt f' x (f'' x)).1 (hd2 x hx)).neg
  have h := masodik_derivalt_nulla_ha_nemnegativbol_nempozitivba hr hd2n
    (fun x hx => show (0:ℝ) ≤ -f'' x by linarith [hL x hx])
    (fun x hx => show -f'' x ≤ (0:ℝ) by linarith [hR x hx])
  have h' : -f'' x₀ = 0 := h
  linarith

/-- **8.7.1. Tétel.** Ha `f(x)` az `x₀` pont valamely környezetében kétszer
differenciálható, és `f(x)`-nek `x₀`-ban inflexiós pontja van, akkor szükségképpen
`f''(x₀) = 0`.

*Bizonyítás (a könyv gondolatmenete).* Az inflexiós pont definíciója szerint `x₀` egyik
oldalán a függvény konvex, a másikon konkáv, tehát a 8.6.1. Tétel szerint `f''` az egyik
félkörnyezetben nemnegatív, a másikban nempozitív. Ha `f''(x₀) ≠ 0` volna, akkor a
8.3.1. Tétel (a derivált Bolzano–Darboux-tulajdonsága) szerint `f''` felvenné az
`f''(x₀)/2` közbülső értéket abban a félkörnyezetben, ahol az előjele ezt kizárja —
ellentmondás. -/
theorem inflexios_pont_masodik_derivalt_nulla {f f' f'' : ℝ → ℝ} {x₀ δ₀ : ℝ} (hδ₀ : 0 < δ₀)
    (hd : ∀ x, |x - x₀| < δ₀ → Derivalt f x (f' x))
    (hd2 : ∀ x, |x - x₀| < δ₀ → Derivalt f' x (f'' x))
    (hinf : InflexiosPont f x₀) : f'' x₀ = 0 := by
  obtain ⟨δ, hδ, hcase⟩ := hinf
  set r : ℝ := min δ δ₀ with hrdef
  have hr : 0 < r := lt_min hδ hδ₀
  have hrδ : r ≤ δ := min_le_left _ _
  have hrδ₀ : r ≤ δ₀ := min_le_right _ _
  have hmem : ∀ y ∈ Ioo (x₀ - r) (x₀ + r), |y - x₀| < δ₀ := by
    intro y hy
    rw [abs_lt]
    exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hd2r : ∀ x ∈ Ioo (x₀ - r) (x₀ + r), Derivalt f' x (f'' x) := fun x hx =>
    hd2 x (hmem x hx)
  -- a bal és a jobb oldali félkörnyezet
  have hsubL : Ioo (x₀ - r) x₀ ⊆ Ioo (x₀ - r) (x₀ + r) := fun y hy =>
    ⟨hy.1, by linarith [hy.2]⟩
  have hsubR : Ioo x₀ (x₀ + r) ⊆ Ioo (x₀ - r) (x₀ + r) := fun y hy =>
    ⟨by linarith [hy.1], hy.2⟩
  have hsubLδ : Ioo (x₀ - r) x₀ ⊆ Ioo (x₀ - δ) x₀ := fun y hy => ⟨by linarith [hy.1], hy.2⟩
  have hsubRδ : Ioo x₀ (x₀ + r) ⊆ Ioo x₀ (x₀ + δ) := fun y hy => ⟨hy.1, by linarith [hy.2]⟩
  have hdL : ∀ x ∈ Ioo (x₀ - r) x₀, Derivalt f x (f' x) := fun x hx =>
    hd x (hmem x (hsubL hx))
  have hd2L : ∀ x ∈ Ioo (x₀ - r) x₀, Derivalt f' x (f'' x) := fun x hx =>
    hd2 x (hmem x (hsubL hx))
  have hdR : ∀ x ∈ Ioo x₀ (x₀ + r), Derivalt f x (f' x) := fun x hx =>
    hd x (hmem x (hsubR hx))
  have hd2R : ∀ x ∈ Ioo x₀ (x₀ + r), Derivalt f' x (f'' x) := fun x hx =>
    hd2 x (hmem x (hsubR hx))
  rcases hcase with ⟨hconvL, hconcR⟩ | ⟨hconcL, hconvR⟩
  · have hL : ∀ x ∈ Ioo (x₀ - r) x₀, 0 ≤ f'' x :=
      masodik_derivalt_nemnegativ_ha_konvex (konvexGorbe_mono hconvL hsubLδ) hdL hd2L
    have hR : ∀ x ∈ Ioo x₀ (x₀ + r), f'' x ≤ 0 :=
      (konkav_iff_masodik_derivalt_nempozitiv hdR hd2R).1 (konkavGorbe_mono hconcR hsubRδ)
    exact masodik_derivalt_nulla_ha_nemnegativbol_nempozitivba hr hd2r hL hR
  · have hL : ∀ x ∈ Ioo (x₀ - r) x₀, f'' x ≤ 0 :=
      (konkav_iff_masodik_derivalt_nempozitiv hdL hd2L).1 (konkavGorbe_mono hconcL hsubLδ)
    have hR : ∀ x ∈ Ioo x₀ (x₀ + r), 0 ≤ f'' x :=
      masodik_derivalt_nemnegativ_ha_konvex (konvexGorbe_mono hconvR hsubRδ) hdR hd2R
    exact masodik_derivalt_nulla_ha_nempozitivbol_nemnegativba hr hd2r hL hR

/-- Ha `f''` az `x₀` bal oldali félkörnyezetében nempozitív, a jobb oldaliban nemnegatív,
akkor a 8.6.1. Tétel szerint `f` balra konkáv, jobbra konvex, azaz `x₀`-ban inflexiós
pontja van. -/
theorem inflexios_ha_masodik_derivalt_negativbol_pozitivba {f f' f'' : ℝ → ℝ} {x₀ r : ℝ}
    (hr : 0 < r)
    (hd : ∀ x ∈ Ioo (x₀ - r) (x₀ + r), Derivalt f x (f' x))
    (hd2 : ∀ x ∈ Ioo (x₀ - r) (x₀ + r), Derivalt f' x (f'' x))
    (hL : ∀ y ∈ Ioo (x₀ - r) x₀, f'' y ≤ 0)
    (hR : ∀ y ∈ Ioo x₀ (x₀ + r), 0 ≤ f'' y) :
    InflexiosPont f x₀ := by
  have hsubL : Ioo (x₀ - r) x₀ ⊆ Ioo (x₀ - r) (x₀ + r) := fun y hy =>
    ⟨hy.1, by linarith [hy.2]⟩
  have hsubR : Ioo x₀ (x₀ + r) ⊆ Ioo (x₀ - r) (x₀ + r) := fun y hy =>
    ⟨by linarith [hy.1], hy.2⟩
  refine ⟨r, hr, Or.inr ⟨?_, ?_⟩⟩
  · exact (konkav_iff_masodik_derivalt_nempozitiv (fun x hx => hd x (hsubL hx))
      (fun x hx => hd2 x (hsubL hx))).2 hL
  · exact konvex_ha_masodik_derivalt_nemnegativ (fun x hx => hd x (hsubR hx))
      (fun x hx => hd2 x (hsubR hx)) hR

/-- Az előző lemma tükrözött változata: ha `f''` balra nemnegatív, jobbra nempozitív,
akkor `f` balra konvex, jobbra konkáv, azaz `x₀`-ban inflexiós pontja van. -/
theorem inflexios_ha_masodik_derivalt_pozitivbol_negativba {f f' f'' : ℝ → ℝ} {x₀ r : ℝ}
    (hr : 0 < r)
    (hd : ∀ x ∈ Ioo (x₀ - r) (x₀ + r), Derivalt f x (f' x))
    (hd2 : ∀ x ∈ Ioo (x₀ - r) (x₀ + r), Derivalt f' x (f'' x))
    (hL : ∀ y ∈ Ioo (x₀ - r) x₀, 0 ≤ f'' y)
    (hR : ∀ y ∈ Ioo x₀ (x₀ + r), f'' y ≤ 0) :
    InflexiosPont f x₀ := by
  have hsubL : Ioo (x₀ - r) x₀ ⊆ Ioo (x₀ - r) (x₀ + r) := fun y hy =>
    ⟨hy.1, by linarith [hy.2]⟩
  have hsubR : Ioo x₀ (x₀ + r) ⊆ Ioo (x₀ - r) (x₀ + r) := fun y hy =>
    ⟨by linarith [hy.1], hy.2⟩
  refine ⟨r, hr, Or.inl ⟨?_, ?_⟩⟩
  · exact konvex_ha_masodik_derivalt_nemnegativ (fun x hx => hd x (hsubL hx))
      (fun x hx => hd2 x (hsubL hx)) hL
  · exact (konkav_iff_masodik_derivalt_nempozitiv (fun x hx => hd x (hsubR hx))
      (fun x hx => hd2 x (hsubR hx))).2 hR

/-- **8.7.2. Tétel.** Ha `f'''(x₀) ≠ 0` és `f''(x₀) = 0`, akkor az `x₀` pontban az `f(x)`
függvénynek inflexiós pontja van.

*Bizonyítás (a könyv gondolatmenete).* Ha `f'''(x₀) ≠ 0`, akkor a 8.2.1. Tétel szerint az
`f''(x)` függvény az `x₀` pontnál növekedő vagy csökkenő, így `x₀` valamely
félkörnyezeteiben `f''(x)` különböző előjelű; tehát a 8.6.1. Tétel szerint az `f(x)`
függvény az `x₀` pontban konvexből konkávba, vagy fordítva megy át, tehát `x₀`-ban valóban
inflexiós pont van. -/
theorem inflexios_pont_ha_harmadik_derivalt_nem_nulla {f f' f'' : ℝ → ℝ} {x₀ δ₀ M : ℝ}
    (hδ₀ : 0 < δ₀)
    (hd : ∀ x, |x - x₀| < δ₀ → Derivalt f x (f' x))
    (hd2 : ∀ x, |x - x₀| < δ₀ → Derivalt f' x (f'' x))
    (h2 : f'' x₀ = 0) (h3 : Derivalt f'' x₀ M) (hM : M ≠ 0) :
    InflexiosPont f x₀ := by
  rcases lt_or_gt_of_ne hM with hneg | hpos
  · -- `f'''(x₀) < 0`: `f''` az `x₀`-nál csökkenő, tehát előtte pozitív, utána negatív
    obtain ⟨α, hα, hp⟩ := pontnal_csokkeno_ha_derivalt_negativ h3 hneg
    set r : ℝ := min α δ₀ with hrdef
    have hr : 0 < r := lt_min hα hδ₀
    have hrα : r ≤ α := min_le_left _ _
    have hrδ₀ : r ≤ δ₀ := min_le_right _ _
    have hmem : ∀ y ∈ Ioo (x₀ - r) (x₀ + r), |y - x₀| < δ₀ := by
      intro y hy
      rw [abs_lt]
      exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
    have hmemα : ∀ y ∈ Ioo (x₀ - r) (x₀ + r), |y - x₀| < α := by
      intro y hy
      rw [abs_lt]
      exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
    have hzR : x₀ + r / 2 ∈ Ioo (x₀ - r) (x₀ + r) := ⟨by linarith, by linarith⟩
    have hzL : x₀ - r / 2 ∈ Ioo (x₀ - r) (x₀ + r) := ⟨by linarith, by linarith⟩
    have hsubL : Ioo (x₀ - r) x₀ ⊆ Ioo (x₀ - r) (x₀ + r) := fun y hy =>
      ⟨hy.1, by linarith [hy.2]⟩
    have hsubR : Ioo x₀ (x₀ + r) ⊆ Ioo (x₀ - r) (x₀ + r) := fun y hy =>
      ⟨by linarith [hy.1], hy.2⟩
    refine inflexios_ha_masodik_derivalt_pozitivbol_negativba hr
      (fun x hx => hd x (hmem x hx)) (fun x hx => hd2 x (hmem x hx)) ?_ ?_
    · intro y hy
      have hlt := (hp y (x₀ + r / 2) (hmemα y (hsubL hy)) (hmemα _ hzR) hy.2
        (by linarith)).1
      rw [h2] at hlt
      linarith
    · intro y hy
      have hlt := (hp (x₀ - r / 2) y (hmemα _ hzL) (hmemα y (hsubR hy)) (by linarith)
        hy.1).2
      rw [h2] at hlt
      linarith
  · -- `f'''(x₀) > 0`: `f''` az `x₀`-nál növekedő, tehát előtte negatív, utána pozitív
    obtain ⟨α, hα, hp⟩ := pontnal_novekedo_ha_derivalt_pozitiv h3 hpos
    set r : ℝ := min α δ₀ with hrdef
    have hr : 0 < r := lt_min hα hδ₀
    have hrα : r ≤ α := min_le_left _ _
    have hrδ₀ : r ≤ δ₀ := min_le_right _ _
    have hmem : ∀ y ∈ Ioo (x₀ - r) (x₀ + r), |y - x₀| < δ₀ := by
      intro y hy
      rw [abs_lt]
      exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
    have hmemα : ∀ y ∈ Ioo (x₀ - r) (x₀ + r), |y - x₀| < α := by
      intro y hy
      rw [abs_lt]
      exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
    have hzR : x₀ + r / 2 ∈ Ioo (x₀ - r) (x₀ + r) := ⟨by linarith, by linarith⟩
    have hzL : x₀ - r / 2 ∈ Ioo (x₀ - r) (x₀ + r) := ⟨by linarith, by linarith⟩
    have hsubL : Ioo (x₀ - r) x₀ ⊆ Ioo (x₀ - r) (x₀ + r) := fun y hy =>
      ⟨hy.1, by linarith [hy.2]⟩
    have hsubR : Ioo x₀ (x₀ + r) ⊆ Ioo (x₀ - r) (x₀ + r) := fun y hy =>
      ⟨by linarith [hy.1], hy.2⟩
    refine inflexios_ha_masodik_derivalt_negativbol_pozitivba hr
      (fun x hx => hd x (hmem x hx)) (fun x hx => hd2 x (hmem x hx)) ?_ ?_
    · intro y hy
      have hlt := (hp y (x₀ + r / 2) (hmemα y (hsubL hy)) (hmemα _ hzR) hy.2
        (by linarith)).1
      rw [h2] at hlt
      linarith
    · intro y hy
      have hlt := (hp (x₀ - r / 2) y (hmemα _ hzL) (hmemα y (hsubR hy)) (by linarith)
        hy.1).2
      rw [h2] at hlt
      linarith

/-! ## Példa: a köbfüggvénynek a `0` pontban inflexiós pontja van -/

/-- Az `f(x) = x³` függvényre `f''(0) = 0` és `f'''(0) = 6 ≠ 0`, tehát a 8.7.2. Tétel
szerint a `0` pontban inflexiós pont van. -/
theorem pelda_kobfuggveny_inflexio : InflexiosPont (fun x : ℝ => x ^ 3) 0 := by
  have hd : ∀ x : ℝ, |x - 0| < 1 →
      Derivalt (fun y : ℝ => y ^ 3) x ((fun y : ℝ => 3 * y ^ 2) x) := by
    intro x _
    rw [derivalt_iff_hasDerivAt]
    have h : HasDerivAt (fun y : ℝ => y ^ 3) (((3 : ℕ) : ℝ) * x ^ (3 - 1)) x :=
      hasDerivAt_pow 3 x
    have he : ((3 : ℕ) : ℝ) * x ^ (3 - 1) = 3 * x ^ 2 := by norm_num
    rw [he] at h
    exact h
  have hd2 : ∀ x : ℝ, |x - 0| < 1 →
      Derivalt (fun y : ℝ => 3 * y ^ 2) x ((fun y : ℝ => 6 * y) x) := by
    intro x _
    rw [derivalt_iff_hasDerivAt]
    have h : HasDerivAt (fun y : ℝ => 3 * y ^ 2) (3 * (((2 : ℕ) : ℝ) * x ^ (2 - 1))) x :=
      (hasDerivAt_pow 2 x).const_mul 3
    have he : (3 : ℝ) * (((2 : ℕ) : ℝ) * x ^ (2 - 1)) = 6 * x := by norm_num; ring
    rw [he] at h
    exact h
  have h3 : Derivalt (fun y : ℝ => 6 * y) 0 6 := by
    rw [derivalt_iff_hasDerivAt]
    simpa using (hasDerivAt_id (0 : ℝ)).const_mul (6 : ℝ)
  exact inflexios_pont_ha_harmadik_derivalt_nem_nulla (δ₀ := 1) one_pos hd hd2
    (by norm_num) h3 (by norm_num)


/-! ## 8.8. A függvénydiszkusszió általános sémája

A könyv 8.8. pontja a fentiek összefoglalásaként a következő sémát adja a
függvénydiszkussziós feladatok megoldására.

**I. Meghatározzuk:**
1. a függvény értelmezési tartományát (5.1. pont),
2. a szakadási pontokat és folytonossági intervallumokat (5.2., 5.19. pont),
3. az értékkészletet (5.1. pont),
4. a zérushelyeket és jeltartási intervallumokat (5.14. pont, Bolzano-tétel),
5. a görbe szimmetriatengelyeit és pontjait (5.1.11. Definíció: páros, páratlan
   függvények).

**II. Meghatározzuk:**
1. a monotonitási intervallumokat (8.1.2. Tétel),
2. a szélső érték helyeit és értékeit (8.4.1., 8.5.1. Tétel).

**III. Meghatározzuk:**
1. a függvénygörbe konvex és konkáv részeit (8.6.1. Tétel),
2. a görbe inflexiós pontjait (8.7.1., 8.7.2. Tétel).

**IV.** Megrajzoljuk a függvény görbéjét (ha lehet).

Ha a függvény deriváltja folytonos, akkor `f'(x)` zérushelyei a monotonitási
intervallumokat is megadják, és e helyeken kell csak a szélső értékeket keresni.
Ha `f''(x)` is létezik és folytonos, akkor ennek a zérushelyei közt lesznek a függvény
konvex és konkáv intervallumainak határai, s a zérushelyeknél lehetnek az inflexiós
pontok.
-/

end Leindler.Ch08
