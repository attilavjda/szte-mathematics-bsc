import Mathlib
import Analizis.Ch05a_FuggvenyekAlapfogalmak
import Analizis.Ch05b_Folytonossag
import Analizis.Ch05d_FuggvenyHatarertek
import Analizis.Ch05e_AlgebraiFuggvenyek

/-!
# Leindler László: Analízis — kiegészítések az 5. fejezethez

Ez a fájl az 5. fejezet azon pontjait formalizálja, amelyek a korábbi modulokból
kimaradtak:

* **5.1.9.** a görbe inflexiós pontjának fogalma (az 5.1.10. függvényváltozat mellett),
* **5.3.6.** a félig folytonosság *Heine-féle* (sorozatos) definíciója és ekvivalenciája
  az 5.3.5. Cauchy-féle definícióval,
* **5.5.1.** az összetett függvény fogalma (értelmezési tartomány, hozzárendelési
  törvény, külső és belső függvény),
* **5.7.4–5.7.6.** a racionális egész, a racionális tört- és a racionális függvények
  fogalma és folytonossága,
* **5.15.4.** a féloldali határérték *Heine-féle* definíciója és ekvivalenciája az
  5.15.5. Cauchy-féle definícióval,
* **5.16.4.** a meg nem szüntethető szakadási helyek fogalma.
-/

namespace Leindler.Ch05

open Set Leindler

/-! ## 5.1.9. Definíció: a görbe inflexiós pontja -/

/-- **5.1.9. Definíció.** *Inflexiós pontnak* egy `G` görbe olyan `P` pontját nevezzük,
ahol a görbe konvexből konkávba (vagy fordítva) megy át.

A görbét az `f` függvény grafikonjaként adjuk meg: a `P = (x₀, y₀)` pont akkor pontja
a görbének, ha `y₀ = f(x₀)`, és akkor inflexiós pont, ha `f`-nek `x₀`-ban inflexiós
pontja van (5.1.10. Definíció). -/
def GorbeInflexiosPontja (f : ℝ → ℝ) (P : ℝ × ℝ) : Prop :=
  P.2 = f P.1 ∧ InflexiosPont f P.1

/-- Az 5.1.9. és az 5.1.10. Definíció megfelelése: az `(x₀, f(x₀))` görbepont pontosan
akkor inflexiós pontja a görbének, ha `f`-nek `x₀`-ban inflexiós pontja van. -/
theorem gorbeInflexiosPontja_iff (f : ℝ → ℝ) (x₀ : ℝ) :
    GorbeInflexiosPontja f (x₀, f x₀) ↔ InflexiosPont f x₀ := by
  simp [GorbeInflexiosPontja]

/-! ## 5.3.6. Definíció: a félig folytonosság Heine-féle alakja -/

/-- **5.3.6. Definíció (Heine).** Az `f` függvény `x₀`-ban *felülről félig folytonos*,
ha bármely `xₙ → x₀` sorozatra `(f(xₙ) - f(x₀))⁺ → 0`, ahol `t⁺ = max(t, 0)` a pozitív
rész. -/
def HeineFelulrolFeligFolytonos (f : ℝ → ℝ) (x₀ : ℝ) : Prop :=
  ∀ a : Ch04.Sorozat, Ch04.HatarErtek a x₀ →
    Ch04.HatarErtek (fun n => max (f (a n) - f x₀) 0) 0

/-- **5.3.6. Definíció (Heine).** Az `f` függvény `x₀`-ban *alulról félig folytonos*,
ha bármely `xₙ → x₀` sorozatra `(f(x₀) - f(xₙ))⁺ → 0`. -/
def HeineAlulrolFeligFolytonos (f : ℝ → ℝ) (x₀ : ℝ) : Prop :=
  ∀ a : Ch04.Sorozat, Ch04.HatarErtek a x₀ →
    Ch04.HatarErtek (fun n => max (f x₀ - f (a n)) 0) 0

/-- Segédlemma: az `1/(n+1)` sugarú környezetekből választott pontok sorozata `x₀`-hoz
tart. -/
theorem kozelito_sorozat_hatarertek {x : Ch04.Sorozat} {x₀ : ℝ}
    (hx : ∀ n : ℕ, |x n - x₀| < 1 / (n + 1 : ℝ)) : Ch04.HatarErtek x x₀ := by
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
  refine ⟨N, fun n hn => ?_⟩
  have h1 : (1 : ℝ) / ε < n := lt_of_lt_of_le hN (by exact_mod_cast hn.le)
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hlt : 1 / ((n : ℝ) + 1) < ε := by
    rw [div_lt_iff₀ hn1]
    rw [div_lt_iff₀ hε] at h1
    nlinarith
  exact lt_of_lt_of_le (hx n) hlt.le

/-- **5.3.5–5.3.6. Tétel.** A felülről félig folytonosság Cauchy-féle (5.3.5.) és
Heine-féle (5.3.6.) definíciója ekvivalens.

*Bizonyítás.* *Cauchy ⇒ Heine.* Legyen `ε > 0` és `xₙ → x₀`. Az `ε`-hoz tartozó `δ`-hoz
van olyan `ν`, hogy `n > ν` esetén `|xₙ - x₀| < δ`, ekkor `f(xₙ) < f(x₀) + ε`, tehát
`(f(xₙ) - f(x₀))⁺ < ε`.

*Heine ⇒ Cauchy* (indirekt). Ha `f` nem félig folytonos, akkor van olyan `ε₀ > 0`, hogy
minden `δ > 0`-hoz van `|x - x₀| < δ` pont, ahol `f(x₀) + ε₀ ≤ f(x)`. A `δ = 1/(n+1)`
választással kapott `xₙ` pontokra `xₙ → x₀`, de `(f(xₙ) - f(x₀))⁺ ≥ ε₀`, ami ellentmond
a Heine-féle feltételnek. -/
theorem heineFelulrolFeligFolytonos_iff (f : ℝ → ℝ) (x₀ : ℝ) :
    HeineFelulrolFeligFolytonos f x₀ ↔ FelulrolFeligFolytonos f x₀ := by
  constructor
  · intro hH
    by_contra hC
    rw [FelulrolFeligFolytonos] at hC
    push_neg at hC
    obtain ⟨ε₀, hε₀, hbad⟩ := hC
    choose x hx hfx using fun n : ℕ => hbad (1 / (n + 1 : ℝ)) (by positivity)
    have hxlim : Ch04.HatarErtek x x₀ := kozelito_sorozat_hatarertek hx
    obtain ⟨N, hN⟩ := hH x hxlim ε₀ hε₀
    have hge : ε₀ ≤ max (f (x (N + 1)) - f x₀) 0 :=
      le_max_of_le_left (by linarith [hfx (N + 1)])
    have := hN (N + 1) (by omega)
    rw [sub_zero, abs_of_nonneg (le_max_right _ _)] at this
    linarith
  · intro hC a ha ε hε
    obtain ⟨δ, hδ, hδp⟩ := hC ε hε
    obtain ⟨N, hN⟩ := ha δ hδ
    refine ⟨N, fun n hn => ?_⟩
    have h1 : f (a n) < f x₀ + ε := hδp (a n) (hN n hn)
    rw [sub_zero, abs_of_nonneg (le_max_right _ _)]
    exact max_lt (by linarith) hε

/-- **5.3.5–5.3.6. Tétel.** Az alulról félig folytonosság Cauchy- és Heine-féle
definíciója ekvivalens. -/
theorem heineAlulrolFeligFolytonos_iff (f : ℝ → ℝ) (x₀ : ℝ) :
    HeineAlulrolFeligFolytonos f x₀ ↔ AlulrolFeligFolytonos f x₀ := by
  constructor
  · intro hH
    by_contra hC
    rw [AlulrolFeligFolytonos] at hC
    push_neg at hC
    obtain ⟨ε₀, hε₀, hbad⟩ := hC
    choose x hx hfx using fun n : ℕ => hbad (1 / (n + 1 : ℝ)) (by positivity)
    have hxlim : Ch04.HatarErtek x x₀ := kozelito_sorozat_hatarertek hx
    obtain ⟨N, hN⟩ := hH x hxlim ε₀ hε₀
    have hge : ε₀ ≤ max (f x₀ - f (x (N + 1))) 0 :=
      le_max_of_le_left (by linarith [hfx (N + 1)])
    have := hN (N + 1) (by omega)
    rw [sub_zero, abs_of_nonneg (le_max_right _ _)] at this
    linarith
  · intro hC a ha ε hε
    obtain ⟨δ, hδ, hδp⟩ := hC ε hε
    obtain ⟨N, hN⟩ := ha δ hδ
    refine ⟨N, fun n hn => ?_⟩
    have h1 : f x₀ - ε < f (a n) := hδp (a n) (hN n hn)
    rw [sub_zero, abs_of_nonneg (le_max_right _ _)]
    exact max_lt (by linarith) hε

/-! ## 5.5.1. Definíció: összetett függvény -/

/-- **5.5.1. Definíció.** Az `f(g(x))` *összetett függvény* hozzárendelési törvénye: az
`x₀` helyen az összetett függvény értéke az `f` függvénynek a `g(x₀)` helyen felvett
értéke. Az `f` a *külső*, a `g` a *belső* függvény. -/
def OsszetettFv (f g : ℝ → ℝ) : ℝ → ℝ := fun x => f (g x)

/-- **5.5.1. Definíció.** Az `f(g(x))` összetett függvény *értelmezési tartománya* a `g`
értelmezési tartományának azon része, ahol `g` olyan értéket vesz fel, ahol `f`
értelmezve van. -/
def OsszetettErtelmezesiTartomany (Df Dg : Set ℝ) (g : ℝ → ℝ) : Set ℝ :=
  {x | x ∈ Dg ∧ g x ∈ Df}

/-- Az összetett függvény hozzárendelési törvénye. -/
theorem osszetettFv_ertek (f g : ℝ → ℝ) (x₀ : ℝ) : OsszetettFv f g x₀ = f (g x₀) := rfl

/-- Az összetett függvény a szokásos függvénykompozíció. -/
theorem osszetettFv_eq_comp (f g : ℝ → ℝ) : OsszetettFv f g = f ∘ g := rfl

/-- Az összetett függvény értelmezési tartománya a `g` értelmezési tartományának és a
`g` szerinti ősképnek a metszete. -/
theorem osszetettErtelmezesiTartomany_eq (Df Dg : Set ℝ) (g : ℝ → ℝ) :
    OsszetettErtelmezesiTartomany Df Dg g = Dg ∩ g ⁻¹' Df := rfl

/-- Az összetett függvény értelmezési tartománya része a belső függvény értelmezési
tartományának. -/
theorem osszetettErtelmezesiTartomany_subset (Df Dg : Set ℝ) (g : ℝ → ℝ) :
    OsszetettErtelmezesiTartomany Df Dg g ⊆ Dg := fun _ hx => hx.1

/-- **5.5.2. Tétel** (vö. 5.4.7.). Folytonos függvények összetétele folytonos: ha `g`
folytonos `x₀`-ban és `f` folytonos `g(x₀)`-ban, akkor `f(g(x))` folytonos `x₀`-ban. -/
theorem osszetettFv_folytonos {f g : ℝ → ℝ} {x₀ : ℝ}
    (hg : CauchyFolytonos g x₀) (hf : CauchyFolytonos f (g x₀)) :
    CauchyFolytonos (OsszetettFv f g) x₀ := by
  have hg' : HeineFolytonos g x₀ := (heineFolytonos_iff_cauchyFolytonos g x₀).2 hg
  have hf' : HeineFolytonos f (g x₀) := (heineFolytonos_iff_cauchyFolytonos f (g x₀)).2 hf
  exact (heineFolytonos_iff_cauchyFolytonos (fun x => f (g x)) x₀).1
    (folytonos_osszetett hg' hf')

/-! ## 5.7.4–5.7.6. Racionális függvények -/

/-- **5.7.3. Definíció.** Az `f` függvény *racionális egész függvény* (polinom), ha
előáll `f(x) = aₙxⁿ + ⋯ + a₁x + a₀` alakban. -/
def RacionalisEgeszFv (h : ℝ → ℝ) : Prop := ∃ p : Polynomial ℝ, ∀ x, h x = p.eval x

/-- **5.7.5. Definíció.** *Racionális törtfüggvény* olyan függvény, amely két polinom
hányadosaként állítható elő. -/
def RacionalisTortFv (h : ℝ → ℝ) : Prop :=
  ∃ p q : Polynomial ℝ, q ≠ 0 ∧ ∀ x, h x = p.eval x / q.eval x

/-- **5.7.6. Definíció.** A racionális egész és törtfüggvényeket közös néven *racionális
függvényeknek* nevezzük. -/
def RacionalisFv (h : ℝ → ℝ) : Prop := RacionalisEgeszFv h ∨ RacionalisTortFv h

/-- **5.7.4. Tétel.** A racionális egész függvények mindenütt folytonosak.

*Bizonyítás.* Felhasználva azt, hogy az `f(x) = c` és `f(x) = x` függvények mindenütt
folytonosak, és hogy folytonos függvények összege és szorzata is folytonos
(5.4.4. Tétel), adódik az állítás. -/
theorem racionalisEgesz_folytonos {h : ℝ → ℝ} (hh : RacionalisEgeszFv h) (x₀ : ℝ) :
    CauchyFolytonos h x₀ := by
  obtain ⟨p, hp⟩ := hh
  have : h = fun x => p.eval x := funext hp
  rw [this]
  exact folytonos_polinom p x₀

/-- **5.7.5. Tétel.** A racionális törtfüggvények a nevező zérushelyeinek kivételével
mindenütt folytonosak. -/
theorem racionalisTort_folytonos {h : ℝ → ℝ} (p q : Polynomial ℝ)
    (hpq : ∀ x, h x = p.eval x / q.eval x) {x₀ : ℝ} (hq : q.eval x₀ ≠ 0) :
    CauchyFolytonos h x₀ := by
  have : h = fun x => p.eval x / q.eval x := funext hpq
  rw [this]
  exact folytonos_racionalis p q x₀ hq

/-- Minden racionális egész függvény egyben racionális törtfüggvény is (nevezőnek az
azonosan `1` polinomot választva). -/
theorem racionalisEgesz_racionalisTort {h : ℝ → ℝ} (hh : RacionalisEgeszFv h) :
    RacionalisTortFv h := by
  obtain ⟨p, hp⟩ := hh
  exact ⟨p, 1, one_ne_zero, fun x => by simp [hp x]⟩

/-- Minden racionális egész függvény racionális függvény. -/
theorem racionalisEgesz_racionalis {h : ℝ → ℝ} (hh : RacionalisEgeszFv h) :
    RacionalisFv h := Or.inl hh

/-- **5.7.5. Példa.** A negatív egész kitevős hatványfüggvény, `y = x⁻ⁿ`, racionális
törtfüggvény. -/
theorem negativ_kitevos_hatvany_racionalisTort (n : ℕ) :
    RacionalisTortFv (fun x : ℝ => 1 / x ^ n) :=
  ⟨1, Polynomial.X ^ n, pow_ne_zero n Polynomial.X_ne_zero, fun x => by simp⟩

/-- **5.7.5. Példa.** A lineáris törtfüggvény, `y = (ax + b)/(cx + d)`, racionális
törtfüggvény (`c ≠ 0`). -/
theorem linearis_tortfuggveny_racionalisTort (a b c d : ℝ) (hc : c ≠ 0) :
    RacionalisTortFv (fun x : ℝ => (a * x + b) / (c * x + d)) := by
  refine ⟨Polynomial.C a * Polynomial.X + Polynomial.C b,
    Polynomial.C c * Polynomial.X + Polynomial.C d, ?_, fun x => by simp⟩
  intro hzero
  have := congrArg (fun r : Polynomial ℝ => r.coeff 1) hzero
  simp [Polynomial.coeff_add, Polynomial.coeff_C] at this
  exact hc this

/-- **5.7.5. Példa.** A lineáris törtfüggvény folytonos minden olyan helyen, ahol a
nevező nem tűnik el. -/
theorem linearis_tortfuggveny_folytonos {a b c d x₀ : ℝ} (h : c * x₀ + d ≠ 0) :
    CauchyFolytonos (fun x : ℝ => (a * x + b) / (c * x + d)) x₀ :=
  (heineFolytonos_iff_cauchyFolytonos (fun x : ℝ => (a * x + b) / (c * x + d)) x₀).1
    (folytonos_div
      ((heineFolytonos_iff_cauchyFolytonos (fun x : ℝ => a * x + b) x₀).2
        (folytonos_linearis a b x₀))
      ((heineFolytonos_iff_cauchyFolytonos (fun x : ℝ => c * x + d) x₀).2
        (folytonos_linearis c d x₀)) h)

/-! ## 5.15.4. Definíció: féloldali határérték Heine-féle alakban -/

/-- **5.15.4. Definíció (Heine).** Az `f`-nek `x₀`-ban létezik a *jobb oldali*
határértéke, és az `c`, ha valahányszor `xₙ → x₀`, `xₙ > x₀`, mindannyiszor
`f(xₙ) → c`. -/
def HeineJobbHatarErtek (f : ℝ → ℝ) (x₀ c : ℝ) : Prop :=
  ∀ a : Ch04.Sorozat, Ch04.HatarErtek a x₀ → (∀ n, x₀ < a n) →
    Ch04.HatarErtek (fun n => f (a n)) c

/-- **5.15.4. Definíció (Heine).** Az `f`-nek `x₀`-ban létezik a *bal oldali*
határértéke, és az `c`, ha valahányszor `xₙ → x₀`, `xₙ < x₀`, mindannyiszor
`f(xₙ) → c`. -/
def HeineBalHatarErtek (f : ℝ → ℝ) (x₀ c : ℝ) : Prop :=
  ∀ a : Ch04.Sorozat, Ch04.HatarErtek a x₀ → (∀ n, a n < x₀) →
    Ch04.HatarErtek (fun n => f (a n)) c

/-- **5.15.4–5.15.5. Tétel.** A jobb oldali határérték Heine-féle és Cauchy-féle
definíciója ekvivalens.

*Bizonyítás.* *Cauchy ⇒ Heine*: ha `xₙ → x₀` és `xₙ > x₀`, akkor az `ε`-hoz tartozó
`δ`-tól kezdve `|f(xₙ) - c| < ε`.

*Heine ⇒ Cauchy* (indirekt): ha a Cauchy-féle feltétel nem teljesül, akkor van olyan
`ε₀ > 0`, hogy minden `δ > 0`-hoz van `x > x₀`, `|x - x₀| < δ` pont
`|f(x) - c| ≥ ε₀`-lal. A `δ = 1/(n+1)` választással adódó `xₙ` sorozat `x₀`-hoz tart
jobbról, de `f(xₙ)` nem tart `c`-hez. -/
theorem heineJobbHatarErtek_iff (f : ℝ → ℝ) (x₀ c : ℝ) :
    HeineJobbHatarErtek f x₀ c ↔ JobbHatarErtek f x₀ c := by
  constructor
  · intro hH
    by_contra hC
    rw [JobbHatarErtek] at hC
    push_neg at hC
    obtain ⟨ε₀, hε₀, hbad⟩ := hC
    choose x hgt hx hfx using fun n : ℕ => hbad (1 / (n + 1 : ℝ)) (by positivity)
    have hxlim : Ch04.HatarErtek x x₀ := kozelito_sorozat_hatarertek hx
    obtain ⟨N, hN⟩ := hH x hxlim hgt ε₀ hε₀
    exact absurd (hN (N + 1) (by omega)) (not_lt.2 (hfx (N + 1)))
  · intro hC a ha hgt ε hε
    obtain ⟨δ, hδ, hδp⟩ := hC ε hε
    obtain ⟨N, hN⟩ := ha δ hδ
    exact ⟨N, fun n hn => hδp (a n) (hgt n) (hN n hn)⟩

/-- **5.15.4–5.15.5. Tétel.** A bal oldali határérték Heine-féle és Cauchy-féle
definíciója ekvivalens. -/
theorem heineBalHatarErtek_iff (f : ℝ → ℝ) (x₀ c : ℝ) :
    HeineBalHatarErtek f x₀ c ↔ BalHatarErtek f x₀ c := by
  constructor
  · intro hH
    by_contra hC
    rw [BalHatarErtek] at hC
    push_neg at hC
    obtain ⟨ε₀, hε₀, hbad⟩ := hC
    choose x hlt hx hfx using fun n : ℕ => hbad (1 / (n + 1 : ℝ)) (by positivity)
    have hxlim : Ch04.HatarErtek x x₀ := kozelito_sorozat_hatarertek hx
    obtain ⟨N, hN⟩ := hH x hxlim hlt ε₀ hε₀
    exact absurd (hN (N + 1) (by omega)) (not_lt.2 (hfx (N + 1)))
  · intro hC a ha hlt ε hε
    obtain ⟨δ, hδ, hδp⟩ := hC ε hε
    obtain ⟨N, hN⟩ := ha δ hδ
    exact ⟨N, fun n hn => hδp (a n) (hlt n) (hN n hn)⟩

/-! ## 5.16.4. Definíció: meg nem szüntethető szakadási helyek -/

/-- **5.16.4. Definíció.** Az első- és másodfajú szakadási helyeket *meg nem
szüntethető* szakadási helyeknek nevezzük. -/
def MegNemSzuntethetoSzakadas (f : ℝ → ℝ) (x₀ : ℝ) : Prop :=
  ElsofajuSzakadas f x₀ ∨ MasodfajuSzakadas f x₀

/-- **5.16.4. Példa.** A szignumfüggvénynek a `0` helyen meg nem szüntethető (elsőfajú)
szakadása van. -/
theorem szignum_meg_nem_szuntetheto : MegNemSzuntethetoSzakadas szignum 0 :=
  Or.inl szignum_elsofaju

end Leindler.Ch05
