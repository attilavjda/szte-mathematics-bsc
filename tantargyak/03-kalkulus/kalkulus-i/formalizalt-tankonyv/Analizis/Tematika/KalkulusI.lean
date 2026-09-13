import Mathlib
import Analizis.Ch03_ValosSzamok
import Analizis.Ch04a_SorozatokAlapok
import Analizis.Ch05a_FuggvenyekAlapfogalmak
import Analizis.Ch05b_Folytonossag
import Analizis.Ch05c_ZartIntervallum
import Analizis.Ch05d_FuggvenyHatarertek
import Analizis.Ch06a_Differencialhatosag
import Analizis.Ch06b_ElemiDerivaltak
import Analizis.Ch07a_MagasabbrenduDerivaltak
import Analizis.Ch07b_TaylorFormula
import Analizis.Ch08a_MonotonitasSzelsoertek
import Analizis.Ch08b_KonvexsegInflexio

/-!
# Kalkulus I. előadás (MBLK37E) — a tematika követelményeinek formalizálása

Ez a modul a *Kalkulus I. előadás* tantárgy tematikájának pontjait követi, és minden
ponthoz formális állítást rendel. Ahol az anyagot a Leindler-féle *Analízis* tankönyv
formalizálása már tartalmazza, ott az itteni tétel az ottani eredményre épül; ahol a
tematika a könyvön túlmutat (teljes indukció, nevezetes egyenlőtlenségek,
függvénytranszformációk, érintő, implicit deriválás), ott új tételek készültek.

A tematika pontjai:

1. A valós számok teste, teljességi (felső határ) axióma.
2. Teljes indukció.
3. Nevezetes egyenlőtlenségek (Bernoulli, számtani–mértani közép, Cauchy–Schwarz).
4. Elemi függvények és inverzeik.
5. Függvénytranszformációk.
6. Függvényhatárérték.
7. Folytonosság.
8. Kompakt intervallumon folytonos függvények (korlátosság, Weierstrass, Bolzano, Heine).
9. Pontbeli derivált, érintő.
10. Láncszabály, implicit deriválás.
11. Középértéktételek (Rolle, Lagrange, Cauchy).
12. Monotonitás és derivált.
13. Lokális szélsőérték: első és második derivált teszt.
14. Konvexitás és a második derivált; inflexió; grafikonvázolás.
15. L'Hospital-szabály.
16. Magasabbrendű deriváltak, Leibniz-formula, Taylor-formula, magasabbrendű
    szélsőérték-kritérium.
-/

namespace Tematika.KalkulusI

open Set Leindler Leindler.Ch05 Leindler.Ch06 Leindler.Ch08

/-! ## 1. A valós számok teste, teljességi axióma -/

/-- **1.** A valós számok rendezett test: a rendezés kompatibilis az összeadással és a
pozitív számmal való szorzással. -/
theorem rendezett_test (x y z : ℝ) (h : x < y) : x + z < y + z ∧ (0 < z → x * z < y * z) :=
  ⟨by linarith, fun hz => mul_lt_mul_of_pos_right h hz⟩

/-- **1.** *Teljességi (felső határ) axióma.* Minden nem üres, felülről korlátos valós
számhalmaznak van legkisebb felső korlátja. (Vö. Leindler 3. fejezet, 10. axióma.) -/
theorem felso_hatar_letezik {S : Set ℝ} (hne : S.Nonempty) (hb : BddAbove S) :
    ∃ K : ℝ, IsLUB S K :=
  ⟨sSup S, isLUB_csSup hne hb⟩

/-- **1.** Az arkhimédeszi tulajdonság: minden valós számnál van nagyobb természetes szám. -/
theorem arkhimedeszi (x : ℝ) : ∃ n : ℕ, x < n := exists_nat_gt x

/-! ## 2. Teljes indukció -/

/-- **2.** A teljes indukció elve. -/
theorem teljes_indukcio (P : ℕ → Prop) (h0 : P 0) (hs : ∀ n, P n → P (n + 1)) :
    ∀ n, P n := by
  intro n
  induction n with
  | zero => exact h0
  | succ k ih => exact hs k ih

/-- **2.** A teljes indukció alkalmazása: az első `n` pozitív egész összege. -/
theorem osszeg_elso_n (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), (k : ℝ) = n * (n + 1) / 2 := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    push_cast
    ring

/-! ## 3. Nevezetes egyenlőtlenségek -/

/-- **3.** *Bernoulli-egyenlőtlenség* (Leindler 4. fejezet). -/
theorem bernoulli_egyenlotlenseg {α : ℝ} (hα : -1 ≤ α) (n : ℕ) :
    1 + n * α ≤ (1 + α) ^ n :=
  Leindler.Ch04.bernoulli hα n

/-- **3.** *Számtani és mértani közép közti egyenlőtlenség* két nemnegatív számra. -/
theorem szamtani_mertani_kozep {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    Real.sqrt (a * b) ≤ (a + b) / 2 := by
  rw [show a * b = (Real.sqrt a * Real.sqrt b) ^ 2 by
    rw [mul_pow, Real.sq_sqrt ha, Real.sq_sqrt hb]]
  rw [Real.sqrt_sq (by positivity)]
  nlinarith [sq_nonneg (Real.sqrt a - Real.sqrt b), Real.sq_sqrt ha, Real.sq_sqrt hb]

/-- **3.** *Cauchy–Schwarz-egyenlőtlenség* véges összegekre. -/
theorem cauchy_schwarz (n : ℕ) (a b : Fin n → ℝ) :
    (∑ i, a i * b i) ^ 2 ≤ (∑ i, a i ^ 2) * (∑ i, b i ^ 2) :=
  Finset.sum_mul_sq_le_sq_mul_sq Finset.univ a b

/-- **3.** *Háromszög-egyenlőtlenség* a valós számok abszolút értékére. -/
theorem haromszog_egyenlotlenseg (x y : ℝ) : |x + y| ≤ |x| + |y| := abs_add_le x y

/-! ## 4. Elemi függvények és inverzeik -/

/-- **4.** Az exponenciális és a logaritmusfüggvény egymás inverzei. -/
theorem exp_log_inverz {x : ℝ} (hx : 0 < x) : Real.exp (Real.log x) = x :=
  Real.exp_log hx

/-- **4.** A logaritmus és az exponenciális függvény egymás inverzei. -/
theorem log_exp_inverz (x : ℝ) : Real.log (Real.exp x) = x := Real.log_exp x

/-- **4.** A szinusz és az arkusz szinusz a `[-1, 1]` intervallumon egymás inverzei. -/
theorem sin_arcsin_inverz {x : ℝ} (h₁ : -1 ≤ x) (h₂ : x ≤ 1) :
    Real.sin (Real.arcsin x) = x := Real.sin_arcsin h₁ h₂

/-- **4.** A tangens és az arkusz tangens egymás inverzei. -/
theorem tan_arctan_inverz (x : ℝ) : Real.tan (Real.arctan x) = x := Real.tan_arctan x

/-- **4.** Az exponenciális függvény szigorúan növekedő, tehát injektív. -/
theorem exp_szigoruan_novekedo : StrictMono Real.exp := Real.exp_strictMono

/-- **4.** Egy szigorúan monoton, folytonos függvénynek zárt intervallumon van folytonos
inverze (Leindler 5.6.1. Tétel). -/
theorem inverz_letezese {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Icc a b)) (hmono : StrictMonoOn f (Icc a b)) :
    f '' Icc a b = Icc (f a) (f b) ∧
      (∀ y ∈ Icc (f a) (f b), f (Function.invFunOn f (Icc a b) y) = y) ∧
      StrictMonoOn (Function.invFunOn f (Icc a b)) (Icc (f a) (f b)) ∧
      ContinuousOn (Function.invFunOn f (Icc a b)) (Icc (f a) (f b)) :=
  inverz_fuggveny hab hf hmono

/-! ## 5. Függvénytranszformációk -/

/-- **5.** *Vízszintes eltolás:* `x ↦ f(x - a)` deriváltja az `x₀` pontban `f'(x₀ - a)`. -/
theorem eltolas_derivalt {f : ℝ → ℝ} {x₀ a L : ℝ} (hd : Derivalt f (x₀ - a) L) :
    Derivalt (fun x => f (x - a)) x₀ L := by
  rw [derivalt_iff_hasDerivAt] at hd ⊢
  simpa using hd.comp x₀ ((hasDerivAt_id x₀).sub_const a)

/-- **5.** *Függőleges nyújtás:* `x ↦ c · f(x)` deriváltja `c · f'(x₀)`. -/
theorem nyujtas_derivalt {f : ℝ → ℝ} {x₀ c L : ℝ} (hd : Derivalt f x₀ L) :
    Derivalt (fun x => c * f x) x₀ (c * L) := by
  rw [derivalt_iff_hasDerivAt] at hd ⊢
  exact hd.const_mul c

/-- **5.** *Vízszintes nyújtás:* `x ↦ f(c · x)` deriváltja `c · f'(c · x₀)`. -/
theorem vizszintes_nyujtas_derivalt {f : ℝ → ℝ} {x₀ c L : ℝ} (hd : Derivalt f (c * x₀) L) :
    Derivalt (fun x => f (c * x)) x₀ (L * c) := by
  rw [derivalt_iff_hasDerivAt] at hd ⊢
  simpa using hd.comp x₀ ((hasDerivAt_id x₀).const_mul c)

/-- **5.** *Tükrözés:* páros függvény deriváltja páratlan. -/
theorem paros_fuggveny_derivaltja {f : ℝ → ℝ} {x₀ L : ℝ} (hp : ParosFv f)
    (hd : Derivalt f x₀ L) : Derivalt f (-x₀) (-L) := by
  rw [derivalt_iff_hasDerivAt] at hd ⊢
  have h0 : HasDerivAt (fun x : ℝ => -x) (-1 : ℝ) (-x₀) := by
    simpa using (hasDerivAt_id (-x₀)).neg
  have hd' : HasDerivAt f L (-(-x₀)) := by simpa using hd
  have hc := hd'.comp (-x₀) h0
  have hfe : (f ∘ fun x : ℝ => -x) = f := by
    funext x
    exact (hp x).symm
  rw [hfe] at hc
  simpa using hc

/-! ## 6–7. Függvényhatárérték és folytonosság -/

/-- **6.** A függvényhatárérték Heine- és Cauchy-féle definíciója ekvivalens
(Leindler 5.15. Tétel). -/
theorem hatarertek_heine_cauchy (f : ℝ → ℝ) (x₀ A : ℝ) :
    HeineHatarErtek f x₀ A ↔ CauchyHatarErtek f x₀ A :=
  heineHatarErtek_iff_cauchyHatarErtek f x₀ A

/-- **7.** A folytonosság Heine- és Cauchy-féle definíciója ekvivalens
(Leindler 5.2.3. Tétel). -/
theorem folytonossag_heine_cauchy (f : ℝ → ℝ) (x₀ : ℝ) :
    HeineFolytonos f x₀ ↔ CauchyFolytonos f x₀ :=
  heineFolytonos_iff_cauchyFolytonos f x₀

/-- **7.** A folytonosság megegyezik a Mathlib `ContinuousAt` fogalmával. -/
theorem folytonossag_continuousAt (f : ℝ → ℝ) (x₀ : ℝ) :
    CauchyFolytonos f x₀ ↔ ContinuousAt f x₀ :=
  cauchyFolytonos_iff_continuousAt f x₀

/-- **7.** Folytonos függvények összege, különbsége és szorzata folytonos. -/
theorem folytonossag_muveletek {f g : ℝ → ℝ} {x₀ : ℝ} (hf : CauchyFolytonos f x₀)
    (hg : CauchyFolytonos g x₀) :
    CauchyFolytonos (fun x => f x + g x) x₀ ∧ CauchyFolytonos (fun x => f x - g x) x₀ ∧
      CauchyFolytonos (fun x => f x * g x) x₀ := by
  have hf' := (heineFolytonos_iff_cauchyFolytonos f x₀).2 hf
  have hg' := (heineFolytonos_iff_cauchyFolytonos g x₀).2 hg
  exact ⟨(heineFolytonos_iff_cauchyFolytonos _ _).1 (folytonos_add hf' hg'),
    (heineFolytonos_iff_cauchyFolytonos _ _).1 (folytonos_sub hf' hg'),
    (heineFolytonos_iff_cauchyFolytonos _ _).1 (folytonos_mul hf' hg')⟩

/-! ## 8. Kompakt intervallumon folytonos függvények -/

/-- **8.** Zárt intervallumon folytonos függvény korlátos. -/
theorem kompaktan_korlatos {f : ℝ → ℝ} {a b : ℝ} (hf : FolytonosZarton f a b) :
    ∃ M : ℝ, ∀ x ∈ Icc a b, |f x| ≤ M :=
  zarton_folytonos_korlatos hf

/-- **8.** *Weierstrass tétele:* zárt intervallumon folytonos függvény felveszi a
maximumát és a minimumát. -/
theorem weierstrass {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hf : FolytonosZarton f a b) :
    (∃ x ∈ Icc a b, ∀ y ∈ Icc a b, f y ≤ f x) ∧
      ∃ x ∈ Icc a b, ∀ y ∈ Icc a b, f x ≤ f y :=
  zarton_folytonos_felveszi_szelsoertekeit hab hf

/-- **8.** *Bolzano-tétel (közbülső érték tétele).* -/
theorem bolzano {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b) (hf : FolytonosZarton f a b)
    {C : ℝ} (h₁ : f a ≤ C) (h₂ : C ≤ f b) : ∃ x ∈ Icc a b, f x = C :=
  kozbulso_ertek hab (folytonosZarton_continuousOn hf) ⟨h₁, h₂⟩

/-- **8.** *Heine tétele:* zárt intervallumon folytonos függvény egyenletesen folytonos. -/
theorem heine {f : ℝ → ℝ} {a b : ℝ} (hf : FolytonosZarton f a b) :
    EgyenletesenFolytonos f (Icc a b) :=
  zarton_folytonos_egyenletesen_folytonos hf

/-! ## 9. Pontbeli derivált, érintő -/

/-- **9.** A pontbeli derivált megegyezik a Mathlib `HasDerivAt` fogalmával. -/
theorem derivalt_hasDerivAt (f : ℝ → ℝ) (x₀ c : ℝ) :
    Derivalt f x₀ c ↔ HasDerivAt f c x₀ :=
  derivalt_iff_hasDerivAt f x₀ c

/-- **9.** *Az érintő jellemzése.* Ha `f`-nek az `x₀` pontban `L` a differenciálhányadosa,
akkor az `e(x) = f(x₀) + L·(x - x₀)` egyenes az `f` görbéjéhez *simuló* egyenes: az
`f(x) - e(x)` eltérés az `x - x₀`-nál magasabb rendben tűnik el, azaz
`(f(x) - e(x))/(x - x₀) → 0`, ha `x → x₀`. -/
theorem erinto_simulo_egyenes {f : ℝ → ℝ} {x₀ L : ℝ} (hd : Derivalt f x₀ L) :
    CauchyHatarErtek (fun x => (f x - (f x₀ + L * (x - x₀))) / (x - x₀)) x₀ 0 := by
  intro ε hε
  obtain ⟨δ, hδ, hp⟩ := hd ε hε
  refine ⟨δ, hδ, fun x hx hxd => ?_⟩
  have h := hp x hx hxd
  have hne : x - x₀ ≠ 0 := sub_ne_zero.2 hx
  have heq : (f x - (f x₀ + L * (x - x₀))) / (x - x₀) = kulonbsegiHanyados f x₀ x - L := by
    rw [kulonbsegiHanyados]
    field_simp
    ring
  show |(f x - (f x₀ + L * (x - x₀))) / (x - x₀) - 0| < ε
  rw [heq, sub_zero]
  exact h

/-- **9.** Differenciálhatóságból következik a folytonosság. -/
theorem derivalhato_folytonos {f : ℝ → ℝ} {x₀ L : ℝ} (hd : Derivalt f x₀ L) :
    CauchyFolytonos f x₀ :=
  differencialhato_folytonos hd

/-! ## 10. Láncszabály, implicit deriválás -/

/-- **10.** *Láncszabály* (Leindler 6.4). -/
theorem lancszabaly {f g : ℝ → ℝ} {x₀ c d : ℝ} (hg : Derivalt g x₀ d)
    (hf : Derivalt f (g x₀) c) : Derivalt (fun x => f (g x)) x₀ (c * d) :=
  derivalt_osszetett hg hf

/-- **10.** *Implicit deriválás.* Ha az `y = y(x)` differenciálható függvény kielégíti az
`x² + y(x)² = r²` körre vonatkozó implicit egyenletet, akkor `y'(x₀) = -x₀ / y(x₀)`
minden olyan `x₀` pontban, ahol `y(x₀) ≠ 0`.

*Bizonyítás.* Az egyenlet mindkét oldalát deriválva `2x₀ + 2 y(x₀) y'(x₀) = 0`. -/
theorem implicit_derivalas_kor {y : ℝ → ℝ} {r x₀ L : ℝ}
    (hy : ∀ x, x ^ 2 + y x ^ 2 = r ^ 2) (hd : Derivalt y x₀ L) (hne : y x₀ ≠ 0) :
    L = -x₀ / y x₀ := by
  have h1 : HasDerivAt y L x₀ := (derivalt_iff_hasDerivAt _ _ _).1 hd
  have ha : HasDerivAt (fun x : ℝ => x ^ 2) (2 * x₀) x₀ := by
    simpa using hasDerivAt_pow 2 x₀
  have hb : HasDerivAt (fun x : ℝ => y x ^ 2) (2 * y x₀ * L) x₀ := by
    simpa [mul_comm, mul_assoc, mul_left_comm] using h1.pow 2
  have h2 : HasDerivAt (fun x : ℝ => x ^ 2 + y x ^ 2) (2 * x₀ + 2 * y x₀ * L) x₀ := ha.add hb
  have heq : (fun x : ℝ => x ^ 2 + y x ^ 2) = fun _ => r ^ 2 := funext hy
  rw [heq] at h2
  have h4 : 2 * x₀ + 2 * y x₀ * L = 0 := h2.unique (hasDerivAt_const x₀ (r ^ 2))
  rw [eq_div_iff hne]
  linear_combination h4 / 2

/-! ## 11. Középértéktételek -/

/-- **11.** *Rolle tétele* (Leindler 6.10.3). -/
theorem rolle_tetel {f : ℝ → ℝ} {a b : ℝ} (hab : a < b) (hcont : ContinuousOn f (Icc a b))
    (hderiv : ∀ x ∈ Ioo a b, ∃ L, Derivalt f x L) (hfab : f a = f b) :
    ∃ c ∈ Ioo a b, Derivalt f c 0 :=
  rolle hab hcont hderiv hfab

/-- **11.** *Lagrange-féle középértéktétel* (Leindler 6.10.4). -/
theorem lagrange_tetel {f : ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (hcont : ContinuousOn f (Icc a b)) (hderiv : ∀ x ∈ Ioo a b, ∃ L, Derivalt f x L) :
    ∃ c ∈ Ioo a b, Derivalt f c ((f b - f a) / (b - a)) :=
  lagrange hab hcont hderiv

/-! ## 12. Monotonitás és derivált -/

/-- **12.** Ha `f' ≥ 0` az `(a, b)`-n, akkor `f` növekedő `[a, b]`-n. -/
theorem monotonitas_derivalttal {f f' : ℝ → ℝ} {a b : ℝ}
    (hcont : ContinuousOn f (Icc a b)) (hd : ∀ x ∈ Ioo a b, Derivalt f x (f' x))
    (hpos : ∀ x ∈ Ioo a b, 0 ≤ f' x) :
    ∀ x₁ ∈ Icc a b, ∀ x₂ ∈ Icc a b, x₁ < x₂ → f x₁ ≤ f x₂ :=
  novekedo_ha_derivalt_nemnegativ hcont hd hpos

/-- **12.** Ha `f' > 0` az `(a, b)`-n, akkor `f` szigorúan növekedő `[a, b]`-n. -/
theorem szigoru_monotonitas_derivalttal {f f' : ℝ → ℝ} {a b : ℝ}
    (hcont : ContinuousOn f (Icc a b)) (hd : ∀ x ∈ Ioo a b, Derivalt f x (f' x))
    (hpos : ∀ x ∈ Ioo a b, 0 < f' x) :
    ∀ x₁ ∈ Icc a b, ∀ x₂ ∈ Icc a b, x₁ < x₂ → f x₁ < f x₂ :=
  szigoruan_novekedo_ha_derivalt_pozitiv hcont hd hpos

/-! ## 13. Lokális szélsőérték: első és második derivált teszt -/

/-- **13.** *Szükséges feltétel:* belső szélsőértékhelyen a derivált nulla
(Fermat-tétel, Leindler 6.10.2). -/
theorem elsorendu_szukseges_feltetel {f : ℝ → ℝ} {c L δ : ℝ} (hδ : 0 < δ)
    (hmax : ∀ x, |x - c| < δ → f x ≤ f c) (hd : Derivalt f c L) : L = 0 :=
  belso_szelsoertek_derivalt_nulla hδ hmax hd

/-- **13.** *Első derivált teszt:* ha `f'` az `x₀`-nál pozitívból negatívba vált, akkor
`x₀`-ban szigorú helyi maximum van (Leindler 8.4.1). -/
theorem elso_derivalt_teszt {f f' : ℝ → ℝ} {x₀ δ : ℝ}
    (hd : ∀ x, |x - x₀| < δ → Derivalt f x (f' x))
    (hbal : ∀ x, |x - x₀| < δ → x < x₀ → 0 < f' x)
    (hjobb : ∀ x, |x - x₀| < δ → x₀ < x → f' x < 0) :
    ∀ x, |x - x₀| < δ → x ≠ x₀ → f x < f x₀ :=
  szigoru_maximum_ha_derivalt_jelet_valt hd hbal hjobb

/-- **13.** *Második derivált teszt:* ha `f'(x₀) = 0` és `f''(x₀) > 0`, akkor `x₀`-ban
szigorú helyi minimum van (Leindler 8.5.1). -/
theorem masodik_derivalt_teszt {f f' : ℝ → ℝ} {x₀ M δ : ℝ} (hδ : 0 < δ)
    (hd : ∀ x, |x - x₀| < δ → Derivalt f x (f' x)) (h1 : f' x₀ = 0)
    (h2 : Derivalt f' x₀ M) (hM : 0 < M) :
    ∃ δ' > 0, ∀ x, |x - x₀| < δ' → x ≠ x₀ → f x₀ < f x :=
  szigoru_minimum_masodik_derivalttal hδ hd h1 h2 hM

/-! ## 13/b. Intervallumon vett (abszolút) szélsőértékek -/

/-- **13/b.** *Intervallumon vett szélsőérték.* Az `[a, b]` zárt intervallumon folytonos,
az `(a, b)` belső pontjaiban differenciálható `f` függvény felveszi a maximumát, és a
maximumhely vagy az intervallum valamelyik végpontja, vagy olyan belső pont, ahol a
derivált eltűnik.

*Bizonyítás.* A Weierstrass-tétel szerint van maximumhely `c ∈ [a, b]`. Ha `c` belső
pont, akkor a `c` egy egész környezetében `f x ≤ f c`, tehát a Fermat-tétel
(Leindler 6.10.2) szerint `f'(c) = 0`. -/
theorem intervallumon_vett_maximum {f f' : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn f (Icc a b)) (hd : ∀ x ∈ Ioo a b, Derivalt f x (f' x)) :
    ∃ c ∈ Icc a b, (∀ x ∈ Icc a b, f x ≤ f c) ∧ (c = a ∨ c = b ∨ f' c = 0) := by
  obtain ⟨c, hc, hmax⟩ := isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.2 hab) hcont
  refine ⟨c, hc, fun x hx => hmax hx, ?_⟩
  rcases eq_or_lt_of_le hc.1 with h | h
  · exact Or.inl h.symm
  rcases eq_or_lt_of_le hc.2 with h2 | h2
  · exact Or.inr (Or.inl h2)
  refine Or.inr (Or.inr ?_)
  have hd0 : 0 < min (c - a) (b - c) := lt_min (by linarith) (by linarith)
  refine belso_szelsoertek_derivalt_nulla hd0 ?_ (hd c ⟨h, h2⟩)
  intro x hx
  have hx' := abs_lt.mp hx
  have h1 : a ≤ x := by
    have := hx'.1
    have hmin : min (c - a) (b - c) ≤ c - a := min_le_left _ _
    linarith
  have h2' : x ≤ b := by
    have := hx'.2
    have hmin : min (c - a) (b - c) ≤ b - c := min_le_right _ _
    linarith
  exact hmax ⟨h1, h2'⟩

/-! ## 14. Konvexitás, inflexió, grafikonvázolás -/

/-- **14.** *Konvexitás és a második derivált* (Leindler 8.6.1). -/
theorem konvexitas_masodik_derivalttal {f f' f'' : ℝ → ℝ} {a b : ℝ}
    (hd : ∀ x ∈ Ioo a b, Derivalt f x (f' x))
    (hd2 : ∀ x ∈ Ioo a b, Derivalt f' x (f'' x)) :
    KonvexGorbe f (Ioo a b) ↔ ∀ x ∈ Ioo a b, 0 ≤ f'' x :=
  konvex_iff_masodik_derivalt_nemnegativ hd hd2

/-- **14.** *Inflexiós pont szükséges feltétele* (Leindler 8.7.1). -/
theorem inflexio_szukseges {f f' f'' : ℝ → ℝ} {x₀ δ₀ : ℝ} (hδ₀ : 0 < δ₀)
    (hd : ∀ x, |x - x₀| < δ₀ → Derivalt f x (f' x))
    (hd2 : ∀ x, |x - x₀| < δ₀ → Derivalt f' x (f'' x))
    (hinf : InflexiosPont f x₀) : f'' x₀ = 0 :=
  inflexios_pont_masodik_derivalt_nulla hδ₀ hd hd2 hinf

/-- **14.** *Inflexiós pont elegendő feltétele* (Leindler 8.7.2). -/
theorem inflexio_elegendo {f f' f'' : ℝ → ℝ} {x₀ δ₀ M : ℝ} (hδ₀ : 0 < δ₀)
    (hd : ∀ x, |x - x₀| < δ₀ → Derivalt f x (f' x))
    (hd2 : ∀ x, |x - x₀| < δ₀ → Derivalt f' x (f'' x))
    (h2 : f'' x₀ = 0) (h3 : Derivalt f'' x₀ M) (hM : M ≠ 0) :
    InflexiosPont f x₀ :=
  inflexios_pont_ha_harmadik_derivalt_nem_nulla hδ₀ hd hd2 h2 h3 hM

/-- **14.** *Grafikonvázolás — mintapélda:* az `x ↦ x³` függvénynek a `0` pontban
inflexiós pontja van. -/
theorem grafikon_pelda : InflexiosPont (fun x : ℝ => x ^ 3) 0 :=
  pelda_kobfuggveny_inflexio

/-! ## 15. L'Hospital-szabály -/

/-- **15.** *L'Hospital-szabály* kétoldali, `0/0` alakú határozatlan kifejezésre
(Leindler 6.11). -/
theorem lhospital {f g f' g' : ℝ → ℝ} {a L : ℝ}
    (hf : ∀ᶠ x in nhds a, HasDerivAt f (f' x) x)
    (hg : ∀ᶠ x in nhds a, HasDerivAt g (g' x) x)
    (hg0 : ∀ᶠ x in nhds a, g' x ≠ 0)
    (hfa : Filter.Tendsto f (nhds a) (nhds 0))
    (hga : Filter.Tendsto g (nhds a) (nhds 0))
    (hlim : Filter.Tendsto (fun x => f' x / g' x) (nhds a) (nhds L)) :
    CauchyHatarErtek (fun x => f x / g x) a L :=
  lhospital_hatarertek hf hg hg0 hfa hga hlim

/-! ## 16. Magasabbrendű deriváltak, Taylor-formula -/

/-- **16.** *Leibniz-formula* a szorzat `n`-edik deriváltjára (7.1.1. Tétel). -/
theorem leibniz_formula {f g : ℝ → ℝ} {n : ℕ} {s : Set ℝ} (hs : IsOpen s)
    (hf : Leindler.Ch07.NszerDifferencialhato f n s)
    (hg : Leindler.Ch07.NszerDifferencialhato g n s) :
    (∀ x ∈ s, Leindler.Ch07.nDerivalt n (fun y => f y * g y) x
        = ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) *
            Leindler.Ch07.nDerivalt (n - k) f x * Leindler.Ch07.nDerivalt k g x) ∧
      Leindler.Ch07.NszerDifferencialhato (fun y => f y * g y) n s :=
  Leindler.Ch07.leibniz_formula hs hf hg

/-- **16.** *Taylor-formula* Lagrange-féle maradéktaggal (7.2.1. Tétel). -/
theorem taylor_formula {f : ℝ → ℝ} {c d : ℝ} {n : ℕ} (hn : 0 < n)
    (hf : Leindler.Ch07.NszerDifferencialhato f n (Ioo c d)) {a x : ℝ} (ha : a ∈ Ioo c d)
    (hx : x ∈ Ioo c d) :
    ∃ theta ∈ Ioo (0 : ℝ) 1,
      f x = Leindler.Ch07.taylorPolinom f n a x
        + Leindler.Ch07.lagrangeMaradektag f n a x theta :=
  Leindler.Ch07.taylor_formula hn hf ha hx

/-- **16.** Magasabbrendű szélsőérték-kritérium: ha az első el nem tűnő derivált páros
rendű és pozitív, akkor szigorú lokális minimum van (8.5.2. Tétel). -/
theorem magasabbrendu_minimum {f : ℝ → ℝ} {c d x₀ : ℝ} {k : ℕ} (hk : 0 < k)
    (hf : Leindler.Ch07.NszerDifferencialhato f (2 * k) (Ioo c d)) (hx₀ : x₀ ∈ Ioo c d)
    (hzero : ∀ i, 1 ≤ i → i < 2 * k → Leindler.Ch07.nDerivalt i f x₀ = 0)
    (hpos : 0 < Leindler.Ch07.nDerivalt (2 * k) f x₀) :
    ∃ δ > 0, ∀ x, |x - x₀| < δ → x ≠ x₀ → f x₀ < f x :=
  Leindler.Ch07.szelsoertek_paros_rendu_minimum hk hf hx₀ hzero hpos

end Tematika.KalkulusI
