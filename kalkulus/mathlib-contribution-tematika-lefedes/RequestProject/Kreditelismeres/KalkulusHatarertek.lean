/-
# Kalkulus I — kreditelismerési bizonyítéktár, 1. rész

Ez a fájl a `kalkulus-tetelsor-2025.pdf` **1–11. tételéhez** tartozó
állításokat formalizálja Lean 4-ben.

A cél az, hogy a kreditelismerési kérelemben minden tételsor-pontnál
hivatkozható legyen egy gépileg ellenőrzött állítás.  A határérték- és
folytonosságelméletet **saját ε–δ definícióból** építjük fel (nem a Mathlib
szűrős apparátusát használjuk), így a bizonyítások valóban a tárgy
bizonyításait követik; a `limitAt_iff_tendsto` lemma köti össze a saját
fogalmat a Mathlib `Filter.Tendsto` fogalmával.

Fedett tételsor-pontok:
* 1. szuprémum, teljességi axióma, √2 irracionalitása, ℚ sűrűsége;
* 2. Cauchy–Schwarz- és Bernoulli-egyenlőtlenség;
* 3. függvénytulajdonságok (monotonitás, korlátosság, szimmetria, bijektivitás);
* 4–5. hatvány-, exponenciális, logaritmus- és arkuszfüggvények;
* 6. határérték, féloldali határérték, a határérték egyértelműsége;
* 7. műveletek határértékekkel, összetett függvény határértéke;
* 8. határérték és egyenlőtlenségek (rendőrelv);
* 9. folytonosság, összetett függvény folytonossága;
* 10. az `e` szám: monoton korlátos függvény/sorozat határértéke;
* 11. Bolzano–Darboux-tétel, kompakt intervallumon folytonos függvények.
-/
import Mathlib
import RequestProject.Portfolio.Kalkulus

namespace SZTE.Kredit.Kalkulus

open Filter Topology Finset

/-! ## 1. tétel — Korlátosság, szuprémum, teljességi axióma, ℚ és irracionális számok -/

/-- **Teljességi axióma.** Nemüres, felülről korlátos valós számhalmaznak van
legkisebb felső korlátja. -/
theorem exists_isLUB_of_bddAbove {S : Set ℝ} (hne : S.Nonempty) (hb : BddAbove S) :
    ∃ a : ℝ, IsLUB S a := by
  exact Real.exists_isLUB hne hb

/-- **A felső határ egyértelmű** (1.5. gyakorlat). -/
theorem isLUB_unique {S : Set ℝ} {a b : ℝ} (ha : IsLUB S a) (hb : IsLUB S b) : a = b := by
  exact ha.unique hb

/-- **√2 irracionális** (1.9. gyakorlat). -/
theorem irrational_sqrt_two' : Irrational (Real.sqrt 2) := by
  exact irrational_sqrt_two

/-- **A racionális számok sűrűn helyezkednek el a valós számok között.** -/
theorem rat_dense (x y : ℝ) (h : x < y) : ∃ q : ℚ, x < (q : ℝ) ∧ (q : ℝ) < y := by
  exact exists_rat_btwn h

/-- **Az irracionális számok is sűrűn helyezkednek el.** -/
theorem irrational_dense (x y : ℝ) (h : x < y) : ∃ z : ℝ, Irrational z ∧ x < z ∧ z < y := by
  obtain ⟨q, hq1, hq2⟩ := exists_rat_btwn (show x - Real.sqrt 2 < y - Real.sqrt 2 by linarith)
  refine ⟨(q : ℝ) + Real.sqrt 2, ?_, by linarith, by linarith⟩
  rw [add_comm]
  exact irrational_sqrt_two.add_ratCast q

/-! ## 2. tétel — Nevezetes egyenlőtlenségek -/

/-- **Cauchy–Schwarz-egyenlőtlenség** véges összegekre. -/
theorem cauchy_schwarz_sum (n : ℕ) (a b : ℕ → ℝ) :
    (∑ i ∈ range n, a i * b i) ^ 2 ≤
      (∑ i ∈ range n, (a i) ^ 2) * (∑ i ∈ range n, (b i) ^ 2) := by
  exact sum_mul_sq_le_sq_mul_sq (range n) a b

/-- **Bernoulli-egyenlőtlenség.** -/
theorem bernoulli_ineq (x : ℝ) (hx : -1 ≤ x) (n : ℕ) : 1 + n * x ≤ (1 + x) ^ n := by
  exact one_add_mul_le_pow (by linarith) n

/-- **Számtani és mértani közép közötti egyenlőtlenség** két tagra. -/
theorem am_gm_two (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) : Real.sqrt (a * b) ≤ (a + b) / 2 := by
  have h : Real.sqrt (a * b) ^ 2 ≤ ((a + b) / 2) ^ 2 := by
    rw [Real.sq_sqrt (by positivity)]
    nlinarith [sq_nonneg (a - b)]
  nlinarith [Real.sqrt_nonneg (a * b), (by linarith : (0 : ℝ) ≤ (a + b) / 2)]

/-! ## 3. tétel — Függvények alapvető tulajdonságai (példák) -/

/-- Az `x ↦ x³` függvény szigorúan monoton növő, tehát injektív. -/
theorem strictMono_cube' : StrictMono (fun x : ℝ => x ^ 3) := by
  exact Odd.strictMono_pow (R := ℝ) (by norm_num)

/-- Az `x ↦ x³` bijekció `ℝ → ℝ`. -/
theorem bijective_cube : Function.Bijective (fun x : ℝ => x ^ 3) := by
  refine ⟨(Odd.strictMono_pow (R := ℝ) (by norm_num)).injective, ?_⟩
  apply Continuous.surjective (by fun_prop)
  · exact tendsto_pow_atTop (by norm_num)
  · have h : Tendsto (fun x : ℝ => -((-x) ^ 3)) atBot atBot :=
      tendsto_neg_atTop_atBot.comp
        ((tendsto_pow_atTop (α := ℝ) (n := 3) (by norm_num)).comp tendsto_neg_atBot_atTop)
    exact h.congr (fun x => by ring)

/-- Páros és páratlan függvény: `cos` páros, `sin` páratlan. -/
theorem cos_even_sin_odd :
    (∀ x : ℝ, Real.cos (-x) = Real.cos x) ∧ (∀ x : ℝ, Real.sin (-x) = -Real.sin x) := by
  exact ⟨fun x => Real.cos_neg x, fun x => Real.sin_neg x⟩

/-- Minden valós függvény egyértelműen bomlik páros és páratlan függvény összegére. -/
theorem exists_unique_even_odd_decomp (f : ℝ → ℝ) :
    ∃! p : (ℝ → ℝ) × (ℝ → ℝ),
      (∀ x, p.1 (-x) = p.1 x) ∧ (∀ x, p.2 (-x) = -p.2 x) ∧ (∀ x, f x = p.1 x + p.2 x) := by
  refine ⟨⟨fun x => (f x + f (-x)) / 2, fun x => (f x - f (-x)) / 2⟩, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro x; simp only [neg_neg]; ring
  · intro x; simp only [neg_neg]; ring
  · intro x; ring
  · rintro ⟨g, h⟩ ⟨hg, hh, hgh⟩
    simp only at hg hh hgh
    have key : ∀ x, g x = (f x + f (-x)) / 2 := by
      intro x
      have h2 := hgh (-x)
      rw [hg x, hh x] at h2
      linarith [hgh x]
    have key2 : ∀ x, h x = (f x - f (-x)) / 2 := by
      intro x
      have := key x
      linarith [hgh x]
    exact Prod.ext (funext key) (funext key2)

/-! ## 4–5. tétel — Hatvány-, exponenciális, logaritmus- és arkuszfüggvények -/

/-- Az exponenciális függvény szigorúan monoton növő. -/
theorem exp_strictMono' : StrictMono Real.exp := by
  exact Real.exp_strictMono

/-- A logaritmus az exponenciális függvény inverze a pozitív félegyenesen. -/
theorem log_exp_inverse :
    (∀ x : ℝ, Real.log (Real.exp x) = x) ∧ (∀ y : ℝ, 0 < y → Real.exp (Real.log y) = y) := by
  exact ⟨fun x => Real.log_exp x, fun y hy => Real.exp_log hy⟩

/-- A logaritmus függvényegyenlete. -/
theorem log_mul_eq {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    Real.log (x * y) = Real.log x + Real.log y := by
  exact Real.log_mul (ne_of_gt hx) (ne_of_gt hy)

/-- Az `arcsin` a `sin` inverze a `[-π/2, π/2]` intervallumon. -/
theorem arcsin_left_inverse {x : ℝ} (h₁ : -(Real.pi / 2) ≤ x) (h₂ : x ≤ Real.pi / 2) :
    Real.arcsin (Real.sin x) = x := by
  exact Real.arcsin_sin h₁ h₂

/-! ## 6. tétel — Határérték: definíció és egyértelműség -/

/-- **A határérték ε–δ definíciója:** `lim_{x→a} f(x) = L`. -/
def LimitAt (f : ℝ → ℝ) (a L : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x : ℝ, 0 < |x - a| → |x - a| < δ → |f x - L| < ε

/-- **Jobb oldali határérték.** -/
def RightLimitAt (f : ℝ → ℝ) (a L : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x : ℝ, a < x → x - a < δ → |f x - L| < ε

/-- **Bal oldali határérték.** -/
def LeftLimitAt (f : ℝ → ℝ) (a L : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x : ℝ, x < a → a - x < δ → |f x - L| < ε

/-- **A határérték egyértelmű** (6. tétel bizonyítása). -/
theorem limitAt_unique {f : ℝ → ℝ} {a L M : ℝ} (hL : LimitAt f a L) (hM : LimitAt f a M) :
    L = M := by
  by_contra hne
  have hpos : 0 < |L - M| / 2 := by
    have : L - M ≠ 0 := sub_ne_zero.mpr hne
    positivity
  obtain ⟨δ₁, hδ₁, H₁⟩ := hL _ hpos
  obtain ⟨δ₂, hδ₂, H₂⟩ := hM _ hpos
  set d := min δ₁ δ₂ / 2 with hd
  have hdpos : 0 < d := by positivity
  have h1 : |a + d - a| = d := by simp [abs_of_pos hdpos]
  have hlt1 : |a + d - a| < δ₁ := by
    rw [h1]
    have h : min δ₁ δ₂ ≤ δ₁ := min_le_left _ _
    simp only [hd]; linarith
  have hlt2 : |a + d - a| < δ₂ := by
    rw [h1]
    have h : min δ₁ δ₂ ≤ δ₂ := min_le_right _ _
    simp only [hd]; linarith
  have e1 := H₁ (a + d) (by rw [h1]; exact hdpos) hlt1
  have e2 := H₂ (a + d) (by rw [h1]; exact hdpos) hlt2
  have htri : |L - M| ≤ |f (a + d) - L| + |f (a + d) - M| :=
    calc |L - M| = |(f (a + d) - M) - (f (a + d) - L)| := by ring_nf
      _ ≤ |f (a + d) - M| + |f (a + d) - L| := abs_sub _ _
      _ = |f (a + d) - L| + |f (a + d) - M| := by ring
  linarith

/-- A saját ε–δ határérték egybeesik a Mathlib szűrős határértékével. -/
theorem limitAt_iff_tendsto {f : ℝ → ℝ} {a L : ℝ} :
    LimitAt f a L ↔ Tendsto f (nhdsWithin a {a}ᶜ) (nhds L) := by
  rw [Metric.tendsto_nhdsWithin_nhds]
  constructor
  · intro h ε hε
    obtain ⟨δ, hδ, H⟩ := h ε hε
    refine ⟨δ, hδ, fun {x} hx hd => ?_⟩
    have hx' : x ≠ a := hx
    rw [Real.dist_eq] at hd ⊢
    exact H x (by simpa [sub_eq_zero] using abs_pos.mpr (sub_ne_zero.mpr hx')) hd
  · intro h ε hε
    obtain ⟨δ, hδ, H⟩ := h ε hε
    refine ⟨δ, hδ, fun x hx hd => ?_⟩
    have hx' : x ≠ a := by
      intro hxa; rw [hxa] at hx; simp at hx
    have := H (x := x) hx' (by rwa [Real.dist_eq])
    rwa [Real.dist_eq] at this

/-- **A határérték pontosan akkor létezik, ha a két féloldali határérték létezik és egyenlő.** -/
theorem limitAt_iff_left_right {f : ℝ → ℝ} {a L : ℝ} :
    LimitAt f a L ↔ (LeftLimitAt f a L ∧ RightLimitAt f a L) := by
  constructor
  · intro h
    refine ⟨fun ε hε => ?_, fun ε hε => ?_⟩
    · obtain ⟨δ, hδ, H⟩ := h ε hε
      refine ⟨δ, hδ, fun x hxa hd => H x ?_ ?_⟩
      · rw [abs_of_neg (by linarith)]; linarith
      · rw [abs_of_neg (by linarith)]; linarith
    · obtain ⟨δ, hδ, H⟩ := h ε hε
      refine ⟨δ, hδ, fun x hxa hd => H x ?_ ?_⟩
      · rw [abs_of_pos (by linarith)]; linarith
      · rw [abs_of_pos (by linarith)]; linarith
  · rintro ⟨hl, hr⟩ ε hε
    obtain ⟨δ₁, hδ₁, H₁⟩ := hl ε hε
    obtain ⟨δ₂, hδ₂, H₂⟩ := hr ε hε
    refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun x hx hd => ?_⟩
    rcases lt_trichotomy x a with h | h | h
    · refine H₁ x h ?_
      have heq : |x - a| = a - x := by rw [abs_of_neg (by linarith)]; ring
      rw [← heq]; exact lt_of_lt_of_le hd (min_le_left _ _)
    · exfalso; rw [h] at hx; simp at hx
    · refine H₂ x h ?_
      have heq : |x - a| = x - a := abs_of_pos (by linarith)
      rw [← heq]; exact lt_of_lt_of_le hd (min_le_right _ _)

/-! ## 7. tétel — Műveletek határértékekkel -/

theorem limitAt_const (a c : ℝ) : LimitAt (fun _ => c) a c := by
  intro ε hε
  exact ⟨1, one_pos, fun x _ _ => by simpa using hε⟩

theorem limitAt_id (a : ℝ) : LimitAt (fun x => x) a a := by
  intro ε hε
  exact ⟨ε, hε, fun x _ h => h⟩

/-- **Összeg határértéke.** -/
theorem limitAt_add {f g : ℝ → ℝ} {a L M : ℝ} (hf : LimitAt f a L) (hg : LimitAt g a M) :
    LimitAt (fun x => f x + g x) a (L + M) := by
  intro ε hε
  obtain ⟨δ₁, hδ₁, H₁⟩ := hf (ε / 2) (by linarith)
  obtain ⟨δ₂, hδ₂, H₂⟩ := hg (ε / 2) (by linarith)
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun x hx hd => ?_⟩
  have e1 := H₁ x hx (lt_of_lt_of_le hd (min_le_left _ _))
  have e2 := H₂ x hx (lt_of_lt_of_le hd (min_le_right _ _))
  calc |f x + g x - (L + M)| = |(f x - L) + (g x - M)| := by ring_nf
    _ ≤ |f x - L| + |g x - M| := abs_add_le _ _
    _ < ε := by linarith

/-- **Szorzat határértéke** (a 7. tétel bizonyítandó állítása). -/
theorem limitAt_mul {f g : ℝ → ℝ} {a L M : ℝ} (hf : LimitAt f a L) (hg : LimitAt g a M) :
    LimitAt (fun x => f x * g x) a (L * M) := by
  intro ε hε
  set C : ℝ := |L| + |M| + 1 with hC
  have hCpos : 0 < C := by positivity
  obtain ⟨δ₁, hδ₁, H₁⟩ := hf (min 1 (ε / C) / 2) (by positivity)
  obtain ⟨δ₂, hδ₂, H₂⟩ := hg (min 1 (ε / C) / 2) (by positivity)
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun x hx hd => ?_⟩
  have e1 := H₁ x hx (lt_of_lt_of_le hd (min_le_left _ _))
  have e2 := H₂ x hx (lt_of_lt_of_le hd (min_le_right _ _))
  set u := f x - L with hu
  set v := g x - M with hv
  have hume : |u| ≤ 1 := le_of_lt (lt_of_lt_of_le e1 (by
    have h : min 1 (ε / C) ≤ 1 := min_le_left _ _; linarith))
  have key : f x * g x - L * M = u * v + u * M + L * v := by
    simp only [hu, hv]; ring
  have h1 : |u * v + u * M + L * v| ≤ |u| * |v| + |u| * |M| + |L| * |v| :=
    calc |u * v + u * M + L * v| ≤ |u * v + u * M| + |L * v| := abs_add_le _ _
      _ ≤ (|u * v| + |u * M|) + |L * v| := by gcongr; exact abs_add_le _ _
      _ = |u| * |v| + |u| * |M| + |L| * |v| := by simp [abs_mul]
  have hmc : min 1 (ε / C) ≤ ε / C := min_le_right _ _
  have hvb : |v| < ε / C / 2 := lt_of_lt_of_le e2 (by linarith)
  have hub : |u| < ε / C / 2 := lt_of_lt_of_le e1 (by linarith)
  have hCe : ε / C * C = ε := by field_simp
  have habs : |u| * |v| + |u| * |M| + |L| * |v| < ε := by
    have h2 : |u| * |v| ≤ |v| := by nlinarith [abs_nonneg v, abs_nonneg u]
    nlinarith [abs_nonneg L, abs_nonneg M, hCpos, hvb, hub]
  rw [key]
  exact lt_of_le_of_lt h1 habs

/-- **Hányados határértéke** nem nulla nevező esetén. -/
theorem limitAt_div {f g : ℝ → ℝ} {a L M : ℝ} (hf : LimitAt f a L) (hg : LimitAt g a M)
    (hM : M ≠ 0) : LimitAt (fun x => f x / g x) a (L / M) := by
  rw [limitAt_iff_tendsto] at hf hg ⊢
  exact hf.div hg hM

/-! ## 8. tétel — Határérték és egyenlőtlenségek -/

/-- Ha `f ≤ g` egy pontozott környezetben, akkor a határértékekre is `L ≤ M`. -/
theorem limitAt_le_of_le {f g : ℝ → ℝ} {a L M : ℝ} (hf : LimitAt f a L) (hg : LimitAt g a M)
    (h : ∃ r > 0, ∀ x, 0 < |x - a| → |x - a| < r → f x ≤ g x) : L ≤ M := by
  obtain ⟨r, hr, hfg⟩ := h
  by_contra hlt
  push_neg at hlt
  set ε := (L - M) / 2 with hε
  have hεpos : 0 < ε := by simp only [hε]; linarith
  obtain ⟨δ₁, hδ₁, H₁⟩ := hf ε hεpos
  obtain ⟨δ₂, hδ₂, H₂⟩ := hg ε hεpos
  set d := min r (min δ₁ δ₂) / 2 with hd
  have hmin : 0 < min r (min δ₁ δ₂) := lt_min hr (lt_min hδ₁ hδ₂)
  have hdpos : 0 < d := by simp only [hd]; linarith
  have hx : |a + d - a| = d := by simp [abs_of_pos hdpos]
  have hd1 : d < δ₁ := by
    have h1 : min r (min δ₁ δ₂) ≤ min δ₁ δ₂ := min_le_right _ _
    have h2 : min δ₁ δ₂ ≤ δ₁ := min_le_left _ _
    simp only [hd]; linarith
  have hd2 : d < δ₂ := by
    have h1 : min r (min δ₁ δ₂) ≤ min δ₁ δ₂ := min_le_right _ _
    have h2 : min δ₁ δ₂ ≤ δ₂ := min_le_right _ _
    simp only [hd]; linarith
  have hdr : d < r := by
    have h1 : min r (min δ₁ δ₂) ≤ r := min_le_left _ _
    simp only [hd]; linarith
  have e1 := H₁ (a + d) (by rw [hx]; exact hdpos) (by rw [hx]; exact hd1)
  have e2 := H₂ (a + d) (by rw [hx]; exact hdpos) (by rw [hx]; exact hd2)
  have e3 := hfg (a + d) (by rw [hx]; exact hdpos) (by rw [hx]; exact hdr)
  have b1 : L - ε < f (a + d) := by have := abs_lt.mp e1; linarith [this.1]
  have b2 : g (a + d) < M + ε := by have := abs_lt.mp e2; linarith [this.2]
  simp only [hε] at b1 b2
  linarith

/-- **Rendőrelv (közrefogási elv).** -/
theorem limitAt_squeeze {f g h : ℝ → ℝ} {a L : ℝ} (hf : LimitAt f a L) (hh : LimitAt h a L)
    (hfg : ∃ r > 0, ∀ x, 0 < |x - a| → |x - a| < r → f x ≤ g x ∧ g x ≤ h x) :
    LimitAt g a L := by
  obtain ⟨r, hr, hb⟩ := hfg
  intro ε hε
  obtain ⟨δ₁, hδ₁, H₁⟩ := hf ε hε
  obtain ⟨δ₂, hδ₂, H₂⟩ := hh ε hε
  refine ⟨min r (min δ₁ δ₂), lt_min hr (lt_min hδ₁ hδ₂), fun x hx hd => ?_⟩
  have hdr : |x - a| < r := lt_of_lt_of_le hd (min_le_left _ _)
  have hd1 : |x - a| < δ₁ := lt_of_lt_of_le hd (le_trans (min_le_right _ _) (min_le_left _ _))
  have hd2 : |x - a| < δ₂ := lt_of_lt_of_le hd (le_trans (min_le_right _ _) (min_le_right _ _))
  obtain ⟨hb1, hb2⟩ := hb x hx hdr
  have e1 := abs_lt.mp (H₁ x hx hd1)
  have e2 := abs_lt.mp (H₂ x hx hd2)
  rw [abs_lt]
  constructor <;> linarith

/-- A rendőrelv alkalmazása: `lim_{x→0} x·sin(1/x) = 0`. -/
theorem limit_x_mul_sin_inv : LimitAt (fun x : ℝ => x * Real.sin (1 / x)) 0 0 := by
  intro ε hε
  refine ⟨ε, hε, fun x hx hd => ?_⟩
  have h1 : |x * Real.sin (1 / x) - 0| = |x| * |Real.sin (1 / x)| := by
    rw [sub_zero, abs_mul]
  rw [h1]
  have h2 : |Real.sin (1 / x)| ≤ 1 := Real.abs_sin_le_one _
  have h3 : |x| < ε := by simpa using hd
  nlinarith [abs_nonneg x, abs_nonneg (Real.sin (1 / x))]

/-! ## 9. tétel — Folytonosság -/

/-- **A folytonosság ε–δ definíciója.** -/
def ContinuousAtEps (f : ℝ → ℝ) (a : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x : ℝ, |x - a| < δ → |f x - f a| < ε

/-- A folytonosság ekvivalens a Mathlib `ContinuousAt` fogalmával. -/
theorem continuousAtEps_iff {f : ℝ → ℝ} {a : ℝ} : ContinuousAtEps f a ↔ ContinuousAt f a := by
  rw [Metric.continuousAt_iff]
  constructor
  · intro h ε hε
    obtain ⟨δ, hδ, H⟩ := h ε hε
    exact ⟨δ, hδ, fun {x} hd => by rw [Real.dist_eq]; exact H x (by rwa [Real.dist_eq] at hd)⟩
  · intro h ε hε
    obtain ⟨δ, hδ, H⟩ := h ε hε
    refine ⟨δ, hδ, fun x hd => ?_⟩
    have := H (x := x) (by rwa [Real.dist_eq])
    rwa [Real.dist_eq] at this

/-- `f` pontosan akkor folytonos `a`-ban, ha a határértéke `a`-ban `f a`. -/
theorem continuousAtEps_iff_limitAt {f : ℝ → ℝ} {a : ℝ} :
    ContinuousAtEps f a ↔ LimitAt f a (f a) := by
  constructor
  · intro h ε hε
    obtain ⟨δ, hδ, H⟩ := h ε hε
    exact ⟨δ, hδ, fun x _ hd => H x hd⟩
  · intro h ε hε
    obtain ⟨δ, hδ, H⟩ := h ε hε
    refine ⟨δ, hδ, fun x hd => ?_⟩
    rcases eq_or_ne x a with rfl | hne
    · simpa using hε
    · exact H x (abs_pos.mpr (sub_ne_zero.mpr hne)) hd

/-- **Összetett függvény folytonossága** (9. tétel bizonyítandó állítása). -/
theorem continuousAtEps_comp {f g : ℝ → ℝ} {a : ℝ} (hg : ContinuousAtEps g a)
    (hf : ContinuousAtEps f (g a)) : ContinuousAtEps (fun x => f (g x)) a := by
  intro ε hε
  obtain ⟨η, hη, Hf⟩ := hf ε hε
  obtain ⟨δ, hδ, Hg⟩ := hg η hη
  exact ⟨δ, hδ, fun x hd => Hf (g x) (Hg x hd)⟩

/-- Folytonos függvények összege és szorzata folytonos. -/
theorem continuousAtEps_add_mul {f g : ℝ → ℝ} {a : ℝ} (hf : ContinuousAtEps f a)
    (hg : ContinuousAtEps g a) :
    ContinuousAtEps (fun x => f x + g x) a ∧ ContinuousAtEps (fun x => f x * g x) a := by
  rw [continuousAtEps_iff] at hf hg
  exact ⟨continuousAtEps_iff.mpr (hf.add hg), continuousAtEps_iff.mpr (hf.mul hg)⟩

/-- **Szakadási helyek osztályozása:** példa elsőfajú (ugrásos) szakadásra. -/
theorem sign_jump_discontinuity :
    LeftLimitAt (fun x : ℝ => if x < 0 then (-1 : ℝ) else 1) 0 (-1) ∧
      RightLimitAt (fun x : ℝ => if x < 0 then (-1 : ℝ) else 1) 0 1 ∧
      ¬ ∃ L, LimitAt (fun x : ℝ => if x < 0 then (-1 : ℝ) else 1) 0 L := by
  refine ⟨fun ε hε => ⟨1, one_pos, fun x hx _ => by simp [hx, hε]⟩,
    fun ε hε => ⟨1, one_pos, fun x hx _ => by simp [not_lt.mpr hx.le, hε]⟩, ?_⟩
  rintro ⟨L, hL⟩
  obtain ⟨δ, hδ, H⟩ := hL 1 one_pos
  have h1 := H (δ / 2) (by rw [abs_of_pos (by linarith)]; linarith) (by
    rw [abs_of_pos (by linarith)]; simp; linarith)
  have h2 := H (-(δ / 2)) (by rw [abs_of_neg (by linarith)]; simp; linarith) (by
    rw [abs_of_neg (by linarith)]; simp; linarith)
  simp only [] at h1 h2
  rw [if_neg (by linarith)] at h1
  rw [if_pos (by linarith)] at h2
  have a1 := abs_lt.mp h1
  have a2 := abs_lt.mp h2
  linarith [a1.1, a1.2, a2.1, a2.2]

/-! ## 10. tétel — Monoton korlátos sorozat és az `e` szám -/

/-- **Monoton növő, felülről korlátos sorozat konvergens** (a szuprémumához tart). -/
theorem tendsto_of_monotone_bddAbove {u : ℕ → ℝ} (hmono : Monotone u)
    (hbdd : BddAbove (Set.range u)) : ∃ L : ℝ, Tendsto u atTop (nhds L) := by
  exact ⟨_, tendsto_atTop_ciSup hmono hbdd⟩

/-- Az `(1 + 1/n)^n` sorozat monoton növő. -/
theorem one_add_inv_pow_monotone {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) :
    (1 + 1 / (m : ℝ)) ^ m ≤ (1 + 1 / (n : ℝ)) ^ n := by
  induction n, hmn using Nat.le_induction with
  | base => exact le_refl _
  | succ n hn ih =>
      refine le_trans ih ?_
      have hn1 : 1 ≤ n := le_trans hm hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
      set A : ℝ := 1 + 1 / (n : ℝ) with hA
      set B : ℝ := 1 + 1 / ((n : ℝ) + 1) with hB
      have hApos : 0 < A := by simp only [hA]; positivity
      have hBpos : 0 < B := by simp only [hB]; positivity
      have hx : (-2 : ℝ) ≤ -(1 / ((n : ℝ) + 1) ^ 2) := by
        have h1 : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith
        have h2 : 1 / ((n : ℝ) + 1) ^ 2 ≤ 1 := by
          rw [div_le_one (by positivity)]; exact h1
        linarith
      have bern := one_add_mul_le_pow hx (n + 1)
      have hratio : B / A = 1 - 1 / ((n : ℝ) + 1) ^ 2 := by
        simp only [hA, hB]; field_simp; ring
      have hkey : ((n : ℝ)) / ((n : ℝ) + 1) ≤ (B / A) ^ (n + 1) := by
        rw [hratio]
        have h2 : 1 + ((n : ℝ) + 1) * (-(1 / ((n : ℝ) + 1) ^ 2)) = (n : ℝ) / ((n : ℝ) + 1) := by
          field_simp; ring
        calc ((n : ℝ)) / ((n : ℝ) + 1)
            = 1 + ((n : ℝ) + 1) * (-(1 / ((n : ℝ) + 1) ^ 2)) := h2.symm
          _ ≤ (1 + -(1 / ((n : ℝ) + 1) ^ 2)) ^ (n + 1) := by
              push_cast at bern ⊢; convert bern using 2
          _ = (1 - 1 / ((n : ℝ) + 1) ^ 2) ^ (n + 1) := by ring_nf
      have hAinv : (n : ℝ) / ((n : ℝ) + 1) = 1 / A := by simp only [hA]; field_simp
      rw [hAinv, div_pow] at hkey
      have hApow : (0 : ℝ) < A ^ (n + 1) := by positivity
      rw [div_le_div_iff₀ hApos hApow] at hkey
      have hsplit : A ^ (n + 1) = A ^ n * A := by ring
      rw [hsplit] at hkey
      have hfin : A ^ n ≤ B ^ (n + 1) := le_of_mul_le_mul_right (by linarith) hApos
      have hcast : (1 : ℝ) + 1 / ((n : ℕ) + 1 : ℕ) = B := by
        simp only [hB]; push_cast; ring
      rw [hcast]
      exact hfin

/-- Az `(1 + 1/n)^n` sorozat felülről korlátos (4-gyel). -/
theorem one_add_inv_pow_lt_four (n : ℕ) (hn : 1 ≤ n) : (1 + 1 / (n : ℝ)) ^ n < 4 := by
  exact SZTE.Portfolio.Kalkulus.ex_3_16c n hn

/-- **Az `e` szám:** az `(1+1/n)^n` sorozat konvergens, és a határértéke `e`. -/
theorem tendsto_one_add_inv_pow_exp_one :
    Tendsto (fun n : ℕ => (1 + 1 / (n : ℝ)) ^ n) atTop (nhds (Real.exp 1)) := by
  simpa using Real.tendsto_one_add_div_pow_exp (1 : ℝ)

/-! ## 11. tétel — Intervallumon folytonos függvények -/

/-- **Bolzano-tétel.** Ha `f` folytonos az `[a,b]` intervallumon és `f a < 0 < f b`, akkor van
gyöke `(a,b)`-ben. -/
theorem bolzano {a b : ℝ} (hab : a < b) {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc a b))
    (hfa : f a < 0) (hfb : 0 < f b) : ∃ c ∈ Set.Ioo a b, f c = 0 := by
  set S : Set ℝ := {x ∈ Set.Icc a b | f x ≤ 0} with hS
  have haS : a ∈ S := ⟨⟨le_refl a, hab.le⟩, hfa.le⟩
  have hne : S.Nonempty := ⟨a, haS⟩
  have hbdd : BddAbove S := ⟨b, fun x hx => hx.1.2⟩
  set c := sSup S with hc
  have hcmem : c ∈ Set.Icc a b := ⟨le_csSup hbdd haS, csSup_le hne (fun x hx => hx.1.2)⟩
  have hSsub : S ⊆ Set.Icc a b := fun x hx => hx.1
  have hccl : c ∈ closure S := csSup_mem_closure hne hbdd
  have hle : f c ≤ 0 := by
    have hcw : ContinuousWithinAt f S c := (hf c hcmem).mono hSsub
    exact ContinuousWithinAt.closure_le hccl hcw continuousWithinAt_const (fun y hy => hy.2)
  have hcb : c < b := by
    rcases lt_or_eq_of_le hcmem.2 with h | h
    · exact h
    · exact absurd hle (by rw [h]; linarith)
  have hge : 0 ≤ f c := by
    have hsub : Set.Ioc c b ⊆ Set.Icc a b := fun x hx => ⟨le_trans hcmem.1 hx.1.le, hx.2⟩
    have hcw : ContinuousWithinAt f (Set.Ioc c b) c := (hf c hcmem).mono hsub
    have hccl2 : c ∈ closure (Set.Ioc c b) := by
      rw [closure_Ioc (ne_of_lt hcb)]
      exact ⟨le_refl c, hcb.le⟩
    refine ContinuousWithinAt.closure_le hccl2 continuousWithinAt_const hcw (fun y hy => ?_)
    by_contra hcon
    push_neg at hcon
    have hyS : y ∈ S := ⟨hsub hy, hcon.le⟩
    exact absurd (le_csSup hbdd hyS) (not_le.mpr hy.1)
  have hfc : f c = 0 := le_antisymm hle hge
  have hca : a < c := by
    rcases lt_or_eq_of_le hcmem.1 with h | h
    · exact h
    · exact absurd hfc (by rw [← h]; linarith)
  exact ⟨c, ⟨hca, hcb⟩, hfc⟩

/-- **Darboux-tulajdonság (közbülsőérték-tétel).** -/
theorem darboux {a b : ℝ} (hab : a < b) {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc a b))
    {y : ℝ} (hy : y ∈ Set.Ioo (f a) (f b)) : ∃ c ∈ Set.Ioo a b, f c = y := by
  have hg : ContinuousOn (fun x => f x - y) (Set.Icc a b) := hf.sub continuousOn_const
  obtain ⟨c, hc, hfc⟩ := bolzano hab hg (by simpa using sub_neg.mpr hy.1)
    (by simpa using sub_pos.mpr hy.2)
  exact ⟨c, hc, by simpa [sub_eq_zero] using hfc⟩

/-- **Weierstrass-tétel.** Korlátos zárt intervallumon folytonos függvény felveszi a
maximumát és a minimumát. -/
theorem weierstrass {a b : ℝ} (hab : a ≤ b) {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc a b)) :
    (∃ p ∈ Set.Icc a b, ∀ x ∈ Set.Icc a b, f x ≤ f p) ∧
      (∃ q ∈ Set.Icc a b, ∀ x ∈ Set.Icc a b, f q ≤ f x) := by
  have hne : (Set.Icc a b).Nonempty := Set.nonempty_Icc.mpr hab
  obtain ⟨p, hp, hpm⟩ := isCompact_Icc.exists_isMaxOn hne hf
  obtain ⟨q, hq, hqm⟩ := isCompact_Icc.exists_isMinOn hne hf
  exact ⟨⟨p, hp, fun x hx => hpm hx⟩, ⟨q, hq, fun x hx => hqm hx⟩⟩

/-- **Heine-tétel.** Korlátos zárt intervallumon folytonos függvény egyenletesen folytonos. -/
theorem heine_uniform_continuity {a b : ℝ} {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc a b)) :
    ∀ ε > 0, ∃ δ > 0, ∀ x ∈ Set.Icc a b, ∀ y ∈ Set.Icc a b, |x - y| < δ → |f x - f y| < ε := by
  have hu : UniformContinuousOn f (Set.Icc a b) :=
    isCompact_Icc.uniformContinuousOn_of_continuous hf
  rw [Metric.uniformContinuousOn_iff] at hu
  intro ε hε
  obtain ⟨δ, hδ, H⟩ := hu ε hε
  refine ⟨δ, hδ, fun x hx y hy hxy => ?_⟩
  have := H x hx y hy (by rwa [Real.dist_eq])
  rwa [Real.dist_eq] at this

end SZTE.Kredit.Kalkulus
