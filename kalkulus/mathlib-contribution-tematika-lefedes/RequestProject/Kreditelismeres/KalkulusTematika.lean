/-
# Kalkulus I (MBLK37E) — a **Neptun-tárgytematika** „Tantárgy tartalma” pontjainak
# bizonyítéktára

Ez a fájl a `KalkulusIelőadás-3.pdf` tárgytematika *Tantárgy tartalma* mezőjét bontja
elemeire (T‑1 … T‑20), és azokat a pontokat formalizálja, amelyek a korábbi két modulban
(`KalkulusHatarertek.lean`, `KalkulusDifferencial.lean`) még nem szerepeltek.

A teljes megfeleltetést (melyik T‑pontot melyik deklaráció fedi, és melyik Mathlib-hozzájárulás
tartozik hozzá) a repó gyökerében lévő `KALKULUS-TEMATIKA-PR-TABLAZAT.md` tartalmazza.

Az itt formalizált pontok:
* T‑1  a valós számtest (teljességi axióma, arkhimédészi tulajdonság, ℚ nem teljes);
* T‑2  teljes indukció (szokásos és erős alakban);
* T‑3  nevezetes egyenlőtlenségek (háromszög-egyenlőtlenség összegre, három tagú AM–GM);
* T‑4  polinomok, racionális törtfüggvények, gyökös és arkuszfüggvények inverz-viszonyai;
* T‑5  értelmezési tartomány, értékkészlet, inverz függvény, összetétel;
* T‑6  szimmetriatulajdonságok, monotonitás, periodicitás;
* T‑7  elemi függvénytranszformációk (eltolás, tükrözés, nyújtás) grafikonszinten;
* T‑13 érintőegyenes (elsőrendű érintkezés és egyértelműség);
* T‑14 implicit deriválás;
* T‑19 teljes függvényvizsgálat egy konkrét függvényen (`x ↦ x³ − 3x`).
-/
import Mathlib

namespace SZTE.Kredit.KalkulusTematika

open Filter Topology Set

/-! ## T‑1. A valós számtest

A teljességi axióma tartalma: minden nemüres, felülről korlátos halmaznak van legkisebb
felső korlátja. Az alábbi állítás azt mutatja meg, *miért nem elég* a racionális számtest:
az `{x ≥ 0 | x² < 2}` halmaz szuprémuma `√2`, ami irracionális. -/

/-- **A teljességi axióma alkalmazása.** Az `S = {x | 0 ≤ x ∧ x² < 2}` halmaz legkisebb felső
korlátja `√2`, és ez a szám irracionális: a szuprémum létezése tehát a valós számtestben
olyan elemet állít elő, amely a racionális számtestben nem létezik. -/
theorem isLUB_sqrt_two :
    IsLUB {x : ℝ | 0 ≤ x ∧ x ^ 2 < 2} (Real.sqrt 2) ∧ Irrational (Real.sqrt 2) := by
  have h2 : (0 : ℝ) ≤ 2 := by norm_num
  have hsq : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt h2
  have hpos : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  refine ⟨⟨?_, ?_⟩, (Nat.prime_two.irrational_sqrt : Irrational (Real.sqrt 2))⟩
  · rintro x ⟨hx0, hx2⟩
    nlinarith [hsq, hx0, hx2]
  · intro b hb
    by_contra hlt
    push_neg at hlt
    -- `b < √2`, ezért van `b` és `√2` közti elem, ami `S`-ben van
    set c : ℝ := max b 0 with hc
    have hcb : b ≤ c := le_max_left _ _
    have hc0 : 0 ≤ c := le_max_right _ _
    have hcs : c < Real.sqrt 2 := max_lt hlt hpos
    obtain ⟨x, hx1, hx2⟩ := exists_between hcs
    have hx0 : 0 ≤ x := le_trans hc0 (le_of_lt hx1)
    have hxmem : x ∈ {x : ℝ | 0 ≤ x ∧ x ^ 2 < 2} := by
      refine ⟨hx0, ?_⟩
      nlinarith [hsq, hx0, hx2]
    have := hb hxmem
    linarith [hcb, hx1]

/-- **Arkhimédészi tulajdonság:** minden valós számnál van nagyobb természetes szám. -/
theorem archimedean_real (x : ℝ) : ∃ n : ℕ, x < n := exists_nat_gt x

/-! ## T‑2. Teljes indukció -/

/-- **Teljes indukció (szokásos alak):** az első `n` páratlan szám összege `n²`. -/
theorem sum_odd_eq_sq (n : ℕ) : ∑ i ∈ Finset.range n, (2 * i + 1) = n ^ 2 := by
  induction n with
  | zero => simp
  | succ k ih => rw [Finset.sum_range_succ, ih]; ring

/-- **Erős (teljes) indukció:** minden `2 ≤ n` természetes számnak van prímosztója.
A bizonyítás a `Nat.strong_induction_on` elvet használja. -/
theorem exists_prime_dvd_of_two_le : ∀ n : ℕ, 2 ≤ n → ∃ p : ℕ, p.Prime ∧ p ∣ n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    by_cases hp : n.Prime
    · exact ⟨n, hp, dvd_rfl⟩
    · obtain ⟨m, hm1, hmn, hmdvd⟩ : ∃ m, m ≠ 1 ∧ m ≠ n ∧ m ∣ n := by
        rw [Nat.prime_def] at hp
        push_neg at hp
        obtain ⟨m, hmdvd, hm1, hmn⟩ := hp hn
        exact ⟨m, hm1, hmn, hmdvd⟩
      have hm0 : m ≠ 0 := by
        rintro rfl
        exact absurd (Nat.eq_zero_of_zero_dvd hmdvd) (by omega)
      have hmlt : m < n := lt_of_le_of_ne (Nat.le_of_dvd (by omega) hmdvd) hmn
      have hm2 : 2 ≤ m := by omega
      obtain ⟨p, hp, hpm⟩ := ih m hmlt hm2
      exact ⟨p, hp, hpm.trans hmdvd⟩

/-! ## T‑3. Nevezetes egyenlőtlenségek

(A Cauchy–Schwarz-, a Bernoulli- és a kéttagú számtani–mértani egyenlőtlenség a
`KalkulusHatarertek.lean` fájlban szerepel; itt a háromszög-egyenlőtlenség véges összegre
és a háromtagú számtani–mértani egyenlőtlenség következik.) -/

/-- **Háromszög-egyenlőtlenség véges összegre.** -/
theorem abs_sum_le_sum_abs' (n : ℕ) (a : ℕ → ℝ) :
    |∑ i ∈ Finset.range n, a i| ≤ ∑ i ∈ Finset.range n, |a i| :=
  Finset.abs_sum_le_sum_abs _ _

/-- **Számtani–mértani egyenlőtlenség három tagra:** `(abc)^(1/3) ≤ (a+b+c)/3`. -/
theorem am_gm_three {a b c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hc : 0 ≤ c) :
    a ^ ((1 : ℝ) / 3) * b ^ ((1 : ℝ) / 3) * c ^ ((1 : ℝ) / 3) ≤ (a + b + c) / 3 := by
  have key : a ^ ((1 : ℝ) / 3) * b ^ ((1 : ℝ) / 3) * c ^ ((1 : ℝ) / 3)
      ≤ (1 / 3) * a + (1 / 3) * b + (1 / 3) * c :=
    Real.geom_mean_le_arith_mean3_weighted (by norm_num) (by norm_num) (by norm_num)
      ha hb hc (by norm_num)
  linarith

/-! ## T‑4. Polinomok, racionális törtfüggvények, gyökös és arkuszfüggvények -/

/-- **Polinomfüggvény folytonos.** -/
theorem polynomial_continuous (p : Polynomial ℝ) : Continuous fun x : ℝ => p.eval x :=
  p.continuous_aeval

/-- **Racionális törtfüggvény folytonos ott, ahol a nevező nem tűnik el.** -/
theorem rational_continuousAt (p q : Polynomial ℝ) {x : ℝ} (hq : q.eval x ≠ 0) :
    ContinuousAt (fun t : ℝ => p.eval t / q.eval t) x :=
  ((polynomial_continuous p).continuousAt).div ((polynomial_continuous q).continuousAt) hq

/-- **A négyzetgyök a négyzetre emelés inverze a nemnegatív félegyenesen.** -/
theorem sqrt_inverse_on_nonneg :
    (∀ x : ℝ, 0 ≤ x → Real.sqrt (x ^ 2) = x) ∧ (∀ x : ℝ, 0 ≤ x → Real.sqrt x ^ 2 = x) :=
  ⟨fun _ hx => Real.sqrt_sq hx, fun _ hx => Real.sq_sqrt hx⟩

/-- **Az arkusztangens a tangens inverze a `(-π/2, π/2)` intervallumon.** -/
theorem arctan_tan_inverse :
    (∀ x : ℝ, Real.tan (Real.arctan x) = x) ∧
      (∀ x : ℝ, -(Real.pi / 2) < x → x < Real.pi / 2 → Real.arctan (Real.tan x) = x) :=
  ⟨Real.tan_arctan, fun _ h₁ h₂ => Real.arctan_tan h₁ h₂⟩

/-! ## T‑5. Értelmezési tartomány, értékkészlet, inverz függvény, összetétel -/

/-- **Értékkészlet:** a négyzetfüggvény értékkészlete a nemnegatív félegyenes. -/
theorem range_sq : Set.range (fun x : ℝ => x ^ 2) = Set.Ici (0 : ℝ) := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    simp only [Set.mem_Ici]
    positivity
  · intro hy
    exact ⟨Real.sqrt y, Real.sq_sqrt hy⟩

/-- **Inverz függvény létezése:** egy függvénynek pontosan akkor van kétoldali inverze,
ha bijektív. -/
theorem exists_inverse_iff_bijective {α β : Type*} [Nonempty α] (f : α → β) :
    (∃ g : β → α, Function.LeftInverse g f ∧ Function.RightInverse g f) ↔
      Function.Bijective f := by
  constructor
  · rintro ⟨g, hl, hr⟩
    exact ⟨hl.injective, hr.surjective⟩
  · intro hf
    obtain ⟨g, hl, hr⟩ := Function.bijective_iff_has_inverse.mp hf
    exact ⟨g, hl, hr⟩

/-- **Összetétel:** injektív függvények kompozíciója injektív, szürjektíveké szürjektív. -/
theorem comp_injective_surjective {α β γ : Type*} {f : α → β} {g : β → γ} :
    (Function.Injective f → Function.Injective g → Function.Injective (g ∘ f)) ∧
      (Function.Surjective f → Function.Surjective g → Function.Surjective (g ∘ f)) :=
  ⟨fun hf hg => hg.comp hf, fun hf hg => hg.comp hf⟩

/-! ## T‑6. Szimmetria, monotonitás, periodicitás -/

/-- **Szimmetria és monotonitás egy konkrét függvényen:** `x ↦ x²` páros (grafikonja
tengelyesen szimmetrikus), a nemnegatív félegyenesen szigorúan növő, a nempozitívon
szigorúan fogyó. -/
theorem sq_symmetry_monotonicity :
    (∀ x : ℝ, (-x) ^ 2 = x ^ 2) ∧
      StrictMonoOn (fun x : ℝ => x ^ 2) (Set.Ici 0) ∧
      StrictAntiOn (fun x : ℝ => x ^ 2) (Set.Iic 0) := by
  refine ⟨fun x => by ring, ?_, ?_⟩
  · intro x hx y hy hxy
    simp only [Set.mem_Ici] at hx hy
    nlinarith
  · intro x hx y hy hxy
    simp only [Set.mem_Iic] at hx hy
    nlinarith

/-- **Periodicitás:** a szinusz `2π` szerint periodikus, és páratlan. -/
theorem sin_periodic_odd :
    Function.Periodic Real.sin (2 * Real.pi) ∧ ∀ x : ℝ, Real.sin (-x) = -Real.sin x :=
  ⟨Real.sin_periodic, Real.sin_neg⟩

/-- **Szigorú monotonitás ⇒ injektivitás** (a grafikonvázolás egyik alapérve). -/
theorem strictMono_injective' {f : ℝ → ℝ} (hf : StrictMono f) : Function.Injective f :=
  hf.injective

/-! ## T‑7. Elemi függvénytranszformációk

A grafikont a síkbeli ponthalmazával azonosítjuk: `graph f = {(x, f x)}`. -/

/-- Egy valós függvény grafikonja. -/
def graph (f : ℝ → ℝ) : Set (ℝ × ℝ) := {p : ℝ × ℝ | p.2 = f p.1}

/-- **Vízszintes eltolás:** az `x ↦ f (x - c)` függvény grafikonja az `f` grafikonjának
`c`-vel jobbra tolt képe. -/
theorem graph_translate (f : ℝ → ℝ) (c : ℝ) :
    graph (fun x => f (x - c)) = (fun p : ℝ × ℝ => (p.1 + c, p.2)) '' graph f := by
  ext ⟨x, y⟩
  simp only [graph, Set.mem_setOf_eq, Set.mem_image, Prod.mk.injEq, Prod.exists]
  constructor
  · intro h
    exact ⟨x - c, f (x - c), rfl, by ring, h.symm⟩
  · rintro ⟨a, b, hb, hax, hby⟩
    subst hb; subst hby
    rw [← hax]
    ring_nf

/-- **Függőleges nyújtás és eltolás:** az `x ↦ a·f x + d` grafikonja az `f` grafikonjának
képe az `(x, y) ↦ (x, a·y + d)` affin leképezés alatt. -/
theorem graph_scale_shift (f : ℝ → ℝ) (a d : ℝ) :
    graph (fun x => a * f x + d) = (fun p : ℝ × ℝ => (p.1, a * p.2 + d)) '' graph f := by
  ext ⟨x, y⟩
  simp only [graph, Set.mem_setOf_eq, Set.mem_image, Prod.mk.injEq, Prod.exists]
  constructor
  · intro h
    exact ⟨x, f x, rfl, rfl, h.symm⟩
  · rintro ⟨u, v, hv, hux, hy⟩
    subst hv; subst hux
    exact hy.symm

/-- **Tükrözés az `y` tengelyre:** az `x ↦ f (-x)` grafikonja az `f` grafikonjának
`(x, y) ↦ (-x, y)` szerinti tükörképe. -/
theorem graph_reflect_y (f : ℝ → ℝ) :
    graph (fun x => f (-x)) = (fun p : ℝ × ℝ => (-p.1, p.2)) '' graph f := by
  ext ⟨x, y⟩
  simp only [graph, Set.mem_setOf_eq, Set.mem_image, Prod.mk.injEq, Prod.exists]
  constructor
  · intro h
    exact ⟨-x, f (-x), rfl, by ring, h.symm⟩
  · rintro ⟨u, v, hv, hux, hy⟩
    subst hv; subst hy
    rw [← hux]
    ring_nf

/-! ## T‑13. Pontbeli derivált és érintőegyenes -/

/-- Az `f` függvény `a` pontbeli, `L` meredekségű érintőegyenese. -/
def tangentLine (f : ℝ → ℝ) (a L : ℝ) : ℝ → ℝ := fun x => f a + L * (x - a)

/-- **Az érintőegyenes elsőrendű érintkezése.** `f` pontosan akkor differenciálható `a`-ban
`L` deriválttal, ha az `x ↦ f a + L·(x−a)` egyenestől való eltérése `o(x−a)`. -/
theorem hasDerivAt_iff_tangentLine {f : ℝ → ℝ} {a L : ℝ} :
    HasDerivAt f L a ↔
      Tendsto (fun x => (f x - tangentLine f a L x) / (x - a)) (𝓝[≠] a) (𝓝 0) := by
  rw [hasDerivAt_iff_tendsto_slope, ← tendsto_sub_nhds_zero_iff (l := 𝓝[≠] a)]
  refine tendsto_congr' ?_
  filter_upwards [self_mem_nhdsWithin] with x hx
  have hxa : x - a ≠ 0 := sub_ne_zero.mpr hx
  simp only [tangentLine, slope_def_field]
  field_simp
  ring

/-- **Az érintő meredeksége egyértelmű:** ha két meredekség is elsőrendű érintkezést ad,
akkor a kettő egyenlő. -/
theorem tangent_slope_unique {f : ℝ → ℝ} {a L M : ℝ} (hL : HasDerivAt f L a)
    (hM : HasDerivAt f M a) : L = M :=
  hL.unique hM

/-! ## T‑14. Implicit deriválás -/

/-- **Implicit deriválás.** Ha az `y = f x` görbe az `x² + y² = 1` egyenletet elégíti ki,
`f` differenciálható `x`-ben, és `f x ≠ 0`, akkor `f' x = -x / f x`. -/
theorem implicit_deriv_circle {f : ℝ → ℝ} {x y' : ℝ} (hf : HasDerivAt f y' x)
    (hcirc : ∀ t : ℝ, t ^ 2 + f t ^ 2 = 1) (hne : f x ≠ 0) : y' = -x / f x := by
  have hid : HasDerivAt (fun t : ℝ => t) 1 x := hasDerivAt_id x
  have hlhs : HasDerivAt (fun t : ℝ => t ^ 2 + f t ^ 2) (2 * x + 2 * f x * y') x := by
    have h1 : HasDerivAt (fun t : ℝ => t ^ 2) (2 * x) x := by
      simpa using (hasDerivAt_pow 2 x)
    have h2 : HasDerivAt (fun t : ℝ => f t ^ 2) (2 * f x * y') x := by
      simpa [mul_comm, mul_assoc, mul_left_comm] using hf.pow 2
    simpa using h1.add h2
  have hconst : HasDerivAt (fun t : ℝ => t ^ 2 + f t ^ 2) 0 x := by
    have : (fun t : ℝ => t ^ 2 + f t ^ 2) = fun _ : ℝ => (1 : ℝ) := funext hcirc
    rw [this]
    exact hasDerivAt_const x 1
  have := hlhs.unique hconst
  field_simp
  linarith [this]

/-! ## T‑19. Teljes függvényvizsgálat: `f x = x³ − 3x`

Monotonitási intervallumok, lokális szélsőértékek, konvexitás és inflexiós pont. -/

/-- A vizsgált függvény. -/
def cubic : ℝ → ℝ := fun x => x ^ 3 - 3 * x

theorem hasDerivAt_cubic (x : ℝ) : HasDerivAt cubic (3 * x ^ 2 - 3) x := by
  have h1 : HasDerivAt (fun t : ℝ => t ^ 3) (3 * x ^ 2) x := by
    simpa using (hasDerivAt_pow 3 x)
  have h2 : HasDerivAt (fun t : ℝ => 3 * t) 3 x := by
    simpa using (hasDerivAt_id x).const_mul (3 : ℝ)
  simpa [cubic] using h1.sub h2

theorem deriv_cubic (x : ℝ) : deriv cubic x = 3 * x ^ 2 - 3 := (hasDerivAt_cubic x).deriv

/-- **Növekedés az `[1, ∞)` félegyenesen.** -/
theorem cubic_strictMonoOn_Ici_one : StrictMonoOn cubic (Set.Ici 1) := by
  apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Ici 1)
    (fun x _ => ((hasDerivAt_cubic x).continuousAt).continuousWithinAt)
    (f' := fun x => 3 * x ^ 2 - 3)
    (fun x _ => (hasDerivAt_cubic x).hasDerivWithinAt)
  intro x hx
  rw [interior_Ici] at hx
  simp only [Set.mem_Ioi] at hx
  nlinarith

/-- **Fogyás a `[-1, 1]` intervallumon.** -/
theorem cubic_strictAntiOn_Icc : StrictAntiOn cubic (Set.Icc (-1) 1) := by
  apply strictAntiOn_of_hasDerivWithinAt_neg (convex_Icc (-1) 1)
    (fun x _ => ((hasDerivAt_cubic x).continuousAt).continuousWithinAt)
    (f' := fun x => 3 * x ^ 2 - 3)
    (fun x _ => (hasDerivAt_cubic x).hasDerivWithinAt)
  intro x hx
  rw [interior_Icc] at hx
  simp only [Set.mem_Ioo] at hx
  nlinarith [hx.1, hx.2]

/-- **Lokális maximum `x = -1`-ben, lokális minimum `x = 1`-ben.** -/
theorem cubic_local_extrema : IsLocalMax cubic (-1) ∧ IsLocalMin cubic 1 := by
  constructor
  · have h : ∀ x : ℝ, cubic x ≤ cubic (-1) ∨ 1 < x := by
      intro x
      by_cases hx : 1 < x
      · exact Or.inr hx
      · left
        push_neg at hx
        have : cubic (-1) - cubic x = -(x + 1) ^ 2 * (x - 2) := by simp [cubic]; ring
        nlinarith [sq_nonneg (x + 1)]
    filter_upwards [eventually_le_nhds (by norm_num : (-1 : ℝ) < 1)] with x hx
    rcases h x with h' | h'
    · exact h'
    · linarith
  · have h : ∀ x : ℝ, -1 < x → cubic 1 ≤ cubic x := by
      intro x hx
      have : cubic x - cubic 1 = (x - 1) ^ 2 * (x + 2) := by simp [cubic]; ring
      nlinarith [sq_nonneg (x - 1)]
    filter_upwards [eventually_gt_nhds (by norm_num : (-1 : ℝ) < 1)] with x hx
    exact h x hx

/-- A derivált mint függvény. -/
theorem deriv_cubic_eq : deriv cubic = fun x => 3 * x ^ 2 - 3 := funext deriv_cubic

theorem hasDerivAt_deriv_cubic (x : ℝ) : HasDerivAt (deriv cubic) (6 * x) x := by
  rw [deriv_cubic_eq]
  have h2 : HasDerivAt (fun t : ℝ => t ^ 2) (2 * x) x := by
    simpa using hasDerivAt_pow 2 x
  have h4 := (h2.const_mul (3 : ℝ)).sub_const (3 : ℝ)
  convert h4 using 1
  ring

/-- **A második derivált:** `f''(x) = 6x`. -/
theorem deriv2_cubic (x : ℝ) : deriv^[2] cubic x = 6 * x := by
  have hiter : deriv^[2] cubic = deriv (deriv cubic) := by
    simp [Function.iterate_succ]
  rw [hiter, (hasDerivAt_deriv_cubic x).deriv]

theorem continuous_cubic : Continuous cubic := by
  unfold cubic
  fun_prop

/-- **Konvexitás a nemnegatív félegyenesen** (a második derivált `6x ≥ 0`). -/
theorem cubic_convexOn_Ici_zero : ConvexOn ℝ (Set.Ici (0 : ℝ)) cubic := by
  refine convexOn_of_deriv2_nonneg (convex_Ici 0) continuous_cubic.continuousOn
    (fun x _ => (hasDerivAt_cubic x).differentiableAt.differentiableWithinAt)
    (fun x _ => (hasDerivAt_deriv_cubic x).differentiableAt.differentiableWithinAt) ?_
  intro x hx
  rw [interior_Ici, Set.mem_Ioi] at hx
  rw [deriv2_cubic]
  linarith

/-- **Konkávitás a nempozitív félegyenesen.** -/
theorem cubic_concaveOn_Iic_zero : ConcaveOn ℝ (Set.Iic (0 : ℝ)) cubic := by
  refine concaveOn_of_deriv2_nonpos (convex_Iic 0) continuous_cubic.continuousOn
    (fun x _ => (hasDerivAt_cubic x).differentiableAt.differentiableWithinAt)
    (fun x _ => (hasDerivAt_deriv_cubic x).differentiableAt.differentiableWithinAt) ?_
  intro x hx
  rw [interior_Iic, Set.mem_Iio] at hx
  rw [deriv2_cubic]
  linarith

/-- **Inflexiós pont `x = 0`-ban:** a görbe `0`-tól balra konkáv, jobbra konvex. -/
theorem cubic_inflection_zero :
    ConcaveOn ℝ (Set.Iic (0 : ℝ)) cubic ∧ ConvexOn ℝ (Set.Ici (0 : ℝ)) cubic :=
  ⟨cubic_concaveOn_Iic_zero, cubic_convexOn_Ici_zero⟩

end SZTE.Kredit.KalkulusTematika
