/-
# Kalkulus I — kreditelismerési bizonyítéktár, 2. rész

Ez a fájl a `kalkulus-tetelsor-2025.pdf` **12–18. tételéhez** tartozó
állításokat formalizálja Lean 4-ben.

Fedett tételsor-pontok:
* 12. a differenciálhányados fogalma, ekvivalens definíció, differenciálhatóság ⇒ folytonosság;
* 13. differenciálási szabályok (összeg, szorzat, hányados, láncszabály, inverz);
* 14. a szélsőérték szükséges feltétele (Fermat-tétel), Rolle tétele;
* 15. Lagrange- és Cauchy-féle középértéktétel, konstans függvény jellemzése;
* 16. monotonitás és derivált kapcsolata, lokális szélsőérték elegendő feltétele;
* 17. konvexitás, L'Hospital-szabály;
* 18. Taylor-polinom, Taylor tétele Lagrange-maradéktaggal, hibabecslés.
-/
import Mathlib
import RequestProject.Kreditelismeres.KalkulusHatarertek

namespace SZTE.Kredit.Kalkulus

open Filter Topology Set

/-! ## 12. tétel — A differenciálhányados -/

/-- **A differenciálhányados definíciója a saját ε–δ határértékkel:** `f` differenciálható
`a`-ban `L` deriválttal pontosan akkor, ha a különbségi hányados határértéke `L`. -/
theorem hasDerivAt_iff_limitAt_slope {f : ℝ → ℝ} {a L : ℝ} :
    HasDerivAt f L a ↔ LimitAt (fun x => (f x - f a) / (x - a)) a L := by
  rw [hasDerivAt_iff_tendsto_slope, limitAt_iff_tendsto]
  have hslope : slope f a = fun x => (f x - f a) / (x - a) := by
    funext x; simp [slope_def_field, div_eq_inv_mul]
  rw [hslope]

/-- **Ekvivalens definíció:** `f x = f a + L·(x-a) + r(x)·(x-a)`, ahol `r(x) → 0`. -/
theorem hasDerivAt_iff_littleO {f : ℝ → ℝ} {a L : ℝ} :
    HasDerivAt f L a ↔
      ∃ r : ℝ → ℝ, (∀ x, f x = f a + L * (x - a) + r x * (x - a)) ∧ LimitAt r a 0 ∧ r a = 0 := by
  constructor
  · intro h
    refine ⟨fun x => if x = a then 0 else (f x - f a - L * (x - a)) / (x - a), ?_, ?_, by simp⟩
    · intro x
      by_cases hx : x = a
      · simp [hx]
      · have h0 : x - a ≠ 0 := sub_ne_zero.mpr hx
        simp only [if_neg hx]
        field_simp
        ring
    · intro ε hε
      have hslope : Tendsto (slope f a) (𝓝[≠] a) (𝓝 L) := hasDerivAt_iff_tendsto_slope.mp h
      rw [Metric.tendsto_nhdsWithin_nhds] at hslope
      obtain ⟨δ, hδ, H⟩ := hslope ε hε
      refine ⟨δ, hδ, fun x hx hd => ?_⟩
      have hxa : x ≠ a := by intro hc; rw [hc] at hx; simp at hx
      have h0 : x - a ≠ 0 := sub_ne_zero.mpr hxa
      have hH := H (x := x) hxa (by rwa [Real.dist_eq])
      rw [Real.dist_eq] at hH
      have heq : (if x = a then (0 : ℝ) else (f x - f a - L * (x - a)) / (x - a)) - 0
          = slope f a x - L := by
        rw [if_neg hxa, slope_def_field]
        field_simp
        ring
      rw [heq]
      exact hH
  · rintro ⟨r, hrep, hlim, hra⟩
    rw [hasDerivAt_iff_tendsto_slope, Metric.tendsto_nhdsWithin_nhds]
    intro ε hε
    obtain ⟨δ, hδ, H⟩ := hlim ε hε
    refine ⟨δ, hδ, fun {x} hx hd => ?_⟩
    have hxa : x ≠ a := hx
    have h0 : x - a ≠ 0 := sub_ne_zero.mpr hxa
    have h1 : slope f a x - L = r x := by
      rw [slope_def_field, hrep x]
      field_simp
      ring
    rw [Real.dist_eq, h1]
    have := H x (abs_pos.mpr h0) (by rwa [Real.dist_eq] at hd)
    simpa using this

/-- **Differenciálhatóság ⇒ folytonosság** (12. tétel bizonyítandó állítása). -/
theorem continuousAt_of_hasDerivAt {f : ℝ → ℝ} {a L : ℝ} (h : HasDerivAt f L a) :
    ContinuousAtEps f a :=
  continuousAtEps_iff.mpr h.continuousAt

/-- Példa arra, hogy a megfordítás nem igaz: `|x|` folytonos `0`-ban, de nem differenciálható. -/
theorem abs_continuous_not_differentiable :
    ContinuousAtEps (fun x : ℝ => |x|) 0 ∧ ¬ ∃ L : ℝ, HasDerivAt (fun x : ℝ => |x|) L 0 := by
  refine ⟨continuousAtEps_iff.mpr continuous_abs.continuousAt, ?_⟩
  rintro ⟨L, hL⟩
  exact not_differentiableAt_abs_zero hL.differentiableAt

/-! ## 13. tétel — Differenciálási szabályok -/

/-- **Összeg differenciálása.** -/
theorem deriv_add_rule {f g : ℝ → ℝ} {a u v : ℝ} (hf : HasDerivAt f u a)
    (hg : HasDerivAt g v a) : HasDerivAt (fun x => f x + g x) (u + v) a :=
  hf.add hg

/-- **Szorzat differenciálása** (13. tétel bizonyítandó állítása). -/
theorem deriv_mul_rule {f g : ℝ → ℝ} {a u v : ℝ} (hf : HasDerivAt f u a)
    (hg : HasDerivAt g v a) : HasDerivAt (fun x => f x * g x) (u * g a + f a * v) a :=
  hf.mul hg

/-- **Hányados differenciálása.** -/
theorem deriv_div_rule {f g : ℝ → ℝ} {a u v : ℝ} (hf : HasDerivAt f u a)
    (hg : HasDerivAt g v a) (hga : g a ≠ 0) :
    HasDerivAt (fun x => f x / g x) ((u * g a - f a * v) / (g a) ^ 2) a :=
  hf.div hg hga

/-- **Láncszabály (összetett függvény differenciálása).** -/
theorem deriv_comp_rule {f g : ℝ → ℝ} {a u v : ℝ} (hg : HasDerivAt g v a)
    (hf : HasDerivAt f u (g a)) : HasDerivAt (fun x => f (g x)) (u * v) a :=
  hf.comp a hg

/-- **Az inverz függvény differenciálhányadosa.** -/
theorem deriv_inverse_rule {f g : ℝ → ℝ} {a u : ℝ} (hg : ContinuousAt g (f a))
    (hfg : ∀ x, g (f x) = x) (hgf : ∀ y, f (g y) = y) (hf : HasDerivAt f u a) (hu : u ≠ 0) :
    HasDerivAt g (1 / u) (f a) := by
  have hga : g (f a) = a := hfg a
  have hfd : HasDerivAt f u (g (f a)) := by rw [hga]; exact hf
  have h := HasDerivAt.of_local_left_inverse hg hfd hu (Filter.Eventually.of_forall hgf)
  simpa [one_div] using h

/-! ## 14. tétel — Szélsőérték szükséges feltétele, Rolle tétele -/

/-- **Fermat-tétel.** Belső lokális szélsőértékhelyen a derivált nulla. -/
theorem fermat_deriv_eq_zero {f : ℝ → ℝ} {a b c L : ℝ} (hc : c ∈ Ioo a b)
    (hmax : ∀ x ∈ Ioo a b, f x ≤ f c) (h : HasDerivAt f L c) : L = 0 := by
  have hlm : IsLocalMax f c := by
    filter_upwards [Ioo_mem_nhds hc.1 hc.2] with x hx using hmax x hx
  exact hlm.hasDerivAt_eq_zero h

/-- **Rolle tétele.** -/
theorem rolle {a b : ℝ} (hab : a < b) {f : ℝ → ℝ} (hcont : ContinuousOn f (Icc a b))
    (hderiv : ∀ x ∈ Ioo a b, DifferentiableAt ℝ f x) (hfab : f a = f b) :
    ∃ c ∈ Ioo a b, HasDerivAt f 0 c := by
  obtain ⟨c, hc, hdc⟩ := exists_deriv_eq_zero hab hcont hfab
  refine ⟨c, hc, ?_⟩
  have := (hderiv c hc).hasDerivAt
  rwa [hdc] at this

/-! ## 15. tétel — Középértéktételek -/

/-- **Lagrange-féle középértéktétel.** -/
theorem lagrange_mvt {a b : ℝ} (hab : a < b) {f : ℝ → ℝ} (hcont : ContinuousOn f (Icc a b))
    (hderiv : ∀ x ∈ Ioo a b, DifferentiableAt ℝ f x) :
    ∃ c ∈ Ioo a b, HasDerivAt f ((f b - f a) / (b - a)) c := by
  obtain ⟨c, hc, hdc⟩ :=
    exists_deriv_eq_slope f hab hcont (fun x hx => (hderiv x hx).differentiableWithinAt)
  refine ⟨c, hc, ?_⟩
  have := (hderiv c hc).hasDerivAt
  rwa [hdc] at this

/-- **Cauchy-féle középértéktétel.** -/
theorem cauchy_mvt {a b : ℝ} (hab : a < b) {f g : ℝ → ℝ} (hfc : ContinuousOn f (Icc a b))
    (hgc : ContinuousOn g (Icc a b)) (hfd : ∀ x ∈ Ioo a b, DifferentiableAt ℝ f x)
    (hgd : ∀ x ∈ Ioo a b, DifferentiableAt ℝ g x) :
    ∃ c ∈ Ioo a b, (f b - f a) * deriv g c = (g b - g a) * deriv f c := by
  obtain ⟨c, hc, hcc⟩ := exists_ratio_deriv_eq_ratio_slope f hab hfc
    (fun x hx => (hfd x hx).differentiableWithinAt) g hgc
    (fun x hx => (hgd x hx).differentiableWithinAt)
  exact ⟨c, hc, by linarith [hcc]⟩

/-- **5.2.1. Következmény.** Ha a derivált egy intervallumon mindenütt eltűnik, akkor a
függvény konstans. -/
theorem const_of_deriv_eq_zero {a b : ℝ} {f : ℝ → ℝ} (hcont : ContinuousOn f (Icc a b))
    (hderiv : ∀ x ∈ Ioo a b, HasDerivAt f 0 x) :
    ∀ x ∈ Icc a b, f x = f a := by
  intro x hx
  rcases eq_or_lt_of_le hx.1 with h | h
  · rw [← h]
  · have hsub : Icc a x ⊆ Icc a b := Icc_subset_Icc le_rfl hx.2
    have hsub' : Ioo a x ⊆ Ioo a b := fun y hy => ⟨hy.1, lt_of_lt_of_le hy.2 hx.2⟩
    obtain ⟨c, hc, hdc⟩ := lagrange_mvt h (hcont.mono hsub)
      (fun y hy => (hderiv y (hsub' hy)).differentiableAt)
    have h0 : HasDerivAt f 0 c := hderiv c (hsub' hc)
    have heq : (f x - f a) / (x - a) = 0 := (hdc.unique h0)
    have hxa : x - a ≠ 0 := sub_ne_zero.mpr (ne_of_gt h)
    have := div_eq_zero_iff.mp heq
    rcases this with h1 | h1
    · linarith [sub_eq_zero.mp h1]
    · exact absurd h1 hxa

/-- Két függvény, amelyek deriváltja megegyezik, csak konstansban különbözik. -/
theorem sub_const_of_deriv_eq {a b : ℝ} {f g : ℝ → ℝ} (hfc : ContinuousOn f (Icc a b))
    (hgc : ContinuousOn g (Icc a b))
    (h : ∀ x ∈ Ioo a b, ∃ L : ℝ, HasDerivAt f L x ∧ HasDerivAt g L x) :
    ∀ x ∈ Icc a b, f x - g x = f a - g a := by
  refine const_of_deriv_eq_zero (f := fun y => f y - g y) (hfc.sub hgc) (fun x hx => ?_)
  obtain ⟨L, hL1, hL2⟩ := h x hx
  have hsub := hL1.sub hL2
  rwa [sub_self] at hsub

/-! ## 16. tétel — Monotonitás és lokális szélsőérték -/

/-- **Monotonitás és derivált kapcsolata.** Nemnegatív derivált ⇒ monoton növekedés. -/
theorem monotoneOn_of_deriv_nonneg' {a b : ℝ} {f : ℝ → ℝ} (hcont : ContinuousOn f (Icc a b))
    (hderiv : ∀ x ∈ Ioo a b, DifferentiableAt ℝ f x) (hpos : ∀ x ∈ Ioo a b, 0 ≤ deriv f x) :
    MonotoneOn f (Icc a b) := by
  refine _root_.monotoneOn_of_deriv_nonneg (convex_Icc a b) hcont ?_ ?_
  · rw [interior_Icc]
    exact fun x hx => (hderiv x hx).differentiableWithinAt
  · rw [interior_Icc]
    exact hpos

/-- Pozitív derivált ⇒ szigorú monotonitás. -/
theorem strictMonoOn_of_deriv_pos' {a b : ℝ} {f : ℝ → ℝ} (hcont : ContinuousOn f (Icc a b))
    (hpos : ∀ x ∈ Ioo a b, 0 < deriv f x) : StrictMonoOn f (Icc a b) := by
  refine _root_.strictMonoOn_of_deriv_pos (convex_Icc a b) hcont ?_
  rw [interior_Icc]
  exact hpos

/-- **A lokális szélsőérték elegendő feltétele (első derivált teszt).** Ha a derivált `c`
előtt nempozitív, `c` után nemnegatív, akkor `c` (abszolút, tehát lokális is) minimumhely
az `[a,b]` intervallumon. -/
theorem isLocalMin_of_deriv_sign {a b c : ℝ} {f : ℝ → ℝ} (hc : c ∈ Ioo a b)
    (hcont : ContinuousOn f (Icc a b)) (hderiv : ∀ x ∈ Ioo a b, DifferentiableAt ℝ f x)
    (hleft : ∀ x ∈ Ioo a c, deriv f x ≤ 0) (hright : ∀ x ∈ Ioo c b, 0 ≤ deriv f x) :
    ∀ x ∈ Icc a b, f c ≤ f x := by
  have hac : a ≤ c := hc.1.le
  have hcb : c ≤ b := hc.2.le
  have hanti : AntitoneOn f (Icc a c) := by
    refine _root_.antitoneOn_of_deriv_nonpos (convex_Icc a c)
      (hcont.mono (Icc_subset_Icc le_rfl hcb)) ?_ ?_
    · rw [interior_Icc]
      exact fun x hx => (hderiv x ⟨hx.1, lt_of_lt_of_le hx.2 hcb⟩).differentiableWithinAt
    · rw [interior_Icc]
      exact hleft
  have hmono : MonotoneOn f (Icc c b) := by
    refine _root_.monotoneOn_of_deriv_nonneg (convex_Icc c b)
      (hcont.mono (Icc_subset_Icc hac le_rfl)) ?_ ?_
    · rw [interior_Icc]
      exact fun x hx => (hderiv x ⟨lt_of_le_of_lt hac hx.1, hx.2⟩).differentiableWithinAt
    · rw [interior_Icc]
      exact hright
  intro x hx
  rcases le_total x c with h | h
  · exact hanti ⟨hx.1, h⟩ ⟨hac, le_rfl⟩ h
  · exact hmono ⟨le_rfl, hcb⟩ ⟨h, hx.2⟩ h

/-- **Második derivált teszt.** -/
theorem isLocalMin_of_deriv2_pos {f : ℝ → ℝ} {c : ℝ} (hcont : ContinuousAt f c)
    (h1 : deriv f c = 0) (h2 : 0 < deriv (deriv f) c) : IsLocalMin f c :=
  isLocalMin_of_deriv_deriv_pos h2 h1 hcont

/-! ## 17. tétel — Konvexitás és a L'Hospital-szabály -/

/-- **Konvexitás és a második derivált.** Ha `f'' ≥ 0` egy intervallumon, akkor `f` konvex. -/
theorem convexOn_of_deriv2_nonneg' {a b : ℝ} {f : ℝ → ℝ} (hcont : ContinuousOn f (Icc a b))
    (hd : ∀ x ∈ Ioo a b, DifferentiableAt ℝ f x)
    (hd2 : ∀ x ∈ Ioo a b, DifferentiableAt ℝ (deriv f) x)
    (hpos : ∀ x ∈ Ioo a b, 0 ≤ deriv (deriv f) x) : ConvexOn ℝ (Icc a b) f := by
  refine _root_.convexOn_of_deriv2_nonneg (convex_Icc a b) hcont ?_ ?_ ?_
  · rw [interior_Icc]
    exact fun x hx => (hd x hx).differentiableWithinAt
  · rw [interior_Icc]
    exact fun x hx => (hd2 x hx).differentiableWithinAt
  · rw [interior_Icc]
    intro x hx
    simpa [Function.iterate_succ] using hpos x hx

/-- **Konvex függvény és a húr:** a konvexitás definíciójából adódó alapegyenlőtlenség. -/
theorem convexOn_chord {f : ℝ → ℝ} {s : Set ℝ} (hf : ConvexOn ℝ s f) {x y : ℝ} (hx : x ∈ s)
    (hy : y ∈ s) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    f (t * x + (1 - t) * y) ≤ t * f x + (1 - t) * f y := by
  simpa [smul_eq_mul] using hf.2 hx hy ht0 (by linarith : (0 : ℝ) ≤ 1 - t) (by ring)

/-- **L'Hospital-szabály** a `0/0` esetre, jobb oldali határértékkel (az órán tárgyalt eset). -/
theorem lhospital_zero_right {a b : ℝ} (hab : a < b) {f g : ℝ → ℝ} {L : ℝ}
    (hfd : ∀ x ∈ Ioo a b, DifferentiableAt ℝ f x)
    (hg' : ∀ x ∈ Ioo a b, deriv g x ≠ 0)
    (hf0 : Tendsto f (nhdsWithin a (Ioi a)) (nhds 0))
    (hg0 : Tendsto g (nhdsWithin a (Ioi a)) (nhds 0))
    (hratio : Tendsto (fun x => deriv f x / deriv g x) (nhdsWithin a (Ioi a)) (nhds L)) :
    Tendsto (fun x => f x / g x) (nhdsWithin a (Ioi a)) (nhds L) :=
  deriv.lhopital_zero_right_on_Ioo hab
    (fun x hx => (hfd x hx).differentiableWithinAt) hg' hf0 hg0 hratio

/-- A `0/0` határérték alapesete: `lim_{x→0} sin x / x = 1`. -/
theorem limit_sin_div_x : LimitAt (fun x : ℝ => Real.sin x / x) 0 1 := by
  have h := hasDerivAt_iff_limitAt_slope.mp (Real.hasDerivAt_sin 0)
  simpa using h

/-! ## 18. tétel — Taylor-polinom és Taylor tétele -/

/-- Az `f` függvény `n`-edfokú Taylor-polinomja az `a` pontban. -/
noncomputable def taylorPoly (f : ℝ → ℝ) (n : ℕ) (a : ℝ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (n + 1), iteratedDeriv k f a / (Nat.factorial k) * (x - a) ^ k

set_option linter.unreachableTactic false in
set_option linter.unusedTactic false in
/-- A Mathlib Lagrange-maradéktagos Taylor-tételének `Icc`/`Ioo` alakja.

A Mathlib újabb verzióiban a `taylor_mean_remainder_lagrange` állítás rendezetlen
intervallumokkal (`uIcc`, `uIoo`) és `x₀ ≠ x` feltétellel van kimondva; ez a burkoló
mindkét változattal működik, így a fájl a rögzített és a legfrissebb Mathlib-bel is fordul.
A `first` két ága közül verziótól függően pontosan az egyik fut le; a másik ág ezért
szükségszerűen „nem hajtódik végre”, emiatt kapcsoljuk ki itt a megfelelő lintereket. -/
theorem taylor_mean_remainder_lagrange_Icc {f : ℝ → ℝ} {a b : ℝ} {n : ℕ} (hab : a < b)
    (hf : ContDiffOn ℝ n f (Icc a b))
    (hf' : DifferentiableOn ℝ (iteratedDerivWithin n f (Icc a b)) (Ioo a b)) :
    ∃ c ∈ Ioo a b, f b - taylorWithinEval f n (Icc a b) a b =
      iteratedDerivWithin (n + 1) f (Icc a b) c * (b - a) ^ (n + 1) / (Nat.factorial (n + 1) : ℝ) := by
  first
  | · have h1 : Set.uIcc a b = Icc a b := Set.uIcc_of_le hab.le
      have h2 : Set.uIoo a b = Ioo a b := Set.uIoo_of_lt hab
      have key := taylor_mean_remainder_lagrange (f := f) (x₀ := a) (x := b) (n := n)
        hab.ne (by rw [h1]; exact hf) (by rw [h1, h2]; exact hf')
      rwa [h1, h2] at key
  | exact taylor_mean_remainder_lagrange hab hf hf'

/-- **Taylor tétele Lagrange-maradéktaggal.** -/
theorem taylor_lagrange {f : ℝ → ℝ} {a b : ℝ} (hab : a < b) (n : ℕ)
    (hf : ContDiff ℝ (n + 1) f) :
    ∃ c ∈ Ioo a b,
      f b = taylorPoly f n a b +
        iteratedDeriv (n + 1) f c / (Nat.factorial (n + 1)) * (b - a) ^ (n + 1) := by
  have hU : UniqueDiffOn ℝ (Icc a b) := uniqueDiffOn_Icc hab
  have hcd : ContDiffOn ℝ (n : ℕ∞) f (Icc a b) :=
    (hf.of_le (by exact_mod_cast Nat.le_succ n)).contDiffOn
  have hdiff : DifferentiableOn ℝ (iteratedDerivWithin n f (Icc a b)) (Ioo a b) :=
    ((hf.contDiffOn (n := ((n : ℕ∞) + 1))).differentiableOn_iteratedDerivWithin
      (by exact_mod_cast Nat.lt_succ_self n) hU).mono Ioo_subset_Icc_self
  obtain ⟨c, hc, hEq⟩ := taylor_mean_remainder_lagrange_Icc hab hcd hdiff
  refine ⟨c, hc, ?_⟩
  have hTP : taylorWithinEval f n (Icc a b) a b = taylorPoly f n a b := by
    rw [taylor_within_apply]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [iteratedDerivWithin_eq_iteratedDeriv hU (hf.contDiffAt.of_le (by
      simp only [Finset.mem_range] at hk
      exact_mod_cast (Nat.lt_succ_iff.mp hk).trans (Nat.le_succ n))) (left_mem_Icc.2 hab.le)]
    simp only [smul_eq_mul]
    ring
  have hR : iteratedDerivWithin (n + 1) f (Icc a b) c = iteratedDeriv (n + 1) f c :=
    iteratedDerivWithin_eq_iteratedDeriv hU (hf.contDiffAt.of_le le_rfl) (Ioo_subset_Icc_self hc)
  rw [hTP, hR] at hEq
  linear_combination hEq

/-- **Hibabecslés példa.** A `sin` (negyedfokú) Taylor-polinomja a `0` körül `x - x³/6`, és a
hiba `|x|⁵/120`-nál nem nagyobb. -/
theorem taylor_sin_error_pos {x : ℝ} (hx : 0 < x) :
    |Real.sin x - (x - x ^ 3 / 6)| ≤ |x| ^ 5 / 120 := by
  obtain ⟨c, _, hEq⟩ := taylor_lagrange (f := Real.sin) (a := 0) (b := x) hx 4 Real.contDiff_sin
  have hTP : taylorPoly Real.sin 4 0 x = x - x ^ 3 / 6 := by
    simp [taylorPoly, Finset.sum_range_succ, iteratedDeriv_succ, Real.deriv_sin, Real.deriv_cos]
    ring
  have h5 : iteratedDeriv 5 Real.sin = Real.cos := by
    simp [iteratedDeriv_succ, Real.deriv_sin, Real.deriv_cos]
  rw [hTP, h5] at hEq
  have hrepr : Real.sin x - (x - x ^ 3 / 6) = Real.cos c / 120 * x ^ 5 := by
    rw [hEq]; norm_num [Nat.factorial]
  rw [hrepr, abs_mul, abs_div, abs_pow, show |(120 : ℝ)| = 120 by norm_num]
  have h1 : |Real.cos c| ≤ 1 := Real.abs_cos_le_one c
  have hp : (0 : ℝ) ≤ |x| ^ 5 := by positivity
  calc |Real.cos c| / 120 * |x| ^ 5 ≤ 1 / 120 * |x| ^ 5 := by
        apply mul_le_mul_of_nonneg_right _ hp
        linarith
    _ = |x| ^ 5 / 120 := by ring

theorem taylor_sin_error (x : ℝ) :
    |Real.sin x - (x - x ^ 3 / 6)| ≤ |x| ^ 5 / 120 := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · have h := taylor_sin_error_pos (x := -x) (by linarith)
    have e : Real.sin (-x) - (-x - (-x) ^ 3 / 6) = -(Real.sin x - (x - x ^ 3 / 6)) := by
      rw [Real.sin_neg]; ring
    rw [e, abs_neg, abs_neg] at h
    exact h
  · simp [hx]
  · exact taylor_sin_error_pos hx

/-- **Hibabecslés példa.** `|eˣ - (1 + x + x²/2)| ≤ e·|x|³/6`, ha `|x| ≤ 1`. -/
theorem taylor_exp_error {x : ℝ} (hx : |x| ≤ 1) :
    |Real.exp x - (1 + x + x ^ 2 / 2)| ≤ Real.exp 1 * |x| ^ 3 / 6 := by
  have h := Real.exp_bound hx (n := 3) (by norm_num)
  have hs : ∑ m ∈ Finset.range 3, x ^ m / (Nat.factorial m : ℝ) = 1 + x + x ^ 2 / 2 := by
    simp [Finset.sum_range_succ, Nat.factorial]
  rw [hs] at h
  refine h.trans ?_
  have he : (2 : ℝ) ≤ Real.exp 1 := by
    have := Real.add_one_le_exp (1 : ℝ)
    linarith
  have hp : (0 : ℝ) ≤ |x| ^ 3 := by positivity
  norm_num [Nat.factorial]
  nlinarith [hp, he]

end SZTE.Kredit.Kalkulus
