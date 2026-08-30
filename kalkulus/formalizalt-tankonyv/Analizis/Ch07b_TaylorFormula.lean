import Mathlib
import Analizis.Ch07a_MagasabbrenduDerivaltak

/-!
# Leindler László: Analízis — 7. fejezet (b): Taylor-formula

A könyv 106–110. oldalának, valamint a 8.5.2. Tételnek a formalizálása:

* **7.2.2. Definíció** — Taylor-polinom és Lagrange-féle maradéktag,
* **7.2.1. Tétel** — a **Taylor-formula** Lagrange-féle maradéktaggal,
* a **Maclaurin-formula** (az `a = 0` eset),
* **8.5.2. Tétel** — a szélső érték, illetve a monotonitás létezése az első el nem tűnő
  magasabbrendű differenciálhányados rendje alapján (bizonyítása a Taylor-formulán alapul).
-/

namespace Leindler.Ch07

open Set Leindler Leindler.Ch05 Leindler.Ch06

/-! ## 7.2. Taylor-formula -/

/-- **7.2.2. Definíció.** Az `f` függvény `a` pont körüli `(n-1)`-edik *Taylor-polinomja*:
`Tₙ₋₁(x) = f(a) + f'(a)(x-a) + … + f⁽ⁿ⁻¹⁾(a)/(n-1)! · (x-a)ⁿ⁻¹`. -/
noncomputable def taylorPolinom (f : ℝ → ℝ) (n : ℕ) (a x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range n, nDerivalt k f a / (Nat.factorial k : ℝ) * (x - a) ^ k

/-- **7.2.2. Definíció.** Az `n`-edik *Lagrange-féle maradéktag*:
`Rₙ(x) = f⁽ⁿ⁾(a + θ(x-a))/n! · (x-a)ⁿ`, ahol `0 < θ < 1`. -/
noncomputable def lagrangeMaradektag (f : ℝ → ℝ) (n : ℕ) (a x theta : ℝ) : ℝ :=
  nDerivalt n f (a + theta * (x - a)) / (Nat.factorial n : ℝ) * (x - a) ^ n

/-! ### Segédtételek a Taylor-formulához -/

/-- A `t ↦ ∑_{k≤m} f⁽ᵏ⁾(t)/k!·(x-t)ᵏ` függvény deriváltja *teleszkopikusan* összecsúszik:
`f⁽ᵐ⁺¹⁾(t)/m!·(x-t)ᵐ`. (Ez a Taylor-formula bizonyításának kulcslépése.) -/
theorem hasDerivAt_taylorOsszeg {f : ℝ → ℝ} {s : Set ℝ} (m : ℕ)
    (hf : NszerDifferencialhato f (m + 1) s) {t : ℝ} (ht : t ∈ s) (x : ℝ) :
    HasDerivAt (fun u => ∑ k ∈ Finset.range (m + 1),
        nDerivalt k f u / (Nat.factorial k : ℝ) * (x - u) ^ k)
      (nDerivalt (m + 1) f t / (Nat.factorial m : ℝ) * (x - t) ^ m) t := by
  induction m with
  | zero =>
      have h0 : HasDerivAt (nDerivalt 0 f) (nDerivalt 1 f t) t :=
        (derivalt_iff_hasDerivAt _ _ _).1 (hf 0 (by omega) t ht)
      simpa using h0
  | succ m ih =>
      have ih' := ih (hf.mono (by omega))
      have hA : HasDerivAt (nDerivalt (m + 1) f) (nDerivalt (m + 1 + 1) f t) t :=
        (derivalt_iff_hasDerivAt _ _ _).1 (hf (m + 1) (by omega) t ht)
      have hB : HasDerivAt (fun u : ℝ => (x - u) ^ (m + 1))
          ((((m : ℝ) + 1)) * (x - t) ^ m * (-1)) t := by
        have h1 : HasDerivAt (fun u : ℝ => x - u) (-1) t := by
          simpa using (hasDerivAt_id t).const_sub x
        simpa using h1.pow (m + 1)
      have hlast := (hA.div_const ((Nat.factorial (m + 1) : ℝ))).mul hB
      have hfun : (fun u => ∑ k ∈ Finset.range (m + 1 + 1),
            nDerivalt k f u / (Nat.factorial k : ℝ) * (x - u) ^ k)
          = fun u => (∑ k ∈ Finset.range (m + 1),
              nDerivalt k f u / (Nat.factorial k : ℝ) * (x - u) ^ k)
              + nDerivalt (m + 1) f u / (Nat.factorial (m + 1) : ℝ) * (x - u) ^ (m + 1) := by
        funext u
        rw [Finset.sum_range_succ]
      rw [hfun]
      have hsum := ih'.add hlast
      convert hsum using 1
      have hm0 : (Nat.factorial m : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero m)
      have hfac : (Nat.factorial (m + 1) : ℝ) = ((m : ℝ) + 1) * (Nat.factorial m : ℝ) := by
        push_cast [Nat.factorial_succ]
        ring
      rw [hfac]
      field_simp
      ring

/-- **7.2.1. Tétel (Taylor-formula).** Ha az `f(x)` függvény az `a` pont valamely
környezetében `n`-szer differenciálható, akkor minden ebbe a környezetbe eső `x` helyen

`f(x) = f(a) + f'(a)(x-a) + … + f⁽ⁿ⁻¹⁾(a)/(n-1)!·(x-a)ⁿ⁻¹ + f⁽ⁿ⁾(a+θ(x-a))/n!·(x-a)ⁿ`,

ahol `0 < θ = θ(x,n) < 1`.

*Bizonyítás (a könyv szerint).* Az `(*)` egyenlőséget teljesítő `c(x₀)` együtthatóval
tekintjük a `Pₙ` polinomot, majd a `k = f - Pₙ` különbségfüggvényre `n`-szer alkalmazzuk a
Rolle-tételt; így kapunk olyan `ξₙ` pontot `a` és `x₀` között, ahol `k⁽ⁿ⁾(ξₙ) = 0`, azaz
`c(x₀) = f⁽ⁿ⁾(ξₙ)/n!`. -/
theorem taylor_formula {f : ℝ → ℝ} {c d : ℝ} {n : ℕ} (hn : 0 < n)
    (hf : NszerDifferencialhato f n (Ioo c d)) {a x : ℝ} (ha : a ∈ Ioo c d)
    (hx : x ∈ Ioo c d) :
    ∃ theta ∈ Ioo (0 : ℝ) 1,
      f x = taylorPolinom f n a x + lagrangeMaradektag f n a x theta := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rcases eq_or_ne x a with rfl | hxa
  · -- Az `x = a` eset: mindkét oldal `f(a)`.
    refine ⟨1 / 2, ⟨by norm_num, by norm_num⟩, ?_⟩
    have h1 : taylorPolinom f (m + 1) x x = f x := by
      rw [taylorPolinom, Finset.sum_eq_single 0]
      · simp
      · intro k _ hk
        simp [zero_pow hk]
      · intro hmem
        exact absurd (Finset.mem_range.2 (Nat.succ_pos m)) hmem
    rw [h1, lagrangeMaradektag]
    simp
  · -- Az `x ≠ a` eset.
    have hxane : (x - a) ^ (m + 1) ≠ 0 := pow_ne_zero _ (sub_ne_zero.2 hxa)
    set C : ℝ := (f x - taylorPolinom f (m + 1) a x) / (x - a) ^ (m + 1) with hC
    set h : ℝ → ℝ := fun t => f x - (∑ k ∈ Finset.range (m + 1),
        nDerivalt k f t / (Nat.factorial k : ℝ) * (x - t) ^ k) - C * (x - t) ^ (m + 1)
      with hhdef
    have hCmul : C * (x - a) ^ (m + 1) = f x - taylorPolinom f (m + 1) a x := by
      rw [hC, div_mul_cancel₀ _ hxane]
    have hha : h a = 0 := by
      show f x - taylorPolinom f (m + 1) a x - C * (x - a) ^ (m + 1) = 0
      rw [hCmul, sub_self]
    have hhx : h x = 0 := by
      show f x - (∑ k ∈ Finset.range (m + 1),
          nDerivalt k f x / (Nat.factorial k : ℝ) * (x - x) ^ k)
          - C * (x - x) ^ (m + 1) = 0
      rw [Finset.sum_eq_single 0]
      · simp
      · intro k _ hk
        simp [zero_pow hk]
      · intro hmem
        exact absurd (Finset.mem_range.2 (Nat.succ_pos m)) hmem
    have hderiv : ∀ t ∈ Ioo c d, HasDerivAt h
        (-(nDerivalt (m + 1) f t / (Nat.factorial m : ℝ) * (x - t) ^ m)
          - C * (((m : ℝ) + 1) * (x - t) ^ m * (-1))) t := by
      intro t ht
      have h1 := hasDerivAt_taylorOsszeg m hf ht x
      have h2 : HasDerivAt (fun u : ℝ => (x - u) ^ (m + 1))
          (((m : ℝ) + 1) * (x - t) ^ m * (-1)) t := by
        have h3 : HasDerivAt (fun u : ℝ => x - u) (-1) t := by
          simpa using (hasDerivAt_id t).const_sub x
        simpa using h3.pow (m + 1)
      have key := ((hasDerivAt_const t (f x)).sub h1).sub (h2.const_mul C)
      simpa [hhdef, sub_sub] using key
    have hsub : Icc (min a x) (max a x) ⊆ Ioo c d := by
      intro y hy
      refine ⟨lt_of_lt_of_le (lt_min ha.1 hx.1) hy.1, lt_of_le_of_lt hy.2 (max_lt ha.2 hx.2)⟩
    have hpq : min a x < max a x := by
      rcases lt_or_gt_of_ne hxa with hlt | hlt
      · rw [min_eq_right hlt.le, max_eq_left hlt.le]; exact hlt
      · rw [min_eq_left hlt.le, max_eq_right hlt.le]; exact hlt
    have hends : h (min a x) = h (max a x) := by
      rcases lt_or_gt_of_ne hxa with hlt | hlt
      · rw [min_eq_right hlt.le, max_eq_left hlt.le, hha, hhx]
      · rw [min_eq_left hlt.le, max_eq_right hlt.le, hha, hhx]
    have hcont : ContinuousOn h (Icc (min a x) (max a x)) := fun y hy =>
      ((hderiv y (hsub hy)).continuousAt).continuousWithinAt
    obtain ⟨xi, hxi, hxi0⟩ := rolle hpq hcont
      (fun y hy => ⟨_, (derivalt_iff_hasDerivAt _ _ _).2
        (hderiv y (hsub (Ioo_subset_Icc_self hy)))⟩) hends
    have hximem : xi ∈ Ioo c d := hsub (Ioo_subset_Icc_self hxi)
    have hunique : -(nDerivalt (m + 1) f xi / (Nat.factorial m : ℝ) * (x - xi) ^ m)
        - C * (((m : ℝ) + 1) * (x - xi) ^ m * (-1)) = 0 :=
      derivalt_unicitas ((derivalt_iff_hasDerivAt _ _ _).2 (hderiv xi hximem)) hxi0
    -- `xi` szigorúan `a` és `x` között van
    have hxineq : xi ≠ x := by
      rcases lt_or_gt_of_ne hxa with hlt | hlt
      · rw [min_eq_right hlt.le] at hxi
        exact ne_of_gt hxi.1
      · rw [max_eq_right hlt.le] at hxi
        exact ne_of_lt hxi.2
    have hpow : (x - xi) ^ m ≠ 0 := pow_ne_zero _ (sub_ne_zero.2 (Ne.symm hxineq))
    have hm0 : (Nat.factorial m : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (Nat.factorial_ne_zero m)
    have hCval : C = nDerivalt (m + 1) f xi / (Nat.factorial (m + 1) : ℝ) := by
      have hfac : (Nat.factorial (m + 1) : ℝ) = ((m : ℝ) + 1) * (Nat.factorial m : ℝ) := by
        push_cast [Nat.factorial_succ]
        ring
      have h4 : (C * ((m : ℝ) + 1) - nDerivalt (m + 1) f xi / (Nat.factorial m : ℝ))
          * (x - xi) ^ m = 0 := by linarith [hunique, mul_comm ((x - xi) ^ m) C]
      have h5 : C * ((m : ℝ) + 1) - nDerivalt (m + 1) f xi / (Nat.factorial m : ℝ) = 0 := by
        rcases mul_eq_zero.1 h4 with h6 | h6
        · exact h6
        · exact absurd h6 hpow
      rw [hfac]
      field_simp at h5 ⊢
      linarith
    -- a `theta` paraméter
    refine ⟨(xi - a) / (x - a), ?_, ?_⟩
    · rcases lt_or_gt_of_ne hxa with hlt | hlt
      · rw [min_eq_right hlt.le, max_eq_left hlt.le] at hxi
        have h7 : (xi - a) / (x - a) = (a - xi) / (a - x) := by
          rw [← neg_div_neg_eq]; ring_nf
        rw [h7]
        exact ⟨div_pos (by linarith [hxi.2]) (by linarith),
          (div_lt_one (by linarith)).2 (by linarith [hxi.1])⟩
      · rw [min_eq_left hlt.le, max_eq_right hlt.le] at hxi
        exact ⟨div_pos (by linarith [hxi.1]) (by linarith),
          (div_lt_one (by linarith)).2 (by linarith [hxi.2])⟩
    · have hxa0 : x - a ≠ 0 := sub_ne_zero.2 hxa
      have harg : a + (xi - a) / (x - a) * (x - a) = xi := by
        field_simp
        ring
      rw [lagrangeMaradektag, harg, ← hCval]
      have := hCmul
      linarith [hCmul]


/-- **Maclaurin-formula.** A Taylor-formula `a = 0` esete. -/
theorem maclaurin_formula {f : ℝ → ℝ} {c d : ℝ} {n : ℕ} (hn : 0 < n)
    (hf : NszerDifferencialhato f n (Ioo c d)) (h0 : (0 : ℝ) ∈ Ioo c d) {x : ℝ}
    (hx : x ∈ Ioo c d) :
    ∃ theta ∈ Ioo (0 : ℝ) 1,
      f x = ∑ k ∈ Finset.range n, nDerivalt k f 0 / (Nat.factorial k : ℝ) * x ^ k
        + nDerivalt n f (theta * x) / (Nat.factorial n : ℝ) * x ^ n := by
  obtain ⟨theta, htheta, hEq⟩ := taylor_formula hn hf h0 hx
  refine ⟨theta, htheta, ?_⟩
  simpa [taylorPolinom, lagrangeMaradektag] using hEq

/-! ## 8.5.2. Tétel: szélső érték és monotonitás magasabbrendű differenciálhányadosokkal -/

/-- **Segédtétel (a derivált előjelhatása).** Ha `F(x₀) = 0`, `F` az `x₀` pontban
differenciálható, és `F'(x₀) = L ≠ 0`, akkor az `x₀` egy környezetében `F(y)` előjele
megegyezik `L·(y - x₀)` előjelével, azaz `F(y)·L·(y - x₀) > 0`.

*Bizonyítás.* A differenciálhányados Cauchy-féle definíciójában `ε = |L|`-t választva a
különbségi hányados `Q = F(y)/(y - x₀)` elég közel kerül `L`-hez ahhoz, hogy `Q·L > 0`
legyen; ekkor `F(y)·L·(y - x₀) = (Q·L)·(y - x₀)² > 0`. -/
theorem derivalt_elojel {F : ℝ → ℝ} {x₀ L : ℝ} (hF : Derivalt F x₀ L) (hF0 : F x₀ = 0)
    (hL : L ≠ 0) :
    ∃ δ > 0, ∀ y, |y - x₀| < δ → y ≠ x₀ → 0 < F y * L * (y - x₀) := by
  obtain ⟨δ, hδ, hlt⟩ := hF |L| (abs_pos.2 hL)
  refine ⟨δ, hδ, ?_⟩
  intro y hy hyne
  have hy0 : y - x₀ ≠ 0 := sub_ne_zero.2 hyne
  have h1 := hlt y hyne hy
  have hQ : kulonbsegiHanyados F x₀ y = F y / (y - x₀) := by
    rw [kulonbsegiHanyados, hF0, sub_zero]
  rw [hQ] at h1
  have hFy : F y = F y / (y - x₀) * (y - x₀) := by field_simp
  have hQL : 0 < F y / (y - x₀) * L := by
    rcases lt_or_gt_of_ne hL with hLneg | hLpos
    · rw [abs_of_neg hLneg] at h1
      have h2 := abs_lt.1 h1
      nlinarith [h2.1, h2.2]
    · rw [abs_of_pos hLpos] at h1
      have h2 := abs_lt.1 h1
      nlinarith [h2.1, h2.2]
  have hsq : 0 < (y - x₀) ^ 2 := by positivity
  have hfact : F y * L * (y - x₀) = (F y / (y - x₀) * L) * (y - x₀) ^ 2 := by
    field_simp
  rw [hfact]
  exact mul_pos hQL hsq

/-- **Segédtétel (az első el nem tűnő magasabbrendű differenciálhányados előjele).**
Ha `f⁽ⁱ⁾(x₀) = 0` minden `1 ≤ i ≤ N` esetén (`N ≥ 1`) és `L = f⁽ᴺ⁺¹⁾(x₀) ≠ 0`, akkor
az `x₀` egy környezetében `(f(x) - f(x₀))·L·(x - x₀)^{N+1} > 0`.

*Bizonyítás (a 8.5.2. Tétel könyvbeli gondolatmenete).* Az `N`-edrendű Taylor-formulában a
Taylor-polinom `f(x₀)`-ra zsugorodik, tehát
`f(x) - f(x₀) = f⁽ᴺ⁾(ξ)/N!·(x - x₀)ᴺ`, ahol `ξ = x₀ + θ(x - x₀)`. Az előző segédtétel
szerint `f⁽ᴺ⁾(ξ)·L·(ξ - x₀) > 0`, és `ξ - x₀ = θ(x - x₀)` ugyanolyan előjelű, mint
`x - x₀`; innen a szorzat pozitivitása már számolás kérdése. -/
theorem elso_nemnulla_derivalt_elojel {f : ℝ → ℝ} {c d x₀ : ℝ} {N : ℕ} (hN : 1 ≤ N)
    (hf : NszerDifferencialhato f (N + 1) (Ioo c d)) (hx₀ : x₀ ∈ Ioo c d)
    (hzero : ∀ i, 1 ≤ i → i ≤ N → nDerivalt i f x₀ = 0)
    (hL : nDerivalt (N + 1) f x₀ ≠ 0) :
    ∃ δ > 0, ∀ x, |x - x₀| < δ → x ≠ x₀ →
      0 < (f x - f x₀) * nDerivalt (N + 1) f x₀ * (x - x₀) ^ (N + 1) := by
  have hFd : Derivalt (nDerivalt N f) x₀ (nDerivalt (N + 1) f x₀) := hf N (by omega) x₀ hx₀
  have hF0 : nDerivalt N f x₀ = 0 := hzero N hN le_rfl
  obtain ⟨δ₁, hδ₁, hsign⟩ := derivalt_elojel hFd hF0 hL
  have hd1 : 0 < x₀ - c := sub_pos.2 hx₀.1
  have hd2 : 0 < d - x₀ := sub_pos.2 hx₀.2
  refine ⟨min δ₁ (min (x₀ - c) (d - x₀)), lt_min hδ₁ (lt_min hd1 hd2), ?_⟩
  intro x hx hxne
  have h1 : |x - x₀| < δ₁ := lt_of_lt_of_le hx (min_le_left _ _)
  have h2 : |x - x₀| < x₀ - c := lt_of_lt_of_le hx (le_trans (min_le_right _ _) (min_le_left _ _))
  have h3 : |x - x₀| < d - x₀ := lt_of_lt_of_le hx (le_trans (min_le_right _ _) (min_le_right _ _))
  have hxmem : x ∈ Ioo c d := by
    obtain ⟨ha1, ha2⟩ := abs_lt.1 h2
    obtain ⟨hb1, hb2⟩ := abs_lt.1 h3
    exact ⟨by linarith, by linarith⟩
  obtain ⟨theta, hth, hEq⟩ :=
    taylor_formula (n := N) (by omega) (hf.mono (by omega)) hx₀ hxmem
  set xi : ℝ := x₀ + theta * (x - x₀) with hxidef
  have hxisub : xi - x₀ = theta * (x - x₀) := by rw [hxidef]; ring
  have hxine : xi ≠ x₀ := by
    intro hc
    have hz : theta * (x - x₀) = 0 := by rw [← hxisub, hc, sub_self]
    rcases mul_eq_zero.1 hz with h | h
    · exact absurd h (ne_of_gt hth.1)
    · exact hxne (sub_eq_zero.1 h)
  have habs : |xi - x₀| < δ₁ := by
    rw [hxisub, abs_mul, abs_of_pos hth.1]
    nlinarith [hth.1, hth.2, h1, abs_nonneg (x - x₀)]
  have hs := hsign xi habs hxine
  rw [hxisub] at hs
  have key : 0 < nDerivalt N f xi * nDerivalt (N + 1) f x₀ * (x - x₀) := by
    nlinarith [hth.1, hs]
  have hpoly : taylorPolinom f N x₀ x = f x₀ := by
    rw [taylorPolinom, Finset.sum_eq_single 0]
    · simp
    · intro k hk hk0
      rw [hzero k (Nat.one_le_iff_ne_zero.2 hk0) (le_of_lt (Finset.mem_range.1 hk))]
      simp
    · intro hmem
      exact absurd (Finset.mem_range.2 (by omega)) hmem
  have hdiff : f x - f x₀ = nDerivalt N f xi / (Nat.factorial N : ℝ) * (x - x₀) ^ N := by
    rw [hEq, hpoly, lagrangeMaradektag]
    ring
  have hne : ((x - x₀) ^ N) ≠ 0 := pow_ne_zero _ (sub_ne_zero.2 hxne)
  have hpos2 : 0 < ((x - x₀) ^ N) ^ 2 := by positivity
  have hfacpos : (0 : ℝ) < (Nat.factorial N : ℝ) := by
    exact_mod_cast Nat.factorial_pos N
  rw [hdiff]
  have hrw : nDerivalt N f xi / (Nat.factorial N : ℝ) * (x - x₀) ^ N
        * nDerivalt (N + 1) f x₀ * (x - x₀) ^ (N + 1)
      = (nDerivalt N f xi * nDerivalt (N + 1) f x₀ * (x - x₀)) * ((x - x₀) ^ N) ^ 2
        / (Nat.factorial N : ℝ) := by
    rw [pow_succ]
    field_simp
  rw [hrw]
  exact div_pos (mul_pos key hpos2) hfacpos

/-- **8.5.2. Tétel (első fele, minimum).** Ha `f⁽ⁱ⁾(x₀) = 0` minden `1 ≤ i ≤ 2k-1` esetén
(`k ≥ 1`), és `f⁽²ᵏ⁾(x₀) > 0`, akkor az `f` függvénynek az `x₀` helyen (szigorú) lokális
minimuma van.

*Bizonyítás (a könyv gondolatmenete).* A `(2k-1)`-edrendű Taylor-formula szerint
`f(x) - f(x₀) = f⁽²ᵏ⁻¹⁾(ξ)/(2k-1)!·(x-x₀)^{2k-1}`, ahol `ξ` az `x₀` és `x` közötti pont.
Mivel `f⁽²ᵏ⁻¹⁾(x₀) = 0` és `(f⁽²ᵏ⁻¹⁾)'(x₀) = f⁽²ᵏ⁾(x₀) > 0`, az `x₀` egy környezetében
`f⁽²ᵏ⁻¹⁾(ξ)` előjele megegyezik `ξ - x₀` előjelével, ez pedig `(x-x₀)^{2k-1}` előjelével;
a szorzat tehát pozitív. -/
theorem szelsoertek_paros_rendu_minimum {f : ℝ → ℝ} {c d x₀ : ℝ} {k : ℕ} (hk : 0 < k)
    (hf : NszerDifferencialhato f (2 * k) (Ioo c d)) (hx₀ : x₀ ∈ Ioo c d)
    (hzero : ∀ i, 1 ≤ i → i < 2 * k → nDerivalt i f x₀ = 0)
    (hpos : 0 < nDerivalt (2 * k) f x₀) :
    ∃ δ > 0, ∀ x, |x - x₀| < δ → x ≠ x₀ → f x₀ < f x := by
  obtain ⟨N, hN⟩ : ∃ N, 2 * k = N + 1 := ⟨2 * k - 1, by omega⟩
  rw [hN] at hf hpos hzero
  obtain ⟨δ, hδ, hkey⟩ :=
    elso_nemnulla_derivalt_elojel (by omega) hf hx₀
      (fun i h1 h2 => hzero i h1 (by omega)) (ne_of_gt hpos)
  refine ⟨δ, hδ, ?_⟩
  intro x hx hxne
  have hkx := hkey x hx hxne
  have hne : (x - x₀) ≠ 0 := sub_ne_zero.2 hxne
  have hp : 0 < (x - x₀) ^ (N + 1) := by
    have hNk : N + 1 = 2 * k := hN.symm
    rw [hNk, pow_mul]
    exact pow_pos (by positivity) k
  nlinarith [hkx, mul_pos hpos hp]

/-- **8.5.2. Tétel (első fele, maximum).** Ha `f⁽ⁱ⁾(x₀) = 0` minden `1 ≤ i ≤ 2k-1` esetén
(`k ≥ 1`), és `f⁽²ᵏ⁾(x₀) < 0`, akkor az `f` függvénynek az `x₀` helyen (szigorú) lokális
maximuma van. -/
theorem szelsoertek_paros_rendu_maximum {f : ℝ → ℝ} {c d x₀ : ℝ} {k : ℕ} (hk : 0 < k)
    (hf : NszerDifferencialhato f (2 * k) (Ioo c d)) (hx₀ : x₀ ∈ Ioo c d)
    (hzero : ∀ i, 1 ≤ i → i < 2 * k → nDerivalt i f x₀ = 0)
    (hneg : nDerivalt (2 * k) f x₀ < 0) :
    ∃ δ > 0, ∀ x, |x - x₀| < δ → x ≠ x₀ → f x < f x₀ := by
  obtain ⟨N, hN⟩ : ∃ N, 2 * k = N + 1 := ⟨2 * k - 1, by omega⟩
  rw [hN] at hf hneg hzero
  obtain ⟨δ, hδ, hkey⟩ :=
    elso_nemnulla_derivalt_elojel (by omega) hf hx₀
      (fun i h1 h2 => hzero i h1 (by omega)) (ne_of_lt hneg)
  refine ⟨δ, hδ, ?_⟩
  intro x hx hxne
  have hkx := hkey x hx hxne
  have hne : (x - x₀) ≠ 0 := sub_ne_zero.2 hxne
  have hp : 0 < (x - x₀) ^ (N + 1) := by
    have hNk : N + 1 = 2 * k := hN.symm
    rw [hNk, pow_mul]
    exact pow_pos (by positivity) k
  nlinarith [hkx, mul_pos (neg_pos.2 hneg) hp]

/-- **8.5.2. Tétel (második fele).** Ha `f⁽ⁱ⁾(x₀) = 0` minden `1 ≤ i ≤ 2k` esetén
(`k ≥ 1`), és `f⁽²ᵏ⁺¹⁾(x₀) > 0`, akkor a függvény az `x₀` valamely környezetében növekedő:
`x < x₀` esetén `f(x) < f(x₀)`, `x > x₀` esetén pedig `f(x₀) < f(x)`. -/
theorem monoton_paratlan_rendu {f : ℝ → ℝ} {c d x₀ : ℝ} {k : ℕ} (hk : 0 < k)
    (hf : NszerDifferencialhato f (2 * k + 1) (Ioo c d)) (hx₀ : x₀ ∈ Ioo c d)
    (hzero : ∀ i, 1 ≤ i → i < 2 * k + 1 → nDerivalt i f x₀ = 0)
    (hpos : 0 < nDerivalt (2 * k + 1) f x₀) :
    ∃ δ > 0, ∀ x, |x - x₀| < δ → (x < x₀ → f x < f x₀) ∧ (x₀ < x → f x₀ < f x) := by
  obtain ⟨δ, hδ, hkey⟩ :=
    elso_nemnulla_derivalt_elojel (N := 2 * k) (by omega) hf hx₀
      (fun i h1 h2 => hzero i h1 (by omega)) (ne_of_gt hpos)
  refine ⟨δ, hδ, ?_⟩
  intro x hx
  constructor
  · intro hlt
    have hkx := hkey x hx (ne_of_lt hlt)
    have hp : (x - x₀) ^ (2 * k + 1) < 0 :=
      Odd.pow_neg (Nat.odd_iff.2 (by omega)) (by linarith)
    nlinarith [hkx, mul_neg_of_pos_of_neg hpos hp]
  · intro hgt
    have hkx := hkey x hx (ne_of_gt hgt)
    have hp : 0 < (x - x₀) ^ (2 * k + 1) := pow_pos (by linarith) _
    nlinarith [hkx, mul_pos hpos hp]

end Leindler.Ch07
