import Mathlib
import Analizis.Ch06a_Differencialhatosag
import Analizis.Ch06b_ElemiDerivaltak

/-!
# Leindler László: Analízis — 7. fejezet (a): Magasabbrendű differenciálhányadosok, Leibniz-formula

A könyv 105–106. oldalának formalizálása:

* **7.0.1. Definíció** — a magasabbrendű differenciálhányados fogalma,
* az összeg magasabbrendű differenciálhányadosa,
* **7.1.1. Tétel** — a **Leibniz-formula** a szorzat `n`-edik differenciálhányadosára.

A 7.2. pont (Taylor-formula) a `Ch07b_TaylorFormula` modulban található.

A differenciálhányados fogalma végig a könyv 6.1.3. Definíciója (`Leindler.Ch06.Derivalt`),
a magasabbrendű differenciálhányadosokat pedig ennek ismételt alkalmazásával kapjuk.
-/

namespace Leindler.Ch07

open Set Leindler Leindler.Ch05 Leindler.Ch06

/-! ## 7.0.1. Definíció: magasabbrendű differenciálhányadosok -/

/-- **7.0.1. Definíció.** Ha az `f(x)` függvény differenciálható, és `f'(x)` ismét
differenciálható, akkor az újabb differenciálhányados-függvény az `f` *második*
differenciálhányadosa; az eljárást folytatva jutunk a magasabbrendű
differenciálhányadosokhoz. Az `n`-edrendű differenciálhányados-függvény jele `f⁽ⁿ⁾`.

Itt `nDerivalt n f` jelöli az `f⁽ⁿ⁾` függvényt; a definíció rekurzív:
`f⁽⁰⁾ = f` és `f⁽ⁿ⁺¹⁾ = (f⁽ⁿ⁾)'`. -/
noncomputable def nDerivalt : ℕ → (ℝ → ℝ) → (ℝ → ℝ)
  | 0, f => f
  | n + 1, f => deriv (nDerivalt n f)

@[simp] theorem nDerivalt_zero (f : ℝ → ℝ) : nDerivalt 0 f = f := rfl

theorem nDerivalt_succ (n : ℕ) (f : ℝ → ℝ) :
    nDerivalt (n + 1) f = deriv (nDerivalt n f) := rfl

/-- A könyv magasabbrendű differenciálhányadosa megegyezik a Mathlib `iteratedDeriv`
fogalmával. -/
theorem nDerivalt_eq_iteratedDeriv (n : ℕ) (f : ℝ → ℝ) :
    nDerivalt n f = iteratedDeriv n f := by
  induction n with
  | zero => simp [iteratedDeriv_zero]
  | succ k ih => rw [nDerivalt_succ, ih, iteratedDeriv_succ]

theorem nDerivalt_succ' (n : ℕ) (f : ℝ → ℝ) :
    nDerivalt (n + 1) f = nDerivalt n (deriv f) := by
  simp [nDerivalt_eq_iteratedDeriv, iteratedDeriv_succ']

/-- Az `f` függvény a `s` halmazon *`n`-szer differenciálható* (a könyv értelmében), ha
minden `k < n` esetén az `f⁽ᵏ⁾` függvény `s` minden pontjában differenciálható, és ott a
differenciálhányadosa `f⁽ᵏ⁺¹⁾`. -/
def NszerDifferencialhato (f : ℝ → ℝ) (n : ℕ) (s : Set ℝ) : Prop :=
  ∀ k < n, ∀ x ∈ s, Derivalt (nDerivalt k f) x (nDerivalt (k + 1) f x)

theorem NszerDifferencialhato.mono {f : ℝ → ℝ} {m n : ℕ} {s : Set ℝ}
    (h : NszerDifferencialhato f n s) (hmn : m ≤ n) : NszerDifferencialhato f m s :=
  fun k hk x hx => h k (lt_of_lt_of_le hk hmn) x hx

theorem NszerDifferencialhato.subset {f : ℝ → ℝ} {n : ℕ} {s t : Set ℝ}
    (h : NszerDifferencialhato f n s) (hts : t ⊆ s) : NszerDifferencialhato f n t :=
  fun k hk x hx => h k hk x (hts hx)

/-- Ha `f` a `s` halmazon `n`-szer differenciálható, akkor `f⁽ᵏ⁾` differenciálható `s`
pontjaiban minden `k < n` esetén (Mathlib-alak). -/
theorem NszerDifferencialhato.differentiableAt {f : ℝ → ℝ} {n : ℕ} {s : Set ℝ}
    (h : NszerDifferencialhato f n s) {k : ℕ} (hk : k < n) {x : ℝ} (hx : x ∈ s) :
    DifferentiableAt ℝ (nDerivalt k f) x :=
  ((derivalt_iff_hasDerivAt _ _ _).1 (h k hk x hx)).differentiableAt

/-- A magasabbrendű differenciálhányados additív: `(f ± g)⁽ⁿ⁾ = f⁽ⁿ⁾ ± g⁽ⁿ⁾`. -/
theorem nDerivalt_add {f g : ℝ → ℝ} {n : ℕ} {s : Set ℝ} (hs : IsOpen s)
    (hf : NszerDifferencialhato f n s) (hg : NszerDifferencialhato g n s) :
    (∀ x ∈ s, nDerivalt n (fun y => f y + g y) x = nDerivalt n f x + nDerivalt n g x) ∧
      NszerDifferencialhato (fun y => f y + g y) n s := by
  induction n with
  | zero => exact ⟨fun _ _ => rfl, fun k hk => absurd hk (Nat.not_lt_zero k)⟩
  | succ n ih =>
    obtain ⟨heq, hd⟩ := ih (hf.mono (Nat.le_succ n)) (hg.mono (Nat.le_succ n))
    have hkey : ∀ x ∈ s, HasDerivAt (nDerivalt n (fun y => f y + g y))
        (nDerivalt (n + 1) f x + nDerivalt (n + 1) g x) x := by
      intro x hx
      have hfx : HasDerivAt (nDerivalt n f) (nDerivalt (n + 1) f x) x :=
        (derivalt_iff_hasDerivAt _ _ _).1 (hf n (Nat.lt_succ_self n) x hx)
      have hgx : HasDerivAt (nDerivalt n g) (nDerivalt (n + 1) g x) x :=
        (derivalt_iff_hasDerivAt _ _ _).1 (hg n (Nat.lt_succ_self n) x hx)
      have hev : (nDerivalt n (fun y => f y + g y))
          =ᶠ[nhds x] (fun y => nDerivalt n f y + nDerivalt n g y) :=
        Filter.eventuallyEq_of_mem (hs.mem_nhds hx) (fun y hy => heq y hy)
      exact (hfx.add hgx).congr_of_eventuallyEq hev
    refine ⟨fun x hx => ?_, fun k hk x hx => ?_⟩
    · rw [nDerivalt_succ]
      exact (hkey x hx).deriv
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk' | rfl
      · exact hd k hk' x hx
      · have h1 := hkey x hx
        have h2 : nDerivalt (k + 1) (fun y => f y + g y) x
            = nDerivalt (k + 1) f x + nDerivalt (k + 1) g x := by
          rw [nDerivalt_succ]; exact h1.deriv
        rw [h2]
        exact (derivalt_iff_hasDerivAt _ _ _).2 h1

/-! ## 7.1. Leibniz-formula -/

/-- Az indukciós lépés kombinatorikus magva: a Pascal-azonosság
`(n choose i) + (n choose (i-1)) = (n+1 choose i)` összegző alakja. -/
theorem leibniz_binom_step (n : ℕ) (X : ℕ → ℝ) :
    (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * X i)
      + (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) * X (i + 1))
      = ∑ i ∈ Finset.range (n + 2), ((n + 1).choose i : ℝ) * X i := by
  rw [Finset.sum_range_succ' (fun i => ((n + 1).choose i : ℝ) * X i) (n + 1)]
  rw [Finset.sum_range_succ' (fun i => (n.choose i : ℝ) * X i) n]
  have h1 : ∑ i ∈ Finset.range (n + 1), ((n + 1).choose (i + 1) : ℝ) * X (i + 1)
      = ∑ i ∈ Finset.range (n + 1),
          ((n.choose i : ℝ) * X (i + 1) + (n.choose (i + 1) : ℝ) * X (i + 1)) := by
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Nat.choose_succ_succ]
    push_cast
    ring
  have h2 : ∑ i ∈ Finset.range n, (n.choose (i + 1) : ℝ) * X (i + 1)
      = ∑ i ∈ Finset.range (n + 1), (n.choose (i + 1) : ℝ) * X (i + 1) := by
    rw [Finset.sum_range_succ]
    simp [Nat.choose_succ_self]
  rw [h1, Finset.sum_add_distrib, h2]
  simp
  ring

/-- **7.1.1. Tétel (Leibniz-formula).** Ha `f(x)` és `g(x)` `n`-szer differenciálhatók,
akkor `f(x)g(x)` is `n`-szer differenciálható, és

`(fg)⁽ⁿ⁾ = ∑_{i=0}^{n} (n choose i) f⁽ⁿ⁻ⁱ⁾ g⁽ⁱ⁾`.

*Bizonyítás (a könyv szerint).* Teljes indukció `n` szerint. `n = 1`-re ez a szorzat
deriválási szabálya. Az `n`-ről `n+1`-re lépéskor a szorzatszabály és az indexeltolás után
a `(n choose i) + (n choose (i-1)) = (n+1 choose i)` azonosságot használjuk. -/
theorem leibniz_formula {f g : ℝ → ℝ} {n : ℕ} {s : Set ℝ} (hs : IsOpen s)
    (hf : NszerDifferencialhato f n s) (hg : NszerDifferencialhato g n s) :
    (∀ x ∈ s, nDerivalt n (fun y => f y * g y) x =
        ∑ i ∈ Finset.range (n + 1),
          (n.choose i : ℝ) * nDerivalt (n - i) f x * nDerivalt i g x) ∧
      NszerDifferencialhato (fun y => f y * g y) n s := by
  induction n with
  | zero => exact ⟨fun _ _ => by simp, fun k hk => absurd hk (Nat.not_lt_zero k)⟩
  | succ n ih =>
    obtain ⟨heq, hd⟩ := ih (hf.mono (Nat.le_succ n)) (hg.mono (Nat.le_succ n))
    have hkey : ∀ x ∈ s, HasDerivAt (nDerivalt n (fun y => f y * g y))
        (∑ i ∈ Finset.range (n + 2),
          ((n + 1).choose i : ℝ) * nDerivalt (n + 1 - i) f x * nDerivalt i g x) x := by
      intro x hx
      have hterm : ∀ i ∈ Finset.range (n + 1),
          HasDerivAt (fun y => (n.choose i : ℝ) * nDerivalt (n - i) f y * nDerivalt i g y)
            ((n.choose i : ℝ) * (nDerivalt (n + 1 - i) f x * nDerivalt i g x)
              + (n.choose i : ℝ)
                  * (nDerivalt (n + 1 - (i + 1)) f x * nDerivalt (i + 1) g x)) x := by
        intro i hi
        have hi' : i ≤ n := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
        have hfd : HasDerivAt (nDerivalt (n - i) f) (nDerivalt (n - i + 1) f x) x :=
          (derivalt_iff_hasDerivAt _ _ _).1 (hf (n - i) (by omega) x hx)
        have hgd : HasDerivAt (nDerivalt i g) (nDerivalt (i + 1) g x) x :=
          (derivalt_iff_hasDerivAt _ _ _).1 (hg i (by omega) x hx)
        have hprod := (hfd.mul hgd).const_mul ((n.choose i : ℝ))
        have e1 : n - i + 1 = n + 1 - i := by omega
        have e2 : n - i = n + 1 - (i + 1) := by omega
        rw [e1, e2] at hprod
        simpa [mul_assoc, mul_add] using hprod
      have hsum0 := HasDerivAt.sum hterm
      have hfun : (∑ i ∈ Finset.range (n + 1),
            fun y => (n.choose i : ℝ) * nDerivalt (n - i) f y * nDerivalt i g y)
          = fun y => ∑ i ∈ Finset.range (n + 1),
              (n.choose i : ℝ) * nDerivalt (n - i) f y * nDerivalt i g y := by
        funext y
        simp [Finset.sum_apply]
      rw [hfun] at hsum0
      have hsum : HasDerivAt
          (fun y => ∑ i ∈ Finset.range (n + 1),
            (n.choose i : ℝ) * nDerivalt (n - i) f y * nDerivalt i g y)
          (∑ i ∈ Finset.range (n + 1),
            ((n.choose i : ℝ) * (nDerivalt (n + 1 - i) f x * nDerivalt i g x)
              + (n.choose i : ℝ)
                  * (nDerivalt (n - i) f x * nDerivalt (i + 1) g x))) x := by
        simpa [Nat.succ_sub_succ] using hsum0
      have hev : (nDerivalt n (fun y => f y * g y)) =ᶠ[nhds x]
          (fun y => ∑ i ∈ Finset.range (n + 1),
            (n.choose i : ℝ) * nDerivalt (n - i) f y * nDerivalt i g y) :=
        Filter.eventuallyEq_of_mem (hs.mem_nhds hx) (fun y hy => heq y hy)
      have hval : (∑ i ∈ Finset.range (n + 1),
            ((n.choose i : ℝ) * (nDerivalt (n + 1 - i) f x * nDerivalt i g x)
              + (n.choose i : ℝ)
                  * (nDerivalt (n - i) f x * nDerivalt (i + 1) g x)))
          = ∑ i ∈ Finset.range (n + 2),
              ((n + 1).choose i : ℝ) * nDerivalt (n + 1 - i) f x * nDerivalt i g x := by
        rw [Finset.sum_add_distrib]
        have hstep := leibniz_binom_step n
          (fun i => nDerivalt (n + 1 - i) f x * nDerivalt i g x)
        simpa [mul_assoc, Nat.succ_sub_succ] using hstep
      rw [← hval]
      exact hsum.congr_of_eventuallyEq hev
    refine ⟨fun x hx => ?_, fun k hk x hx => ?_⟩
    · rw [nDerivalt_succ]
      exact (hkey x hx).deriv
    · rcases Nat.lt_succ_iff_lt_or_eq.1 hk with hk' | rfl
      · exact hd k hk' x hx
      · have h1 := hkey x hx
        have h2 : nDerivalt (k + 1) (fun y => f y * g y) x
            = ∑ i ∈ Finset.range (k + 2),
                ((k + 1).choose i : ℝ) * nDerivalt (k + 1 - i) f x * nDerivalt i g x := by
          rw [nDerivalt_succ]; exact h1.deriv
        rw [h2]
        exact (derivalt_iff_hasDerivAt _ _ _).2 h1

end Leindler.Ch07
