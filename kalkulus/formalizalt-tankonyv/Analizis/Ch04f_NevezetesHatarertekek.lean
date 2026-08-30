import Analizis.Ch04c_Konvergenciakriteriumok

/-!
# Leindler László: Analízis — 4.7. Nevezetes sorozatok határértékei (folytatás)

Ez a modul a 4.7. szakasz hátralévő részét formalizálja (19–22. oldal):

* **4.7.3. Tétel** ‑ a `qⁿ` sorozat divergens esete (`|q| > 1`),
* **4.7.5. Definíció** ‑ oszcilláló sorozat, **4.7.6. Példák**,
* **4.7.7. Példa** ‑ `ⁿ√a → 1`, ha `a > 0`,
* **4.7.8. Példa** ‑ `aⁿ/n! → 0` bármely valós `a`-ra,
* **4.7.9. Példa** ‑ `ⁿ√n → 1`.

A `4.7.1.`, `4.7.2.`, `4.7.3. (a), (β)` és `4.7.4.` (Bernoulli-egyenlőtlenség) állítások a
`Ch04a_SorozatokAlapok` modulban szerepelnek.

**Jelölés.** Az `ⁿ√a` gyököt a valós kitevős hatvány (`Real.rpow`) segítségével
`a ^ (1/n)` alakban írjuk; a könyv is megjegyzi, hogy `ⁿ√a` pontos jelentését és
létezését csak később (5.7., 5.10. szakasz) tisztázza.
-/

namespace Leindler
namespace Ch04

open scoped BigOperators
open scoped Nat

/-! ## 4.7.3. Tétel — a divergens eset -/

/-- **4.7.3. Tétel (γ) rész.** Ha `|q| > 1`, akkor a `{qⁿ}` sorozat divergens.

*Bizonyítás.* A Bernoulli-egyenlőtlenség szerint `q²ⁿ = (q²)ⁿ ≥ 1 + n(q² - 1)`, azaz a
sorozat `{q²ⁿ}` részsorozata minden határon túl nő, tehát a sorozat nem korlátos.  A
4.8.1. Tétel szerint viszont a konvergens sorozat korlátos, így `{qⁿ}` nem lehet
konvergens. -/
theorem q_hatvany_divergens {q : ℝ} (hq : 1 < |q|) : Divergens (fun n : ℕ => q ^ n) := by
  intro hkonv
  obtain ⟨K, hK⟩ := (korlatos_iff_abs _).mp (konvergens_korlatos hkonv)
  -- `|q|² > 1`, ezért a Bernoulli-egyenlőtlenség szerint `|q|^(2n) ≥ 1 + n(|q|² - 1) → ∞`.
  have hq2 : 1 < |q| ^ 2 := by nlinarith [abs_nonneg q]
  obtain ⟨N, hN⟩ := exists_nat_gt ((K - 1) / (|q| ^ 2 - 1))
  have hpos : (0 : ℝ) < |q| ^ 2 - 1 := by linarith
  have hlt : K - 1 < (N : ℝ) * (|q| ^ 2 - 1) := by
    have := (div_lt_iff₀ hpos).mp hN
    linarith
  have hber : 1 + (N : ℝ) * (|q| ^ 2 - 1) ≤ (|q| ^ 2) ^ N :=
    bernoulli' (by positivity) N
  have hK' : |q ^ (2 * N)| ≤ K := hK (2 * N)
  have hrw : |q ^ (2 * N)| = (|q| ^ 2) ^ N := by
    rw [abs_pow, pow_mul]
  rw [hrw] at hK'
  linarith

/-! ## 4.7.5. Oszcilláló sorozatok -/

/-- **4.7.5. Definíció.** Az `{aₙ}` sorozatot *oszcilláló sorozatnak* nevezzük, ha az
egymás után következő tagok előjele különböző. -/
def Oszcillalo (a : Sorozat) : Prop := ∀ n, a n * a (n + 1) < 0

/-- **4.7.6. Példa (1).** Ha `q < 0`, akkor `{qⁿ}` oszcilláló sorozat. -/
theorem oszcillalo_q_hatvany {q : ℝ} (hq : q < 0) : Oszcillalo (fun n => q ^ n) := by
  intro n
  have h : q ^ n * q ^ (n + 1) = q ^ (2 * n + 1) := by ring
  rw [h]
  exact Odd.pow_neg ⟨n, by ring⟩ hq

/-- **4.7.6. Példa (2).** Ha `aₙ > 0` minden `n`-re, akkor `{(-1)ⁿaₙ}` oszcilláló
sorozat. -/
theorem oszcillalo_valto_elojel {a : Sorozat} (ha : ∀ n, 0 < a n) :
    Oszcillalo (fun n => (-1 : ℝ) ^ n * a n) := by
  intro n
  have hsign : ((-1 : ℝ) ^ n) * ((-1 : ℝ) ^ (n + 1)) = -1 := by
    rw [← pow_add, show n + (n + 1) = 2 * n + 1 by ring, pow_succ, pow_mul]
    norm_num
  have h : ((-1 : ℝ) ^ n * a n) * ((-1 : ℝ) ^ (n + 1) * a (n + 1))
      = -((a n) * a (n + 1)) := by
    calc ((-1 : ℝ) ^ n * a n) * ((-1 : ℝ) ^ (n + 1) * a (n + 1))
        = (((-1 : ℝ) ^ n) * ((-1 : ℝ) ^ (n + 1))) * (a n * a (n + 1)) := by ring
      _ = -((a n) * a (n + 1)) := by rw [hsign]; ring
  simp only [h, neg_lt_zero]
  exact mul_pos (ha n) (ha (n + 1))

/-! ## 4.7.7. Példa — `ⁿ√a → 1` -/

/-- Segédállítás: `a ≥ 1` esetén `1 ≤ ⁿ√a ≤ 1 + (a-1)/n` minden `n ≥ 1`-re.

A könyv gondolatmenete: a Bernoulli-egyenlőtlenség szerint `a = (ⁿ√a)ⁿ ≥ 1 + n(ⁿ√a - 1)`,
amiből `ⁿ√a - 1 ≤ (a-1)/n` adódik. -/
theorem gyok_becsles {a : ℝ} (ha : 1 ≤ a) {n : ℕ} (hn : 1 ≤ n) :
    1 ≤ a ^ ((n : ℝ)⁻¹) ∧ a ^ ((n : ℝ)⁻¹) - 1 ≤ (a - 1) / n := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hx1 : 1 ≤ a ^ ((n : ℝ)⁻¹) := Real.one_le_rpow ha (by positivity)
  refine ⟨hx1, ?_⟩
  have hxn : (a ^ ((n : ℝ)⁻¹)) ^ n = a := by
    rw [← Real.rpow_natCast (a ^ ((n : ℝ)⁻¹)) n, ← Real.rpow_mul (by linarith)]
    rw [inv_mul_cancel₀ (ne_of_gt hn0), Real.rpow_one]
  have hber : 1 + (n : ℝ) * (a ^ ((n : ℝ)⁻¹) - 1) ≤ (a ^ ((n : ℝ)⁻¹)) ^ n := by
    have h := bernoulli (α := a ^ ((n : ℝ)⁻¹) - 1) (by linarith) n
    have hrw : 1 + (a ^ ((n : ℝ)⁻¹) - 1) = a ^ ((n : ℝ)⁻¹) := by ring
    rwa [hrw] at h
  rw [hxn] at hber
  rw [le_div_iff₀ hn0]
  linarith

/-- **4.7.7. Példa.** `ⁿ√a → 1`, ha `a > 0`.

*Bizonyítás.* Az `a = 1` eset nyilvánvaló.  Ha `a > 1`, akkor a Bernoulli-egyenlőtlenség
szerint `0 ≤ ⁿ√a - 1 ≤ (a-1)/n`, s a jobb oldal nullához tart, tehát a rendőrelv
alkalmazható.  Ha `0 < a < 1`, akkor `1/a > 1`, és `ⁿ√a = 1 / ⁿ√(1/a)`, így az előző eset
és a hányados határértékére vonatkozó tétel adja az állítást. -/
theorem gyok_a_hatarerteke {a : ℝ} (ha : 0 < a) :
    HatarErtek (fun n : ℕ => a ^ ((n : ℝ)⁻¹)) 1 := by
  by_cases ha1 : 1 ≤ a
  · -- `a ≥ 1`
    intro ε hε
    obtain ⟨N, hN⟩ := exists_nat_gt ((a - 1) / ε)
    refine ⟨max N 1, fun n hn => ?_⟩
    have hn1 : 1 ≤ n := le_of_lt (lt_of_le_of_lt (le_max_right N 1) hn)
    have hnN : (N : ℝ) < n := by
      exact_mod_cast lt_of_le_of_lt (le_max_left N 1) hn
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
    obtain ⟨hx1, hx2⟩ := gyok_becsles ha1 hn1
    have hlt : (a - 1) / n < ε := by
      rcases eq_or_lt_of_le (by linarith : (1 : ℝ) ≤ a) with h | h
      · rw [← h]; simpa using hε
      · have h1 : (a - 1) / ε < n := lt_trans hN hnN
        rw [div_lt_iff₀ hn0]
        rw [div_lt_iff₀ hε] at h1
        linarith
    rw [abs_lt]
    constructor <;> linarith
  · -- `0 < a < 1`
    have hinv : (1 : ℝ) ≤ a⁻¹ := by
      rw [le_inv_comm₀ (by norm_num) ha]
      linarith
    have hb : HatarErtek (fun n : ℕ => a⁻¹ ^ ((n : ℝ)⁻¹)) 1 := by
      intro ε hε
      obtain ⟨N, hN⟩ := exists_nat_gt ((a⁻¹ - 1) / ε)
      refine ⟨max N 1, fun n hn => ?_⟩
      have hn1 : 1 ≤ n := le_of_lt (lt_of_le_of_lt (le_max_right N 1) hn)
      have hnN : (N : ℝ) < n := by
        exact_mod_cast lt_of_le_of_lt (le_max_left N 1) hn
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn1
      obtain ⟨hx1, hx2⟩ := gyok_becsles hinv hn1
      have hlt : (a⁻¹ - 1) / n < ε := by
        rcases eq_or_lt_of_le hinv with h | h
        · rw [← h]; simpa using hε
        · have h1 : (a⁻¹ - 1) / ε < n := lt_trans hN hnN
          rw [div_lt_iff₀ hn0]
          rw [div_lt_iff₀ hε] at h1
          linarith
      rw [abs_lt]
      constructor <;> linarith
    push_neg at ha1
    have hdiv := hatarErtek_div (a := fun _ : ℕ => (1 : ℝ))
      (b := fun n : ℕ => a⁻¹ ^ ((n : ℝ)⁻¹)) (allando_hatarerteke 1) hb one_ne_zero
    have heq : (fun n : ℕ => (1 : ℝ) / a⁻¹ ^ ((n : ℝ)⁻¹)) = fun n : ℕ => a ^ ((n : ℝ)⁻¹) := by
      funext n
      rw [Real.inv_rpow (le_of_lt ha), one_div, inv_inv]
    rw [heq] at hdiv
    simpa using hdiv

/-! ## 4.7.8. Példa — `aⁿ/n! → 0` -/

/-- Segédállítás (a könyv `K/n` becslése).  Ha `1 ≤ k` és `|a| ≤ k`, akkor minden `n ≥ k`
esetén `|a|ⁿ/n! ≤ (|a|ᵏ/k!) · (k/n)`.

*Bizonyítás.* Teljes indukció `n` szerint: `n = k`-ra egyenlőség áll, a lépésnél pedig
`|a|ⁿ⁺¹/(n+1)! = (|a|ⁿ/n!)·(|a|/(n+1)) ≤ (|a|ᵏ/k!)·(k/n)·(k/(n+1)) ≤ (|a|ᵏ/k!)·(k/(n+1))`,
mert `k ≤ n`. -/
theorem faktorialis_becsles {a : ℝ} {k : ℕ} (hk : 1 ≤ k) (hak : |a| ≤ k) :
    ∀ n, k ≤ n → |a| ^ n / (n ! : ℝ) ≤ (|a| ^ k / (k ! : ℝ)) * (k / n) := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
      have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
      rw [div_self (ne_of_gt hk0), mul_one]
  | succ n hkn ih =>
      have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
      have hn0 : (0 : ℝ) < n := lt_of_lt_of_le hk0 (by exact_mod_cast hkn)
      have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by linarith
      have hfac : (0 : ℝ) < (n ! : ℝ) := by exact_mod_cast n.factorial_pos
      have hstep : |a| ^ (n + 1) / ((n + 1)! : ℝ)
          = (|a| ^ n / (n ! : ℝ)) * (|a| / ((n : ℝ) + 1)) := by
        rw [Nat.factorial_succ]
        push_cast
        field_simp
        ring
      rw [hstep]
      have hK0 : (0 : ℝ) ≤ |a| ^ k / (k ! : ℝ) := by positivity
      have h1 : (|a| ^ n / (n ! : ℝ)) * (|a| / ((n : ℝ) + 1))
          ≤ ((|a| ^ k / (k ! : ℝ)) * (k / n)) * (|a| / ((n : ℝ) + 1)) := by
        apply mul_le_mul_of_nonneg_right ih
        positivity
      refine le_trans h1 ?_
      have hkn' : (k : ℝ) ≤ n := by exact_mod_cast hkn
      have h2 : ((k : ℝ) / n) * (|a| / ((n : ℝ) + 1)) ≤ (k : ℝ) / ((n : ℝ) + 1) := by
        rw [div_mul_div_comm, div_le_div_iff₀ (by positivity) hn1]
        have hle : |a| ≤ (n : ℝ) := le_trans hak hkn'
        have h3 : (k : ℝ) * |a| ≤ (k : ℝ) * n := by nlinarith [abs_nonneg a]
        have h4 := mul_le_mul_of_nonneg_right h3 (le_of_lt hn1)
        nlinarith [h4]
      calc ((|a| ^ k / (k ! : ℝ)) * ((k : ℝ) / n)) * (|a| / ((n : ℝ) + 1))
          = (|a| ^ k / (k ! : ℝ)) * (((k : ℝ) / n) * (|a| / ((n : ℝ) + 1))) := by ring
        _ ≤ (|a| ^ k / (k ! : ℝ)) * ((k : ℝ) / ((n : ℝ) + 1)) :=
            mul_le_mul_of_nonneg_left h2 hK0
        _ = (|a| ^ k / (k ! : ℝ)) * ((k : ℝ) / ((n + 1 : ℕ) : ℝ)) := by push_cast; ring

/-- **4.7.8. Példa.** `aⁿ/n! → 0` bármely valós `a`-ra.

*Bizonyítás.* Legyen `k = [|a|] + 1` és `K = |a|ᵏ/k!`.  A szorzat tagjait becsülve
`|aⁿ/n!| = (|a|/1)(|a|/2)⋯(|a|/n) ≤ K·(k/n)`, hiszen a `k`-adik tényezőtől kezdve minden
tényező legfeljebb 1.  A jobb oldal nullához tart, így elég nagy `n`-re kisebb `ε`-nál. -/
theorem a_hatvany_per_faktorialis (a : ℝ) :
    HatarErtek (fun n : ℕ => a ^ n / (n ! : ℝ)) 0 := by
  intro ε hε
  set k : ℕ := ⌊|a|⌋₊ + 1 with hkdef
  have hk1 : 1 ≤ k := by omega
  have hak : |a| ≤ (k : ℝ) := by
    have := Nat.lt_floor_add_one (|a|)
    rw [hkdef]
    push_cast
    linarith
  set K : ℝ := |a| ^ k / (k ! : ℝ) with hKdef
  have hK0 : 0 ≤ K := by positivity
  obtain ⟨N, hN⟩ := exists_nat_gt (K * k / ε)
  refine ⟨max N k, fun n hn => ?_⟩
  have hkn : k ≤ n := le_of_lt (lt_of_le_of_lt (le_max_right N k) hn)
  have hnN : (N : ℝ) < n := by
    exact_mod_cast lt_of_le_of_lt (le_max_left N k) hn
  have hn0 : (0 : ℝ) < n := by
    have hnpos : 0 < n := lt_of_lt_of_le hk1 hkn
    exact_mod_cast hnpos
  have hfac : (0 : ℝ) < (n ! : ℝ) := by exact_mod_cast n.factorial_pos
  have hbecs := faktorialis_becsles hk1 hak n hkn
  show |a ^ n / (n ! : ℝ) - 0| < ε
  have habs : |a ^ n / (n ! : ℝ) - 0| = |a| ^ n / (n ! : ℝ) := by
    rw [sub_zero, abs_div, abs_pow, abs_of_pos hfac]
  rw [habs]
  have hlt : K * (k / n) < ε := by
    have h1 : K * k / ε < n := lt_trans hN hnN
    rw [div_lt_iff₀ hε] at h1
    rw [mul_div_assoc'] at *
    rw [div_lt_iff₀ hn0]
    linarith
  exact lt_of_le_of_lt hbecs hlt

/-! ## 4.7.9. Példa — `ⁿ√n → 1` -/

/-- Segédállítás: `n ≥ 2` esetén `(ⁿ√n - 1)² ≤ 16/n`.

*Bizonyítás (a könyv \"trükkös fogása\").*  Legyen `b = ⁿ√n - 1 ≥ 0`.  Ekkor
`n = (1+b)ⁿ ≥ (1+b)^{2[n/2]} = ((1+b)^{[n/2]})² ≥ (1 + [n/2]b)² > [n/2]²b² ≥ (n/4)²b²`,
amiből `b² ≤ 16/n` adódik. -/
theorem n_edik_gyok_becsles {n : ℕ} (hn : 2 ≤ n) :
    ((n : ℝ) ^ ((n : ℝ)⁻¹) - 1) ^ 2 ≤ 16 / n := by
  have hn0 : (0 : ℝ) < n := by
    have : (0 : ℕ) < n := by omega
    exact_mod_cast this
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_of_lt hn
  set x : ℝ := (n : ℝ) ^ ((n : ℝ)⁻¹) with hxdef
  have hx1 : 1 ≤ x := Real.one_le_rpow hn1 (by positivity)
  have hb : 0 ≤ x - 1 := by linarith
  have hxn : x ^ n = n := by
    rw [hxdef, ← Real.rpow_natCast ((n : ℝ) ^ ((n : ℝ)⁻¹)) n,
      ← Real.rpow_mul (le_of_lt hn0), inv_mul_cancel₀ (ne_of_gt hn0), Real.rpow_one]
  set m : ℕ := n / 2 with hmdef
  have h2m : 2 * m ≤ n := by omega
  have h4m : n ≤ 4 * m := by omega
  have h4mR : (n : ℝ) ≤ 4 * m := by exact_mod_cast h4m
  have hmono : x ^ (2 * m) ≤ x ^ n := pow_le_pow_right₀ hx1 h2m
  have hber : 1 + (m : ℝ) * (x - 1) ≤ x ^ m := by
    have := bernoulli (α := x - 1) (by linarith) m
    simpa using this
  have hsq : (1 + (m : ℝ) * (x - 1)) ^ 2 ≤ (x ^ m) ^ 2 := by
    apply pow_le_pow_left₀ (by positivity) hber
  have hxm : (x ^ m) ^ 2 = x ^ (2 * m) := by
    rw [← pow_mul, mul_comm]
  have hkey : (1 + (m : ℝ) * (x - 1)) ^ 2 ≤ (n : ℝ) := by
    rw [hxm] at hsq
    linarith [hmono, hxn ▸ hmono]
  have hmb : 0 ≤ (m : ℝ) * (x - 1) := by positivity
  have hmb2 : (n : ℝ) / 4 * (x - 1) ≤ (m : ℝ) * (x - 1) :=
    mul_le_mul_of_nonneg_right (by linarith) hb
  have h5 : ((n : ℝ) / 4 * (x - 1)) ^ 2 ≤ (1 + (m : ℝ) * (x - 1)) ^ 2 :=
    pow_le_pow_left₀ (by positivity) (by linarith) 2
  have h6 : ((n : ℝ) / 4 * (x - 1)) ^ 2 ≤ (n : ℝ) := le_trans h5 hkey
  have hnb : (n : ℝ) * (x - 1) ^ 2 ≤ 16 := by
    nlinarith [h6, hn0, sq_nonneg (x - 1)]
  rw [le_div_iff₀ hn0]
  linarith [hnb]

/-- **4.7.9. Példa.** `ⁿ√n → 1`.

*Bizonyítás.* Az előző becslés szerint `0 ≤ ⁿ√n - 1` és `(ⁿ√n - 1)² ≤ 16/n`, tehát
`n > 16/ε²` esetén `(ⁿ√n - 1)² < ε²`, azaz `|ⁿ√n - 1| < ε`. -/
theorem n_edik_gyok_hatarerteke :
    HatarErtek (fun n : ℕ => (n : ℝ) ^ ((n : ℝ)⁻¹)) 1 := by
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (16 / ε ^ 2)
  refine ⟨max N 2, fun n hn => ?_⟩
  have hn2 : 2 ≤ n := le_of_lt (lt_of_le_of_lt (le_max_right N 2) hn)
  have hnN : (N : ℝ) < n := by
    exact_mod_cast lt_of_le_of_lt (le_max_left N 2) hn
  have hn0 : (0 : ℝ) < n := by
    have : (0 : ℕ) < n := by omega
    exact_mod_cast this
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_of_lt hn2
  have hx1 : 1 ≤ (n : ℝ) ^ ((n : ℝ)⁻¹) := Real.one_le_rpow hn1 (by positivity)
  have hbecs := n_edik_gyok_becsles hn2
  have hlt : 16 / (n : ℝ) < ε ^ 2 := by
    have h1 : 16 / ε ^ 2 < (n : ℝ) := lt_trans hN hnN
    rw [div_lt_iff₀ (by positivity)] at h1
    rw [div_lt_iff₀ hn0]
    linarith
  have hsq : ((n : ℝ) ^ ((n : ℝ)⁻¹) - 1) ^ 2 < ε ^ 2 := lt_of_le_of_lt hbecs hlt
  have : (n : ℝ) ^ ((n : ℝ)⁻¹) - 1 < ε := by nlinarith [hsq, hx1, hε]
  rw [abs_lt]
  constructor <;> linarith

end Ch04
end Leindler
