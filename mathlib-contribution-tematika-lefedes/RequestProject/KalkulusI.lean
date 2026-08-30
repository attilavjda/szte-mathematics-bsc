/-
# Kalkulus I

A kurzus néhány központi állítása és tipikus gyakorlófeladata:

* `sup_unique` — a felső határ (szuprémum) egyértelmű;
* `tendsto_one_div_atTop` — az `1/n` sorozat nullához tart;
* `frog_series` — a felező ugrások összege 1 (mértani sor összege);
* `exists_root_cubic` — Bolzano-tétel alkalmazása: az `x³ + x - 1` polinomnak
  van gyöke a `(0,1)` intervallumban;
* `strictMono_cube` — az `x ↦ x³` függvény szigorúan monoton növő.
-/
import Mathlib

namespace SZTE.Kalkulus

open Filter Topology

/-- A felső határ egyértelmű: ha `a` és `b` is legkisebb felső korlátja
az `S` halmaznak, akkor `a = b`. -/
theorem sup_unique {S : Set ℝ} {a b : ℝ} (ha : IsLUB S a) (hb : IsLUB S b) :
    a = b := ha.unique hb

/-- Az `1/n` sorozat határértéke 0. -/
theorem tendsto_one_div_atTop :
    Tendsto (fun n : ℕ => (1 : ℝ) / n) atTop (𝓝 0) :=
  tendsto_one_div_atTop_nhds_zero_nat

/-- A "szélesszájú kisbéka" feladat: a felező ugrások hossza összesen 1. -/
theorem frog_series : ∑' n : ℕ, (1 / 2 : ℝ) ^ (n + 1) = 1 := by
  have h : ∑' n : ℕ, (1 / 2 : ℝ) ^ (n + 1) = (1 / 2 : ℝ) * ∑' n : ℕ, (1 / 2 : ℝ) ^ n := by
    rw [← tsum_mul_left]
    congr 1
    ext n
    ring
  rw [h, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]
  norm_num

/-- Bolzano-tétel alkalmazása: az `x³ + x - 1` függvénynek van gyöke `(0,1)`-ben. -/
theorem exists_root_cubic : ∃ x ∈ Set.Ioo (0 : ℝ) 1, x ^ 3 + x - 1 = 0 := by
  have hcont : ContinuousOn (fun x : ℝ => x ^ 3 + x - 1) (Set.Icc 0 1) := by fun_prop
  have hIVT := intermediate_value_Ioo (by norm_num : (0 : ℝ) ≤ 1) hcont
  have h0 : (0 : ℝ) ∈
      Set.Ioo ((fun x : ℝ => x ^ 3 + x - 1) 0) ((fun x : ℝ => x ^ 3 + x - 1) 1) := by
    norm_num
  obtain ⟨x, hx, hfx⟩ := hIVT h0
  exact ⟨x, hx, hfx⟩

/-- Az `x ↦ x³` függvény szigorúan monoton növő a valós számokon. -/
theorem strictMono_cube : StrictMono (fun x : ℝ => x ^ 3) :=
  Odd.strictMono_pow (R := ℝ) (by norm_num)

end SZTE.Kalkulus
