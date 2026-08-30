import Analizis.Ch04c_Konvergenciakriteriumok
import Analizis.Ch04d_Peldak

/-!
# Leindler László: Analízis — 4.17. szakasz: Valós számsorok (folytatás)

Ez a modul a **4.17. szakasz** hátralévő tételeit formalizálja (42–44. oldal). A sor,
a részletösszeg, a konvergencia és az összeg fogalma (**4.17.1–4.17.4. Definíció**),
valamint a geometriai sor konvergens esete a `Ch04c_Konvergenciakriteriumok` modulban
szerepel.

* **4.17.5. Tétel** — a konvergencia szükséges feltétele, hogy az általános tag nullához
  tartson (`sor_konvergens_tag_nullahoz`); a feltétel nem elégséges (lásd 4.17.8).
* **4.17.6. Tétel** — a sorokra vonatkozó **Cauchy-féle konvergenciakritérium**
  (`sor_cauchy_kriterium`).
* **4.17.7. Tétel** — a geometriai sor `|q| ≥ 1` esetén divergens
  (`geometriai_sor_divergens`); a `|q| < 1` eset a `geometriai_sor` tétel.
* **4.17.8. Tétel** — a **harmonikus sor divergens** (`harmonikus_sor_divergens`), bár az
  általános tagja nullához tart.
-/

namespace Leindler
namespace Ch04

open scoped BigOperators

/-! ## Segédállítások -/

/-- Az `[m, n)` indexekhez tartozó tagok összege a részletösszegek különbsége. -/
theorem sum_Ico_eq_reszletosszeg_sub (a : Sorozat) {m n : ℕ} (h : m ≤ n) :
    ∑ i ∈ Finset.Ico m n, a i = Reszletosszeg a n - Reszletosszeg a m := by
  unfold Reszletosszeg
  exact Finset.sum_Ico_eq_sub _ h

/-- Ha `aₙ → A`, akkor az eggyel eltolt `a_{n+1}` sorozat határértéke is `A`. -/
theorem hatarErtek_shift {a : Sorozat} {A : ℝ} (h : HatarErtek a A) :
    HatarErtek (fun n => a (n + 1)) A := by
  intro ε hε
  obtain ⟨N, hN⟩ := h ε hε
  exact ⟨N, fun n hn => hN (n + 1) (by omega)⟩

/-! ## 4.17.5. Tétel -/

/-- **4.17.5. Tétel.** Számsor konvergenciájának szükséges feltétele, hogy az általános
tagja nullához tartson. (De nem elégséges e feltétel, lásd 4.17.8.)

*Bizonyítás.* Mivel `aₙ = sₙ₊₁ - sₙ`, és `sₙ → S`, `sₙ₊₁ → S`, így `aₙ → 0`. -/
theorem sor_konvergens_tag_nullahoz {a : Sorozat} (h : SorKonvergens a) : HatarErtek a 0 := by
  obtain ⟨S, hS⟩ := h
  have hkey : HatarErtek (fun n => Reszletosszeg a (n + 1) - Reszletosszeg a n) (S - S) :=
    hatarErtek_sub (hatarErtek_shift hS) hS
  have hfun : a = fun n => Reszletosszeg a (n + 1) - Reszletosszeg a n :=
    funext fun n => tag_reszletosszegbol a n
  rw [hfun]
  simpa using hkey

/-! ## 4.17.6. Tétel: Cauchy-féle konvergenciakritérium sorokra -/

/-- A sorokra vonatkozó Cauchy-féle feltétel: bármely `ε > 0`-hoz van olyan `ν`
küszöbszám, hogy `n > m ≥ ν` esetén `|∑_{i=m}^{n-1} aᵢ| < ε`. -/
def SorCauchyFeltetel (a : Sorozat) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ m > N, ∀ n > m, |∑ i ∈ Finset.Ico m n, a i| < ε

/-- **4.17.6. Tétel (Cauchy-féle konvergenciakritérium).** A `∑ aₙ` sor akkor és csakis
akkor konvergál, ha bármely `ε > 0`-hoz megadható olyan `ν = ν(ε)` küszöbszám, hogy
`n > m ≥ ν` esetén `|∑_{i=m}^{n} aᵢ| < ε`.

*Bizonyítás.* Mivel `∑_{i=m}^{n-1} aᵢ = sₙ - sₘ`, a sorozatokra megismert Cauchy-féle
konvergenciakritériumból és a végtelen sorok konvergenciájának definíciójából az állítás
azonnal adódik. -/
theorem sor_cauchy_kriterium (a : Sorozat) : SorKonvergens a ↔ SorCauchyFeltetel a := by
  rw [SorKonvergens, cauchy_kriterium]
  constructor
  · intro h ε hε
    obtain ⟨N, hN⟩ := h ε hε
    refine ⟨N, fun m hm n hn => ?_⟩
    rw [sum_Ico_eq_reszletosszeg_sub a hn.le]
    exact hN n (by omega) m hm
  · intro h ε hε
    obtain ⟨N, hN⟩ := h ε hε
    refine ⟨N, fun n hn m hm => ?_⟩
    rcases lt_trichotomy m n with hlt | rfl | hgt
    · have := hN m hm n hlt
      rwa [sum_Ico_eq_reszletosszeg_sub a hlt.le] at this
    · simpa using hε
    · have := hN n hn m hgt
      rw [sum_Ico_eq_reszletosszeg_sub a hgt.le] at this
      rwa [abs_sub_comm] at this

/-! ## 4.17.7. Tétel: a geometriai sor -/

/-- **4.17.7. Tétel** (a divergens eset). Ha `|q| ≥ 1`, akkor a `∑ qⁿ` geometriai sor
divergens.

*Bizonyítás.* Ha `|q| ≥ 1`, akkor `|qⁿ| ≥ 1`, tehát az általános tag nem tart nullához,
így a 4.17.5. Tétel szerint a sor nem lehet konvergens. -/
theorem geometriai_sor_divergens {q : ℝ} (hq : 1 ≤ |q|) :
    ¬ SorKonvergens (fun n => q ^ n) := by
  intro h
  obtain ⟨N, hN⟩ := sor_konvergens_tag_nullahoz h 1 one_pos
  have h1 : |q ^ (N + 1)| < 1 := by simpa using hN (N + 1) (by omega)
  have h2 : (1 : ℝ) ≤ |q ^ (N + 1)| := by
    rw [abs_pow]
    exact one_le_pow₀ hq
  linarith

/-! ## 4.17.8. Tétel: a harmonikus sor -/

/-- A harmonikus sor általános tagja (a könyv `1/n` jelölésének nulláról induló
indexeléssel megfelelő alakja). -/
noncomputable def harmonikusTag (n : ℕ) : ℝ := 1 / (n + 1 : ℝ)

/-- A harmonikus sor általános tagja nullához tart. -/
theorem harmonikusTag_nullahoz : HatarErtek harmonikusTag 0 := by
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
  refine ⟨N, fun n hn => ?_⟩
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hlt : 1 / ε < (n : ℝ) + 1 := by
    have : (N : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn.le
    linarith
  have : 1 / ((n : ℝ) + 1) < ε := by
    rw [div_lt_iff₀ hn1]
    rw [div_lt_iff₀ hε] at hlt
    linarith
  rw [harmonikusTag, sub_zero, abs_of_pos (by positivity)]
  exact this

/-- Az `[m, 2m)` indexekhez tartozó harmonikus tagok összege legalább `1/2`. -/
theorem harmonikus_blokk_becsles {m : ℕ} (hm : 1 ≤ m) :
    (1 : ℝ) / 2 ≤ ∑ i ∈ Finset.Ico m (2 * m), harmonikusTag i := by
  have hm0 : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hle : ∀ i ∈ Finset.Ico m (2 * m), 1 / (2 * (m : ℝ)) ≤ harmonikusTag i := by
    intro i hi
    rw [Finset.mem_Ico] at hi
    have hi1 : (i : ℝ) + 1 ≤ 2 * (m : ℝ) := by
      have : (i : ℝ) + 1 ≤ ((2 * m : ℕ) : ℝ) := by exact_mod_cast hi.2
      push_cast at this
      linarith
    have hipos : (0 : ℝ) < (i : ℝ) + 1 := by positivity
    exact one_div_le_one_div_of_le hipos hi1
  have hcard : (Finset.Ico m (2 * m)).card = m := by
    rw [Nat.card_Ico]
    omega
  have := Finset.card_nsmul_le_sum (Finset.Ico m (2 * m)) harmonikusTag
    (1 / (2 * (m : ℝ))) hle
  rw [hcard, nsmul_eq_mul] at this
  refine le_trans (le_of_eq ?_) this
  field_simp

/-- **4.17.8. Tétel.** A `∑ 1/n` harmonikus sor divergens (bár `aₙ → 0`).

*Bizonyítás.* Bármely `m`-re `∑_{n=m}^{2m-1} 1/n ≥ m · (1/(2m)) = 1/2`, tehát a
Cauchy-féle konvergenciakritérium `ε = 1/2`-re nem teljesülhet. -/
theorem harmonikus_sor_divergens : ¬ SorKonvergens harmonikusTag := by
  intro h
  obtain ⟨N, hN⟩ := (sor_cauchy_kriterium harmonikusTag).1 h (1 / 2) (by norm_num)
  have hlt := hN (N + 1) (by omega) (2 * (N + 1)) (by omega)
  have hge := harmonikus_blokk_becsles (m := N + 1) (by omega)
  have habs : ∑ i ∈ Finset.Ico (N + 1) (2 * (N + 1)), harmonikusTag i ≤
      |∑ i ∈ Finset.Ico (N + 1) (2 * (N + 1)), harmonikusTag i| := le_abs_self _
  linarith

end Ch04
end Leindler
