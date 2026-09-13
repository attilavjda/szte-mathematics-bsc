import Mathlib
import Analizis.Ch04a_SorozatokAlapok
import Analizis.Ch04b_SorozatokMuveletek
import Analizis.Ch04c_Konvergenciakriteriumok
import Analizis.Ch04f_NevezetesHatarertekek
import Analizis.Ch04g_LimeszSzuperior
import Analizis.Ch04h_Kiegeszitesek

/-!
# Leindler László: Analízis — a 4. fejezet példái és megjegyzései

Ez a modul a 4. fejezet azon *számozott példáit és megjegyzéseit* formalizálja, amelyek a
korábbi modulokból kimaradtak (13–37. oldal):

* **4.2.2. Példák** — a harmonikus, a geometriai és a számtani sorozat (formulával), egy
  rekurzióval adott sorozat, és egy utasítással adott sorozat (`√2` tizedesjegyei),
* **4.2.3. Megjegyzés** — az indexezés gyakran nullával kezdődik; ez a konvergencián nem
  változtat,
* **4.3.2. Példák** — korlátos sorozatok: `{1/n}`, `{(-1)ⁿ}`, `{1 + (-1)ⁿ}`,
* **4.4.2. Példák és jelölésük** — `{1} ↗`, `{n} ↑`, `{1} ↘`, `{1/n} ↓`,
* **4.5.2. Példák** — az `{n²}` sorozat `{(2n)²}` és `{(2ⁿ)²}` részsorozatai, továbbá a
  4.5.2. utáni megjegyzés: nem monoton sorozatnak lehet monoton, nem korlátos sorozatnak
  korlátos részsorozata,
* **4.6.9. Példák** — divergens sorozatok: `{(-1)ⁿ}`, `{1 + (-1)ⁿ}`, `{(1 + (-1)ⁿ)n}`,
* **4.6.10. Megjegyzés** — a divergencia azt jelenti, hogy *nincs* olyan `a` szám, amely a
  határérték definícióját teljesíti,
* **4.8.7. Példák** — a természetes számok reciprok sorozatának egy átrendezése
  (`1/2, 1, 1/4, 1/3, …`),
* **4.9.2. Példák** — a műveleti szabályok alkalmazása négy konkrét határértékre,
* **4.10.2. Megjegyzés** — a 4.10.1. Tétel feltételei mellett `aₙ < b_m` is teljesül
  majdnem minden `n`-re és `m`-re,
* **4.10.4. Megjegyzés** — `aₙ < bₙ` esetén sem állíthatunk többet, mint `A ≤ B`
  (példa: `1/n` és `−1/n`),
* **4.11.2. Megjegyzés** — a `dₙ → ∞` jelölés *divergenciát* jelöl: az ilyen sorozat nem
  konvergens,
* **4.12.2. Megjegyzés** — valódi divergens sorozatok különbségéről és hányadosáról
  általában semmit nem állíthatunk (három ellenpélda),
* **4.14.7. Megjegyzés** — a 4.14.6. Tételben a zártság lényeges: a `(0, 1/n)` nyitott
  intervallumoknak nincs közös pontja,
* **4.14.11. Megjegyzés** — a legnagyobb (legkisebb) torlódási pont a torlódási pontok
  halmazának felső (alsó) határa.

**Indexelési konvenció.** A jegyzet a sorozatokat `n = 1`-től indexeli, a Lean-beli
`Sorozat = ℕ → ℝ` viszont `n = 0`-tól; ezért a könyv `{1/n}` sorozatát a
`harmonikusSorozat n = 1/(n+1)` képlettel írjuk fel — ez pontosan a jegyzetben felsorolt
`1, 1/2, 1/3, …` sorozat. (A 4.2.3. Megjegyzés éppen azt rögzíti, hogy az indexezés
kezdőpontja lényegtelen.)
-/

namespace Leindler
namespace Ch04

open scoped BigOperators

/-! ## 4.2.2. Példák — sorozatok megadási módjai -/

/-- **4.2.2. Példa.** A *harmonikus sorozat*: `1, 1/2, 1/3, …, 1/n, …` (formulával adott). -/
noncomputable def harmonikusSorozat : Sorozat := fun n => 1 / ((n : ℝ) + 1)

/-- **4.2.2. Példa.** A *geometriai sorozat*: `2, 4, 8, …, 2ⁿ, …` (formulával adott);
általánosabban `qⁿ`. -/
noncomputable def geometriaiSorozat (q : ℝ) : Sorozat := fun n => q ^ (n + 1)

/-- **4.2.2. Példa.** A *számtani sorozat*: `d, 2d, 3d, …, nd, …` (formulával adott). -/
noncomputable def szamtaniSorozat (d : ℝ) : Sorozat := fun n => ((n : ℝ) + 1) * d

/-- **4.2.2. Példa.** Rekurzióval adott sorozat: `a₁ = a`, `aₙ = 2aₙ₋₁ + 1`. -/
noncomputable def rekurzivSorozat (a : ℝ) : Sorozat
  | 0 => a
  | n + 1 => 2 * rekurzivSorozat a n + 1

/-- **4.2.2. Példa.** Utasítással adott sorozat: `aₙ` legyen `√2` `n`-edik tizedesjegye. -/
noncomputable def gyokKettoTizedesjegye : Sorozat :=
  fun n => (⌊Real.sqrt 2 * 10 ^ (n + 1)⌋ % 10 : ℤ)

/-- A harmonikus sorozat nullához tart. -/
theorem harmonikusSorozat_hatarerteke : HatarErtek harmonikusSorozat 0 := by
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
  refine ⟨N, fun n hn => ?_⟩
  have hn0 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hNn : (N : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have h1 : 1 / ε < (n : ℝ) + 1 := by linarith
  have hlt : 1 / ((n : ℝ) + 1) < ε := by
    rw [div_lt_iff₀ hn0]
    have := (div_lt_iff₀ hε).1 h1
    linarith [this]
  have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
  simp only [harmonikusSorozat, sub_zero, abs_of_pos hpos]
  exact hlt

/-- A geometriai sorozat hányadosa állandó: `aₙ₊₁ = q·aₙ`. -/
theorem geometriaiSorozat_rekurzio (q : ℝ) (n : ℕ) :
    geometriaiSorozat q (n + 1) = q * geometriaiSorozat q n := by
  simp [geometriaiSorozat, pow_succ]
  ring

/-- A számtani sorozat különbsége állandó: `aₙ₊₁ - aₙ = d`. -/
theorem szamtaniSorozat_rekurzio (d : ℝ) (n : ℕ) :
    szamtaniSorozat d (n + 1) - szamtaniSorozat d n = d := by
  simp [szamtaniSorozat]
  ring

/-- A rekurzióval adott sorozat zárt alakja: `aₙ = 2ⁿ(a + 1) - 1`. -/
theorem rekurzivSorozat_zart_alak (a : ℝ) (n : ℕ) :
    rekurzivSorozat a n = 2 ^ n * (a + 1) - 1 := by
  induction n with
  | zero => simp [rekurzivSorozat]
  | succ n ih =>
      rw [rekurzivSorozat, ih, pow_succ]
      ring

/-- A `√2` tizedesjegyeiből álló sorozat tagjai `0` és `9` közé esnek. -/
theorem gyokKettoTizedesjegye_mem (n : ℕ) :
    0 ≤ gyokKettoTizedesjegye n ∧ gyokKettoTizedesjegye n ≤ 9 := by
  have h0 : (0 : ℝ) ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hfl : 0 ≤ ⌊Real.sqrt 2 * 10 ^ (n + 1)⌋ := by
    apply Int.floor_nonneg.2
    positivity
  have hmod : (0 : ℤ) ≤ ⌊Real.sqrt 2 * 10 ^ (n + 1)⌋ % 10 :=
    Int.emod_nonneg _ (by norm_num)
  have hmod' : ⌊Real.sqrt 2 * 10 ^ (n + 1)⌋ % 10 < 10 := Int.emod_lt_of_pos _ (by norm_num)
  constructor
  · simpa [gyokKettoTizedesjegye] using (show (0:ℝ) ≤ ((⌊Real.sqrt 2 * 10 ^ (n+1)⌋ % 10 : ℤ) : ℝ)
      from by exact_mod_cast hmod)
  · have : ((⌊Real.sqrt 2 * 10 ^ (n+1)⌋ % 10 : ℤ) : ℝ) ≤ 9 := by
      have : ⌊Real.sqrt 2 * 10 ^ (n + 1)⌋ % 10 ≤ 9 := by omega
      exact_mod_cast this
    simpa [gyokKettoTizedesjegye] using this

/-! ## 4.2.3. Megjegyzés — az indexezés kezdőpontja -/

/-- **4.2.3. Megjegyzés.** „Gyakran nullával kezdődik a sorozatok indexezése, azaz
`a₀, a₁, a₂, …`” — az indexezés kezdőpontja a konvergenciát és a határértéket nem
befolyásolja: `{aₙ}` pontosan akkor tart `A`-hoz, ha az eggyel eltolt sorozat is. -/
theorem hatarErtek_eltolas_iff (a : Sorozat) (A : ℝ) :
    HatarErtek a A ↔ HatarErtek (fun n => a (n + 1)) A := by
  constructor
  · intro h
    exact eltolt_hatarerteke 1 h
  · intro h ε hε
    obtain ⟨N, hN⟩ := h ε hε
    refine ⟨N + 1, fun n hn => ?_⟩
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact hN m (by omega)

/-! ## 4.3.2. Példák — korlátos sorozatok -/

/-- **4.3.2. Példa.** Az `{1/n}` sorozat korlátos (`0 ≤ aₙ ≤ 1`). -/
theorem harmonikusSorozat_korlatos : Korlatos harmonikusSorozat := by
  refine ⟨⟨0, fun n => ?_⟩, ⟨1, fun n => ?_⟩⟩ <;> simp only [harmonikusSorozat]
  · positivity
  · rw [div_le_one (by positivity)]
    have : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith

/-- **4.3.2. Példa.** A `{(-1)ⁿ}` sorozat korlátos. -/
theorem valto_elojel_korlatos : Korlatos (fun n : ℕ => (-1 : ℝ) ^ n) := by
  refine (korlatos_iff_abs _).2 ⟨1, fun n => ?_⟩
  simp [abs_pow]

/-- **4.3.2. Példa.** Az `{1 + (-1)ⁿ}` sorozat korlátos. -/
theorem egy_meg_valto_elojel_korlatos : Korlatos (fun n : ℕ => 1 + (-1 : ℝ) ^ n) := by
  have key : ∀ n : ℕ, 0 ≤ 1 + (-1 : ℝ) ^ n ∧ 1 + (-1 : ℝ) ^ n ≤ 2 := by
    intro n
    rcases Nat.even_or_odd n with h | h
    · rw [h.neg_one_pow]; norm_num
    · rw [h.neg_one_pow]; norm_num
  exact ⟨⟨0, fun n => (key n).1⟩, ⟨2, fun n => (key n).2⟩⟩

/-! ## 4.4.2. Példák és jelölésük — monoton sorozatok -/

/-- **4.4.2. Példa.** `{1} ↗`: az azonosan `1` sorozat (tágabb értelemben) növekedő. -/
theorem allando_novekedo : Novekedo (fun _ : ℕ => (1 : ℝ)) := fun _ => le_refl _

/-- **4.4.2. Példa.** `{n} ↑`: az `{n}` sorozat szigorúan növekedő. -/
theorem termeszetes_szigoruan_novekedo : SzigoruanNovekedo (fun n : ℕ => (n : ℝ)) := by
  intro n
  push_cast
  linarith

/-- **4.4.2. Példa.** `{1} ↘`: az azonosan `1` sorozat (tágabb értelemben) csökkenő. -/
theorem allando_csokkeno : Csokkeno (fun _ : ℕ => (1 : ℝ)) := fun _ => le_refl _

/-- **4.4.2. Példa.** `{1/n} ↓`: a harmonikus sorozat szigorúan csökkenő. -/
theorem harmonikusSorozat_szigoruan_csokkeno : SzigoruanCsokkeno harmonikusSorozat := by
  intro n
  have h1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have h2 : (0 : ℝ) < ((n : ℝ) + 1) + 1 := by positivity
  simp only [harmonikusSorozat, Nat.cast_add, Nat.cast_one]
  rw [div_lt_div_iff₀ (by positivity) h1]
  linarith

/-! ## 4.5.2. Példák — részsorozatok -/

/-- **4.5.2. Példa.** Az `{n²}` sorozat egyik részsorozata `{(2n)²}` (itt `nₖ = 2k`). -/
theorem negyzet_reszsorozat_paros :
    Reszsorozat (fun k : ℕ => ((2 * k : ℕ) : ℝ) ^ 2) (fun n : ℕ => (n : ℝ) ^ 2) :=
  ⟨fun k => 2 * k, fun _ _ h => by dsimp only; omega, rfl⟩

/-- **4.5.2. Példa.** Az `{n²}` sorozat másik részsorozata `{(2ⁿ)²}` (itt `nₖ = 2ᵏ`). -/
theorem negyzet_reszsorozat_kettohatvany :
    Reszsorozat (fun k : ℕ => ((2 ^ k : ℕ) : ℝ) ^ 2) (fun n : ℕ => (n : ℝ) ^ 2) :=
  ⟨fun k => 2 ^ k, fun _ _ h => Nat.pow_lt_pow_right (by norm_num) h, rfl⟩

/-- **4.5.2. utáni megjegyzés.** Nem monoton sorozatnak lehet monoton részsorozata: az
`aₙ = (1 + (-1)ⁿ)/n` sorozat páratlan indexű tagjai mind nullák. -/
theorem nem_monoton_monoton_reszsorozata :
    Reszsorozat (fun k : ℕ => (1 + (-1 : ℝ) ^ (2 * k + 1)) / ((2 * k + 1 : ℕ) : ℝ))
      (fun n : ℕ => (1 + (-1 : ℝ) ^ n) / (n : ℝ)) ∧
    Novekedo (fun k : ℕ => (1 + (-1 : ℝ) ^ (2 * k + 1)) / ((2 * k + 1 : ℕ) : ℝ)) := by
  constructor
  · exact ⟨fun k => 2 * k + 1, fun _ _ h => by dsimp only; omega, rfl⟩
  · intro k
    have h1 : Odd (2 * k + 1) := ⟨k, by ring⟩
    have h2 : Odd (2 * (k + 1) + 1) := ⟨k + 1, by ring⟩
    simp [h1.neg_one_pow, h2.neg_one_pow]

/-- **4.5.2. utáni megjegyzés.** Nem korlátos sorozatnak lehet korlátos részsorozata: a
`bₙ = (1 + (-1)ⁿ)n` sorozat páratlan indexű tagjai mind nullák. -/
theorem nem_korlatos_korlatos_reszsorozata :
    Reszsorozat (fun k : ℕ => (1 + (-1 : ℝ) ^ (2 * k + 1)) * ((2 * k + 1 : ℕ) : ℝ))
      (fun n : ℕ => (1 + (-1 : ℝ) ^ n) * (n : ℝ)) ∧
    Korlatos (fun k : ℕ => (1 + (-1 : ℝ) ^ (2 * k + 1)) * ((2 * k + 1 : ℕ) : ℝ)) := by
  refine ⟨⟨fun k => 2 * k + 1, fun _ _ h => by dsimp only; omega, rfl⟩,
      ⟨⟨0, fun k => ?_⟩, ⟨0, fun k => ?_⟩⟩⟩ <;>
    · have h1 : Odd (2 * k + 1) := ⟨k, by ring⟩
      simp [h1.neg_one_pow]

/-! ## 4.6.9. Példák — divergens sorozatok -/

/-- **4.6.9. Példa.** Az `{1 + (-1)ⁿ}` sorozat divergens. -/
theorem egy_meg_valto_elojel_divergens : Divergens (fun n : ℕ => 1 + (-1 : ℝ) ^ n) := by
  rintro ⟨A, hA⟩
  obtain ⟨N, hN⟩ := hA 1 one_pos
  have h1 := hN (2 * N + 2) (by omega)
  have h2 := hN (2 * N + 3) (by omega)
  have e1 : Even (2 * N + 2) := ⟨N + 1, by ring⟩
  have e2 : Odd (2 * N + 3) := ⟨N + 1, by ring⟩
  dsimp only at h1 h2
  rw [e1.neg_one_pow] at h1
  rw [e2.neg_one_pow] at h2
  rw [abs_lt] at h1 h2
  linarith [h1.1, h1.2, h2.1, h2.2]

/-- **4.6.9. Példa.** Az `{(1 + (-1)ⁿ)n}` sorozat divergens (nem is korlátos). -/
theorem egy_meg_valto_elojel_szor_n_divergens :
    Divergens (fun n : ℕ => (1 + (-1 : ℝ) ^ n) * (n : ℝ)) := by
  intro hkonv
  obtain ⟨K, hK⟩ := (korlatos_iff_abs _).1 (konvergens_korlatos hkonv)
  obtain ⟨N, hN⟩ := exists_nat_gt K
  have e : Even (2 * N + 2) := ⟨N + 1, by ring⟩
  have h := hK (2 * N + 2)
  rw [e.neg_one_pow] at h
  have hcast : ((2 * N + 2 : ℕ) : ℝ) = 2 * (N : ℝ) + 2 := by push_cast; ring
  rw [hcast] at h
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  rw [show (1 : ℝ) + 1 = 2 by norm_num, abs_of_nonneg (by linarith)] at h
  linarith

/-! ## 4.6.10. Megjegyzés -/

/-- **4.6.10. Megjegyzés.** Az, hogy egy adott sorozatnak nincs határértéke, azt jelenti,
hogy nem tudunk megadni olyan `a` számot, amely az előző definíciókban szereplő
tulajdonságokkal rendelkezik. -/
theorem divergens_iff (a : Sorozat) : Divergens a ↔ ∀ A : ℝ, ¬ HatarErtek a A := by
  simp [Divergens, Konvergens, not_exists]

/-! ## 4.8.7. Példák — átrendezések -/

/-- A `4.8.7.` első példájának permutációja: a szomszédos indexpárokat cseréli fel,
`p = (2, 1, 4, 3, 6, 5, …)`. -/
def parcsere : ℕ ≃ ℕ where
  toFun n := if n % 2 = 0 then n + 1 else n - 1
  invFun n := if n % 2 = 0 then n + 1 else n - 1
  left_inv n := by
    rcases Nat.even_or_odd n with h | h
    · have h0 : n % 2 = 0 := Nat.even_iff.1 h
      have h1 : (n + 1) % 2 = 1 := by omega
      simp [h0, h1]
    · have h1 : n % 2 = 1 := Nat.odd_iff.1 h
      have hn : 1 ≤ n := by omega
      have h0 : (n - 1) % 2 = 0 := by omega
      simp [h1, h0]
      omega
  right_inv n := by
    rcases Nat.even_or_odd n with h | h
    · have h0 : n % 2 = 0 := Nat.even_iff.1 h
      have h1 : (n + 1) % 2 = 1 := by omega
      simp [h0, h1]
    · have h1 : n % 2 = 1 := Nat.odd_iff.1 h
      have hn : 1 ≤ n := by omega
      have h0 : (n - 1) % 2 = 0 := by omega
      simp [h1, h0]
      omega

/-- **4.8.7. Példa.** A `1/2, 1, 1/4, 1/3, 1/6, 1/5, …` sorozat a természetes számok
reciprok sorozatának átrendezése. -/
theorem parcsere_atrendezes :
    Atrendezes (fun n => harmonikusSorozat (parcsere n)) harmonikusSorozat :=
  ⟨parcsere, rfl⟩

/-- **4.8.7. Példa (folytatás).** A **4.8.5. Tétel** szerint az átrendezett sorozat is
nullához tart. -/
theorem parcsere_hatarerteke :
    HatarErtek (fun n => harmonikusSorozat (parcsere n)) 0 :=
  atrendezes_konvergens parcsere_atrendezes harmonikusSorozat_hatarerteke

/-! ## 4.9.2. Példák — a műveleti szabályok alkalmazása -/

/-- **4.9.2. Példa, 1.** `ⁿ√n + 1/n → 1 + 0 = 1`. -/
theorem pelda_4_9_2_1 :
    HatarErtek (fun n : ℕ => (n : ℝ) ^ ((n : ℝ)⁻¹) + harmonikusSorozat n) 1 := by
  simpa using hatarErtek_add n_edik_gyok_hatarerteke harmonikusSorozat_hatarerteke

/-- **4.9.2. Példa, 1. (a `-` eset).** `ⁿ√n - 1/n → 1 - 0 = 1`. -/
theorem pelda_4_9_2_1' :
    HatarErtek (fun n : ℕ => (n : ℝ) ^ ((n : ℝ)⁻¹) - harmonikusSorozat n) 1 := by
  simpa using hatarErtek_sub n_edik_gyok_hatarerteke harmonikusSorozat_hatarerteke

/-- **4.9.2. Példa, 2.** `3(1 + 1/n) → 3(1 + 0) = 3`. -/
theorem pelda_4_9_2_2 :
    HatarErtek (fun n : ℕ => 3 * (1 + harmonikusSorozat n)) 3 := by
  have h : HatarErtek (fun n : ℕ => 1 + harmonikusSorozat n) 1 := by
    simpa using hatarErtek_add (allando_hatarerteke 1) harmonikusSorozat_hatarerteke
  simpa using hatarErtek_const_mul 3 h

/-- **4.9.2. Példa, 3.** `ⁿ√2 (2/n + ⁿ√n) → 1(0 + 1) = 1`. -/
theorem pelda_4_9_2_3 :
    HatarErtek
      (fun n : ℕ => (2 : ℝ) ^ ((n : ℝ)⁻¹) *
        (2 * harmonikusSorozat n + (n : ℝ) ^ ((n : ℝ)⁻¹))) 1 := by
  have h1 : HatarErtek (fun n : ℕ => 2 * harmonikusSorozat n) 0 := by
    simpa using hatarErtek_const_mul 2 harmonikusSorozat_hatarerteke
  have h2 : HatarErtek
      (fun n : ℕ => 2 * harmonikusSorozat n + (n : ℝ) ^ ((n : ℝ)⁻¹)) 1 := by
    simpa using hatarErtek_add h1 n_edik_gyok_hatarerteke
  simpa using hatarErtek_mul (gyok_a_hatarerteke (by norm_num : (0:ℝ) < 2)) h2

/-- **4.9.2. Példa, 4.** `((1/2)ⁿ + 3)/(3 + ⁿ√5) → (0 + 3)/(3 + 1) = 3/4`. -/
theorem pelda_4_9_2_4 :
    HatarErtek
      (fun n : ℕ => ((1 / 2 : ℝ) ^ n + 3) / (3 + (5 : ℝ) ^ ((n : ℝ)⁻¹))) (3 / 4) := by
  have hszam : HatarErtek (fun n : ℕ => (1 / 2 : ℝ) ^ n + 3) 3 := by
    have h : HatarErtek (fun n : ℕ => (1 / 2 : ℝ) ^ n) 0 :=
      q_hatvany_nullahoz (by rw [abs_of_pos] <;> norm_num)
    simpa using hatarErtek_add h (allando_hatarerteke 3)
  have hnev : HatarErtek (fun n : ℕ => 3 + (5 : ℝ) ^ ((n : ℝ)⁻¹)) 4 := by
    have h :=
      hatarErtek_add (allando_hatarerteke 3) (gyok_a_hatarerteke (by norm_num : (0:ℝ) < 5))
    simpa only [show (3 : ℝ) + 1 = 4 by norm_num] using h
  exact hatarErtek_div hszam hnev (by norm_num)

/-! ## 4.10.2. Megjegyzés -/

/-- **4.10.2. Megjegyzés.** A 4.10.1. Tétel feltételei mellett a bizonyítás alapján az is
adódik, hogy `aₙ < b_m` teljesül majdnem minden `n`-re és `m`-re: van olyan `ν`, hogy
`n, m > ν` esetén `aₙ < b_m`. -/
theorem kisebb_majdnem_minden_kettos {a b : Sorozat} {A B : ℝ} (ha : HatarErtek a A)
    (hb : HatarErtek b B) (hAB : A < B) : ∃ N : ℕ, ∀ n > N, ∀ m > N, a n < b m := by
  obtain ⟨N₁, hN₁⟩ := ha ((B - A) / 4) (by linarith)
  obtain ⟨N₂, hN₂⟩ := hb ((B - A) / 4) (by linarith)
  refine ⟨max N₁ N₂, fun n hn m hm => ?_⟩
  have h₁ := abs_lt.mp (hN₁ n (lt_of_le_of_lt (le_max_left _ _) hn))
  have h₂ := abs_lt.mp (hN₂ m (lt_of_le_of_lt (le_max_right _ _) hm))
  linarith [h₁.2, h₂.1]

/-! ## 4.10.4. Megjegyzés -/

/-- **4.10.4. Megjegyzés.** Ha azt tennénk fel, hogy `aₙ < bₙ` (`aₙ ≤ bₙ` helyett), akkor
sem tudnánk többet állítani, mint `A ≤ B`: a határátmenetnél a szigorú egyenlőtlenség
egyenlőségbe mehet át. -/
theorem szigoru_egyenlotlenseg_hatarertekben {a b : Sorozat} {A B : ℝ}
    (ha : HatarErtek a A) (hb : HatarErtek b B) {N₀ : ℕ} (hlt : ∀ n > N₀, a n < b n) :
    A ≤ B :=
  hatarErtek_le ha hb (N₀ := N₀) fun n hn => (hlt n hn).le

/-- **4.10.4. Megjegyzés** (a példa). Legyen `aₙ = 1/n` és `bₙ = −1/n`. Ekkor `bₙ < aₙ`
minden `n`-re, mégis `lim bₙ = lim aₙ = 0`, tehát a szigorú egyenlőtlenség a
határátmenetnél egyenlőségbe ment át. -/
theorem szigoru_egyenlotlenseg_ellenpelda :
    (∀ n, -harmonikusSorozat n < harmonikusSorozat n) ∧
      HatarErtek (fun n => -harmonikusSorozat n) 0 ∧ HatarErtek harmonikusSorozat 0 := by
  have hpos : ∀ n, 0 < harmonikusSorozat n := by
    intro n
    have : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    simpa [harmonikusSorozat] using div_pos one_pos this
  refine ⟨fun n => by linarith [hpos n], ?_, harmonikusSorozat_hatarerteke⟩
  simpa using hatarErtek_const_mul (-1) harmonikusSorozat_hatarerteke

/-! ## 4.11.2. Megjegyzés -/

/-- **4.11.2. Megjegyzés.** A `dₙ → ∞` jelölés olyan, mint a konvergencia jelölése, „itt
azonban divergenciáról van szó”: a plusz végtelenbe divergáló sorozat nem konvergens.

*Bizonyítás.* Konvergens sorozat korlátos, a plusz végtelenbe divergáló sorozat viszont
bármely `K` korlátot meghalad. -/
theorem divergal_nem_konvergens {d : Sorozat} (hd : PlusVegtelenbeDivergal d) :
    Divergens d := by
  intro hkonv
  obtain ⟨K, hK⟩ := (korlatos_iff_abs _).1 (konvergens_korlatos hkonv)
  have h1 := hd K
  obtain ⟨N, hN⟩ := h1
  have h2 := hN (N + 1) (by omega)
  have h3 := hK (N + 1)
  have := le_abs_self (d (N + 1))
  linarith

/-! ## 4.12.2. Megjegyzés — a különbség és a hányados határozatlansága -/

/-- Az `{n}` sorozat a plusz végtelenbe divergál. -/
theorem termeszetes_divergal : PlusVegtelenbeDivergal (fun n : ℕ => (n : ℝ)) := by
  intro M
  obtain ⟨N, hN⟩ := exists_nat_gt M
  refine ⟨N, fun n hn => ?_⟩
  have hNn : (N : ℝ) < (n : ℝ) := by exact_mod_cast hn
  simp only [gt_iff_lt]
  linarith

/-- **4.12.2. Megjegyzés, 1. példa.** `dₙ = n + 2` és `d̄ₙ = n` esetén mindkét sorozat
valódi divergens, de `dₙ - d̄ₙ = 2 → 2`. -/
theorem pelda_4_12_2_1_kulonbseg :
    PlusVegtelenbeDivergal (fun n : ℕ => (n : ℝ) + 2) ∧
      HatarErtek (fun n : ℕ => ((n : ℝ) + 2) - (n : ℝ)) 2 := by
  refine ⟨divergal_add_konvergens termeszetes_divergal (allando_hatarerteke 2), ?_⟩
  have h : (fun n : ℕ => ((n : ℝ) + 2) - (n : ℝ)) = fun _ : ℕ => (2 : ℝ) := by
    funext n; ring
  rw [h]
  exact allando_hatarerteke 2

/-- **4.12.2. Megjegyzés, 1. példa (hányados).** `(n + 2)/n → 1`. -/
theorem pelda_4_12_2_1_hanyados :
    HatarErtek (fun n : ℕ => ((n : ℝ) + 2) / (n : ℝ)) 1 := by
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (2 / ε)
  refine ⟨max N 1, fun n hn => ?_⟩
  have hn1 : 1 ≤ n := le_of_lt (lt_of_le_of_lt (le_max_right N 1) hn)
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hNn : (N : ℝ) < (n : ℝ) := by
    exact_mod_cast lt_of_le_of_lt (le_max_left N 1) hn
  have hkey : 2 / ε < (n : ℝ) := lt_trans hN hNn
  have heq : ((n : ℝ) + 2) / (n : ℝ) - 1 = 2 / (n : ℝ) := by
    field_simp
    ring
  rw [heq, abs_of_pos (by positivity), div_lt_iff₀ hn0]
  have := (div_lt_iff₀ hε).1 hkey
  linarith

/-- **4.12.2. Megjegyzés, 2. példa.** `dₙ = n²` és `d̄ₙ = n` esetén `dₙ - d̄ₙ = n(n-1) → ∞`
és `dₙ/d̄ₙ → ∞`. -/
theorem pelda_4_12_2_2 :
    PlusVegtelenbeDivergal (fun n : ℕ => (n : ℝ) ^ 2 - (n : ℝ)) ∧
      PlusVegtelenbeDivergal (fun n : ℕ => (n : ℝ) ^ 2 / (n : ℝ)) := by
  constructor
  · intro M
    obtain ⟨N, hN⟩ := exists_nat_gt (M + 1)
    refine ⟨max N 1, fun n hn => ?_⟩
    have hn1 : 1 ≤ n := le_of_lt (lt_of_le_of_lt (le_max_right N 1) hn)
    have hn1' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
    have hNn : (N : ℝ) < (n : ℝ) := by
      exact_mod_cast lt_of_le_of_lt (le_max_left N 1) hn
    have hMn : M + 1 < (n : ℝ) := lt_trans hN hNn
    have hkey : (n : ℝ) - 1 ≤ (n : ℝ) ^ 2 - (n : ℝ) := by nlinarith
    simp only [gt_iff_lt]
    linarith
  · intro M
    obtain ⟨N, hN⟩ := exists_nat_gt M
    refine ⟨max N 1, fun n hn => ?_⟩
    have hn1 : 1 ≤ n := le_of_lt (lt_of_le_of_lt (le_max_right N 1) hn)
    have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
    have hNn : (N : ℝ) < (n : ℝ) := by
      exact_mod_cast lt_of_le_of_lt (le_max_left N 1) hn
    have heq : (n : ℝ) ^ 2 / (n : ℝ) = (n : ℝ) := by
      field_simp
    simp only [gt_iff_lt, heq]
    exact lt_trans hN hNn

/-- **4.12.2. Megjegyzés, 3. példa.** `dₙ = n` és `d̄ₙ = n²` esetén `dₙ - d̄ₙ = n(1-n) → -∞`
és `dₙ/d̄ₙ → 0`. -/
theorem pelda_4_12_2_3 :
    MinuszVegtelenbeDivergal (fun n : ℕ => (n : ℝ) - (n : ℝ) ^ 2) ∧
      HatarErtek (fun n : ℕ => (n : ℝ) / (n : ℝ) ^ 2) 0 := by
  constructor
  · have h := negalt_divergal pelda_4_12_2_2.1
    have heq : (fun n : ℕ => -((n : ℝ) ^ 2 - (n : ℝ))) = fun n : ℕ => (n : ℝ) - (n : ℝ) ^ 2 := by
      funext n; ring
    rwa [heq] at h
  · have heq : (fun n : ℕ => (n : ℝ) / (n : ℝ) ^ 2) = fun n : ℕ => 1 / (n : ℝ) := by
      funext n
      rcases Nat.eq_zero_or_pos n with h | h
      · simp [h]
      · have hn0 : (n : ℝ) ≠ 0 := by
          have hpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast h
          exact ne_of_gt hpos
        field_simp
    rw [heq]
    exact egy_per_n_hatarerteke

/-! ## 4.14.7. Megjegyzés — a zártság lényeges -/

/-- **4.14.7. Megjegyzés.** A 4.14.6. Tételben („egymásba skatulyázott zárt intervallumok”)
a zártság fontos: nyitott intervallumokra nem igaz az állítás, lásd a `(0, 1/n)`
intervallumokat, amelyeknek nincs közös pontjuk. -/
theorem nyitott_skatulyazott_intervallumok_ures :
    ⋂ n : ℕ, Set.Ioo (0 : ℝ) (1 / ((n : ℝ) + 1)) = ∅ := by
  ext x
  simp only [Set.mem_iInter, Set.mem_Ioo, Set.mem_empty_iff_false, iff_false, not_forall]
  by_contra hcon
  push_neg at hcon
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / x)
  have hx0 : 0 < x := (hcon 0).1
  have hlt : x < 1 / ((N : ℝ) + 1) := (hcon N).2
  have hN1 : 1 / x < (N : ℝ) + 1 := by linarith
  rw [div_lt_iff₀ hx0] at hN1
  rw [lt_div_iff₀ (by positivity)] at hlt
  linarith

/-! ## 4.14.11. Megjegyzés — a torlódási pontok halmazának határai -/

/-- **4.14.11. Megjegyzés.** A 4.14.10. Tételt „lehetne úgy is bizonyítani, hogy vesszük a
torlódási pontok felső határát”: a legnagyobb torlódási pont valóban a torlódási pontok
halmazának felső határa. -/
theorem limeszSzuperior_eq_sSup {a : Sorozat} {L : ℝ} (h : LimeszSzuperior a L) :
    L = sSup {A : ℝ | TorlodasiPont a A} :=
  (IsGreatest.csSup_eq ⟨h.1, fun _ hB => h.2 _ hB⟩).symm

/-- **4.14.11. Megjegyzés.** Hasonlóan: a legkisebb torlódási pont a torlódási pontok
halmazának alsó határa. -/
theorem limeszInferior_eq_sInf {a : Sorozat} {l : ℝ} (h : LimeszInferior a l) :
    l = sInf {A : ℝ | TorlodasiPont a A} :=
  (IsLeast.csInf_eq ⟨h.1, fun _ hB => h.2 _ hB⟩).symm

end Ch04
end Leindler
