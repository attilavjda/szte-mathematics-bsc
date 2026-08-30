import Mathlib

/-!
# Szabó László: Bevezetés a lineáris algebrába — 1. fejezet: Bevezetés

A jegyzet 1. fejezetének (1–3. oldal) formalizálása: a *számtest* fogalma, a
számtestek alaptulajdonságai, valamint a `∑` és `∏` jelekkel kapcsolatos
alapösszefüggések.
-/

namespace SzaboLinAlg
namespace Ch01

open scoped BigOperators

/-! ## 1.1. A számtest fogalma -/

/-- **1.1. Definíció.** *Számtesteknek* nevezzük a komplex számok halmazának olyan
legalább kételemű részhalmazait, melyek zártak a négy alapműveletre, azaz tartalmazzák
bármely két elemük összegét, különbségét, szorzatát és hányadosát (amennyiben az osztó
nem 0).  A számtestek elemeit skalároknak is hívjuk. -/
structure Szamtest where
  /-- A számtest alaphalmaza. -/
  carrier : Set ℂ
  /-- Legalább kételemű. -/
  ketelemu : ∃ x ∈ carrier, ∃ y ∈ carrier, x ≠ y
  /-- Zárt az összeadásra. -/
  add_mem : ∀ x ∈ carrier, ∀ y ∈ carrier, x + y ∈ carrier
  /-- Zárt a kivonásra. -/
  sub_mem : ∀ x ∈ carrier, ∀ y ∈ carrier, x - y ∈ carrier
  /-- Zárt a szorzásra. -/
  mul_mem : ∀ x ∈ carrier, ∀ y ∈ carrier, x * y ∈ carrier
  /-- Zárt az osztásra (nem nulla osztó esetén). -/
  div_mem : ∀ x ∈ carrier, ∀ y ∈ carrier, y ≠ 0 → x / y ∈ carrier

namespace Szamtest

variable (T : Szamtest)

instance : Membership ℂ Szamtest := ⟨fun T z => z ∈ T.carrier⟩

theorem mem_def {z : ℂ} : z ∈ T ↔ z ∈ T.carrier := Iff.rfl

/-- "Minden számtest tartalmaz 0-tól különböző elemet, amit önmagával elosztva 1-et
kapunk": tehát `1 ∈ T`. -/
theorem one_mem : (1 : ℂ) ∈ T := by
  obtain ⟨x, hx, y, hy, hxy⟩ := T.ketelemu
  have hd : x - y ∈ T.carrier := T.sub_mem x hx y hy
  have hne : x - y ≠ 0 := sub_ne_zero.mpr hxy
  have := T.div_mem _ hd _ hd hne
  rwa [div_self hne] at this

/-- Minden számtest tartalmazza a `0`-t. -/
theorem zero_mem : (0 : ℂ) ∈ T := by
  have h1 := T.one_mem
  simpa using T.sub_mem 1 h1 1 h1

/-- Minden számtest tartalmazza a természetes számokat. -/
theorem natCast_mem (n : ℕ) : (n : ℂ) ∈ T := by
  induction n with
  | zero => simpa using T.zero_mem
  | succ k ih =>
      have := T.add_mem _ ih _ T.one_mem
      simpa using this

/-- Minden számtest tartalmazza az egész számokat. -/
theorem intCast_mem (n : ℤ) : (n : ℂ) ∈ T := by
  rcases n with m | m
  · simpa using T.natCast_mem m
  · have := T.sub_mem 0 T.zero_mem ((m : ℂ) + 1) (T.add_mem _ (T.natCast_mem m) _ T.one_mem)
    simpa [Int.negSucc_eq] using this

/-- **Tétel.** "Minden számtest tartalmazza a racionális számok `ℚ` halmazát." -/
theorem ratCast_mem (q : ℚ) : (q : ℂ) ∈ T := by
  have hnum : ((q.num : ℤ) : ℂ) ∈ T.carrier := T.intCast_mem q.num
  have hden : ((q.den : ℕ) : ℂ) ∈ T.carrier := T.natCast_mem q.den
  have hne : ((q.den : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr q.den_nz
  have := T.div_mem _ hnum _ hden hne
  rwa [← Rat.cast_def] at this

/-- Minden számtest zárt az ellentettképzésre. -/
theorem neg_mem {x : ℂ} (hx : x ∈ T) : -x ∈ T := by
  simpa using T.sub_mem 0 T.zero_mem x hx

/-- Minden számtest zárt az invertálásra. -/
theorem inv_mem {x : ℂ} (hx : x ∈ T) (hx0 : x ≠ 0) : x⁻¹ ∈ T := by
  simpa using T.div_mem 1 T.one_mem x hx hx0

/-- Egy számtest a komplex számtest résztestét alkotja (Mathlib-értelemben). -/
def toSubfield : Subfield ℂ where
  carrier := T.carrier
  mul_mem' := fun hx hy => T.mul_mem _ hx _ hy
  one_mem' := T.one_mem
  add_mem' := fun hx hy => T.add_mem _ hx _ hy
  zero_mem' := T.zero_mem
  neg_mem' := fun hx => T.neg_mem hx
  inv_mem' := fun x hx => by
    rcases eq_or_ne x 0 with rfl | hx0
    · simpa using T.zero_mem
    · exact T.inv_mem hx hx0

end Szamtest

/-! ### Példák számtestekre -/

/-- A komplex számok teste számtest. -/
def szamtestC : Szamtest where
  carrier := Set.univ
  ketelemu := ⟨0, trivial, 1, trivial, zero_ne_one⟩
  add_mem := fun _ _ _ _ => trivial
  sub_mem := fun _ _ _ _ => trivial
  mul_mem := fun _ _ _ _ => trivial
  div_mem := fun _ _ _ _ _ => trivial

/-- A valós számok teste számtest (a komplex számok valós részhalmazaként). -/
def szamtestR : Szamtest where
  carrier := {z : ℂ | z.im = 0}
  ketelemu := ⟨0, by simp, 1, by simp, zero_ne_one⟩
  add_mem := fun x hx y hy => by simp only [Set.mem_setOf_eq] at *; simp [hx, hy]
  sub_mem := fun x hx y hy => by simp only [Set.mem_setOf_eq] at *; simp [hx, hy]
  mul_mem := fun x hx y hy => by simp only [Set.mem_setOf_eq] at *; simp [hx, hy]
  div_mem := fun x hx y hy _ => by
    simp only [Set.mem_setOf_eq] at *
    simp [Complex.div_im, hx, hy]

/-- A racionális számok teste számtest. -/
def szamtestQ : Szamtest where
  carrier := Set.range ((↑) : ℚ → ℂ)
  ketelemu := ⟨0, ⟨0, by simp⟩, 1, ⟨1, by simp⟩, zero_ne_one⟩
  add_mem := by rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩; exact ⟨a + b, by push_cast; ring⟩
  sub_mem := by rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩; exact ⟨a - b, by push_cast; ring⟩
  mul_mem := by rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩; exact ⟨a * b, by push_cast; ring⟩
  div_mem := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩ hb
    exact ⟨a / b, by push_cast; ring⟩

/-- A `{a + b√2 : a, b ∈ ℚ}` halmaz is számtest. -/
def szamtestQsqrt2 : Szamtest where
  carrier := {z : ℂ | ∃ a b : ℚ, z = (a : ℂ) + (b : ℂ) * (Real.sqrt 2 : ℝ)}
  ketelemu := ⟨0, ⟨0, 0, by simp⟩, 1, ⟨1, 0, by simp⟩, zero_ne_one⟩
  add_mem := by
    rintro _ ⟨a, b, rfl⟩ _ ⟨c, d, rfl⟩
    exact ⟨a + c, b + d, by push_cast; ring⟩
  sub_mem := by
    rintro _ ⟨a, b, rfl⟩ _ ⟨c, d, rfl⟩
    exact ⟨a - c, b - d, by push_cast; ring⟩
  mul_mem := by
    rintro _ ⟨a, b, rfl⟩ _ ⟨c, d, rfl⟩
    refine ⟨a * c + 2 * (b * d), a * d + b * c, ?_⟩
    have hs : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
      rw [sq, ← Complex.ofReal_mul, ← Real.sqrt_mul_self (by norm_num : (0:ℝ) ≤ 2)]
      norm_num
    push_cast
    linear_combination ((b : ℂ) * (d : ℂ)) * hs
  div_mem := by
    rintro _ ⟨a, b, rfl⟩ _ ⟨c, d, rfl⟩ hne
    have hs : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
      rw [sq, ← Complex.ofReal_mul, ← Real.sqrt_mul_self (by norm_num : (0:ℝ) ≤ 2)]
      norm_num
    -- A nevező "konjugáltjával" bővítünk; ehhez kell, hogy `c² - 2d² ≠ 0`,
    -- ami √2 irracionalitásából következik.
    have hden : (c : ℚ) ^ 2 - 2 * (d : ℚ) ^ 2 ≠ 0 := by
      intro h
      rcases eq_or_ne d 0 with rfl | hd0
      · have hc : c = 0 := by
          have : (c : ℚ) ^ 2 = 0 := by simpa using h
          exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
        exact hne (by simp [hc])
      · have h' : (c : ℝ) ^ 2 - 2 * (d : ℝ) ^ 2 = 0 := by exact_mod_cast h
        have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd0
        have h2 : ((c / d : ℚ) : ℝ) ^ 2 = 2 := by
          push_cast
          field_simp
          linarith
        have heq : Real.sqrt 2 = |((c / d : ℚ) : ℝ)| := by rw [← h2, Real.sqrt_sq_eq_abs]
        have hirr : Irrational (Real.sqrt 2) := Nat.prime_two.irrational_sqrt
        rw [heq] at hirr
        exact hirr ⟨|c / d|, by push_cast; simp⟩
    have hdenC : ((c : ℂ) ^ 2 - 2 * (d : ℂ) ^ 2) ≠ 0 := by exact_mod_cast hden
    refine ⟨(a * c - 2 * b * d) / (c ^ 2 - 2 * d ^ 2), (b * c - a * d) / (c ^ 2 - 2 * d ^ 2), ?_⟩
    rw [div_eq_iff hne]
    push_cast
    field_simp
    linear_combination ((a : ℂ) * (d : ℂ) ^ 2 - (b : ℂ) * (c : ℂ) * (d : ℂ)) * hs

/-! ## A `∑` és `∏` jelek használata -/

/-- "A `∑` jel használata során előfordulhat, hogy az összegnek nulla tagja van. …
Ilyenkor az összeg definíció szerint 0." -/
theorem ures_osszeg {K : Type*} [AddCommMonoid K] (f : ℕ → K) :
    ∑ i ∈ (∅ : Finset ℕ), f i = 0 := Finset.sum_empty

/-- "A nulla tényezős szorzat definíció szerint 1." -/
theorem ures_szorzat {K : Type*} [CommMonoid K] (f : ℕ → K) :
    ∏ i ∈ (∅ : Finset ℕ), f i = 1 := Finset.prod_empty

/-- Kettős összeg felcserélhetősége: előbb soronként, majd oszloponként összegezve
ugyanazt kapjuk:
`∑ᵢ (∑ⱼ aᵢⱼ) = ∑ⱼ (∑ᵢ aᵢⱼ)`. -/
theorem kettos_osszeg_csere {K : Type*} [AddCommMonoid K] (m n : ℕ) (a : ℕ → ℕ → K) :
    ∑ i ∈ Finset.range m, ∑ j ∈ Finset.range n, a i j
      = ∑ j ∈ Finset.range n, ∑ i ∈ Finset.range m, a i j :=
  Finset.sum_comm

/-- Az összegzés lineáris: `∑ᵢ (c · aᵢ) = c · ∑ᵢ aᵢ`. -/
theorem osszeg_skalarszoros {K : Type*} [Semiring K] (s : Finset ℕ) (c : K) (a : ℕ → K) :
    ∑ i ∈ s, c * a i = c * ∑ i ∈ s, a i := (Finset.mul_sum s a c).symm

/-- Két összeg szorzata kettős összeg:
`(∑ᵢ aᵢ)(∑ⱼ bⱼ) = ∑ᵢ ∑ⱼ aᵢbⱼ`. -/
theorem osszegek_szorzata {K : Type*} [CommSemiring K] (s t : Finset ℕ) (a b : ℕ → K) :
    (∑ i ∈ s, a i) * (∑ j ∈ t, b j) = ∑ i ∈ s, ∑ j ∈ t, a i * b j := by
  rw [Finset.sum_mul_sum]

/-- A jegyzet 1. fejezetét záró Vandermonde-szorzat kételemű esete és általános alakja
közti kapcsolat: a `∏_{1 ≤ i < j ≤ n} (aⱼ - aᵢ)` szorzat definíciója. -/
def vandermondeSzorzat {K : Type*} [CommRing K] (n : ℕ) (a : ℕ → K) : K :=
  ∏ j ∈ Finset.range n, ∏ i ∈ Finset.range j, (a j - a i)

/-- Két elemre a Vandermonde-szorzat `a₁ - a₀`. -/
theorem vandermonde_ket_elem {K : Type*} [CommRing K] (a : ℕ → K) :
    vandermondeSzorzat 2 a = a 1 - a 0 := by
  simp [vandermondeSzorzat, Finset.prod_range_succ]

/-- Három elemre a Vandermonde-szorzat `(a₁ - a₀)(a₂ - a₀)(a₂ - a₁)`. -/
theorem vandermonde_harom_elem {K : Type*} [CommRing K] (a : ℕ → K) :
    vandermondeSzorzat 3 a = (a 1 - a 0) * ((a 2 - a 0) * (a 2 - a 1)) := by
  simp [vandermondeSzorzat, Finset.prod_range_succ]

end Ch01
end SzaboLinAlg
