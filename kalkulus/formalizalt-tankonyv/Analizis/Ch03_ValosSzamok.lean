import Mathlib

/-!
# Leindler László: Analízis — 3. fejezet: A valós számok

Ez a fájl a tankönyv 3. fejezetének (5–12. oldal) formalizálása.

A könyv a valós számokat *axiomatikusan* vezeti be: az 1–9. axióma a műveleti,
illetve rendezési axiómák, a 10. axióma pedig a teljességi (legkisebb felső korlát)
axióma.  A Lean/Mathlib `ℝ` típusa pontosan ilyen struktúra (teljesen rendezett
test), ezért az axiómákat itt **tételként** mondjuk ki `ℝ`-re: ezzel igazoljuk,
hogy a Mathlib `ℝ`-je valóban a Leindler-féle axiómarendszernek tesz eleget, s így
a könyv további fejezetei jogosan formalizálhatók `ℝ` felett.

A szakaszszámozás és a tételek elnevezése a könyvet követi.
-/

namespace Leindler
namespace Ch03

open scoped BigOperators

/-! ## 3.1. A valós számok axiómái -/

/-! ### Műveleti axiómák -/

/-- **1. Axióma (Kommutatív törvény).** `x + y = y + x`, `x·y = y·x`. -/
theorem axioma1_kommutativ (x y : ℝ) : x + y = y + x ∧ x * y = y * x :=
  ⟨add_comm x y, mul_comm x y⟩

/-- **2. Axióma (Asszociatív törvény).** `x + (y + z) = (x + y) + z`, `x(yz) = (xy)z`. -/
theorem axioma2_asszociativ (x y z : ℝ) :
    x + (y + z) = (x + y) + z ∧ x * (y * z) = (x * y) * z :=
  ⟨(add_assoc x y z).symm, (mul_assoc x y z).symm⟩

/-- **3. Axióma (Disztributív törvény).** `x(y + z) = xy + xz`. -/
theorem axioma3_disztributiv (x y z : ℝ) : x * (y + z) = x * y + x * z :=
  mul_add x y z

/-- **4. Axióma (Egységelemek létezése).** Létezik két különböző valós szám, `0` és `1`,
úgy, hogy bármely valós számra `0 + x = x + 0 = x` és `1·x = x·1 = x`. -/
theorem axioma4_egysegelemek :
    (0 : ℝ) ≠ 1 ∧ ∀ x : ℝ, (0 + x = x ∧ x + 0 = x) ∧ (1 * x = x ∧ x * 1 = x) :=
  ⟨zero_ne_one, fun x => ⟨⟨zero_add x, add_zero x⟩, ⟨one_mul x, mul_one x⟩⟩⟩

/-- **5. Axióma (Negatívok létezése).** Bármely `x`-hez létezik olyan `y`, hogy
`x + y = y + x = 0`.  A könyv megjegyzése szerint ez az `y` egyértelmű; ezt is
kimondjuk (`∃!`). -/
theorem axioma5_negativok (x : ℝ) : ∃! y : ℝ, x + y = 0 ∧ y + x = 0 := by
  refine ⟨-x, ⟨add_neg_cancel x, neg_add_cancel x⟩, ?_⟩
  rintro y ⟨hy, -⟩
  linarith

/-- **6. Axióma (Reciprok létezése).** Bármely `0`-tól különböző `x`-hez létezik
(egyértelmű) `y`, melyre `xy = yx = 1`. -/
theorem axioma6_reciprok {x : ℝ} (hx : x ≠ 0) : ∃! y : ℝ, x * y = 1 ∧ y * x = 1 := by
  refine ⟨x⁻¹, ⟨mul_inv_cancel₀ hx, inv_mul_cancel₀ hx⟩, ?_⟩
  rintro y ⟨hy, -⟩
  field_simp at hy ⊢
  linarith [hy]

/-! ### Rendezési axiómák

A könyv a valós számok egy részhalmazának *pozitivitás* tulajdonságát teszi fel.
A formalizálásban a `0 < x` reláció játssza a "pozitív" szerepét. -/

/-- **7. Axióma (Pozitivitástartás).** Ha `x` és `y` pozitív, akkor `x + y` és `xy`
is pozitív. -/
theorem axioma7_pozitivitastarto {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    0 < x + y ∧ 0 < x * y :=
  ⟨add_pos hx hy, mul_pos hx hy⟩

/-- **8. Axióma (Előjel axióma).** Minden `0`-tól különböző valós szám esetén vagy `x`,
vagy `-x` pozitív. -/
theorem axioma8_elojel {x : ℝ} (hx : x ≠ 0) : 0 < x ∨ 0 < -x := by
  rcases lt_trichotomy 0 x with h | h | h
  · exact Or.inl h
  · exact absurd h.symm hx
  · exact Or.inr (by linarith)

/-- **9. Axióma.** A `0` szám nem pozitív. -/
theorem axioma9_nulla_nem_pozitiv : ¬ (0 : ℝ) < 0 := lt_irrefl 0

/-- **Definíció (egyenlőtlenség).** `x < y` azt jelenti, hogy `y - x` pozitív. -/
theorem kisebb_def (x y : ℝ) : x < y ↔ 0 < y - x := by
  constructor <;> intro h <;> linarith

/-! ### Felső korlát, felső határ, teljességi axióma -/

/-- **Definíció.** `K` felső korlátja az `S` valós számhalmaznak, ha `S` minden `x`
elemére `x ≤ K`. -/
def FelsoKorlat (S : Set ℝ) (K : ℝ) : Prop := ∀ x ∈ S, x ≤ K

/-- **Definíció.** Az `S` halmaz *felülről korlátos*, ha van felső korlátja. -/
def FelulrolKorlatos (S : Set ℝ) : Prop := ∃ K, FelsoKorlat S K

/-- **Definíció.** `K` az `S` halmaz *legkisebb felső korlátja* (felső határa), ha `K`
felső korlát, és bármely `K' < K` szám már nem felső korlátja `S`-nek, azaz van olyan
`x ∈ S`, hogy `x > K'`. -/
def LegkisebbFelsoKorlat (S : Set ℝ) (K : ℝ) : Prop :=
  FelsoKorlat S K ∧ ∀ K' < K, ∃ x ∈ S, K' < x

/-- A szuprémum a fenti értelemben legkisebb felső korlát. -/
theorem sSup_legkisebbFelsoKorlat {S : Set ℝ} (hne : S.Nonempty) (hbdd : BddAbove S) :
    LegkisebbFelsoKorlat S (sSup S) := by
  refine ⟨fun x hx => le_csSup hbdd hx, fun K' hK' => ?_⟩
  by_contra hcon
  push_neg at hcon
  exact absurd (csSup_le hne hcon) (not_le.mpr hK')

/-- **10. Axióma (Teljességi axióma).** Ha `S` a valós számok nem üres, felülről
korlátos halmaza, akkor létezik egyértelműen meghatározott valós szám, amely `S`
legkisebb felső korlátja. -/
theorem axioma10_teljessegi {S : Set ℝ} (hne : S.Nonempty) (hb : FelulrolKorlatos S) :
    ∃! K : ℝ, LegkisebbFelsoKorlat S K := by
  obtain ⟨M, hM⟩ := hb
  have hbdd : BddAbove S := ⟨M, fun x hx => hM x hx⟩
  refine ⟨sSup S, sSup_legkisebbFelsoKorlat hne hbdd, ?_⟩
  rintro K ⟨hK1, hK2⟩
  by_contra hne'
  rcases lt_or_gt_of_ne hne' with h | h
  · obtain ⟨x, hx, hlt⟩ := (sSup_legkisebbFelsoKorlat hne hbdd).2 K h
    exact absurd (hK1 x hx) (not_le.mpr hlt)
  · obtain ⟨x, hx, hlt⟩ := hK2 _ h
    exact absurd (le_csSup hbdd hx) (not_le.mpr hlt)

/-! ## 3.3. További fogalmak

### Az egyenlőtlenségekre vonatkozó legfontosabb szabályok -/

/-- **1. A trichotómia törvénye.** `a < b`, `b < a`, `a = b` közül csak egy teljesülhet. -/
theorem trichotomia (a b : ℝ) :
    (a < b ∧ ¬ b < a ∧ a ≠ b) ∨ (¬ a < b ∧ b < a ∧ a ≠ b) ∨ (¬ a < b ∧ ¬ b < a ∧ a = b) := by
  rcases lt_trichotomy a b with h | h | h
  · exact Or.inl ⟨h, asymm h, ne_of_lt h⟩
  · exact Or.inr (Or.inr ⟨by simp [h], by simp [h], h⟩)
  · exact Or.inr (Or.inl ⟨asymm h, h, (ne_of_lt h).symm⟩)

/-- **2. A tranzitivitás törvénye.** Ha `a < b` és `b < c`, akkor `a < c`. -/
theorem tranzitivitas {a b c : ℝ} (h₁ : a < b) (h₂ : b < c) : a < c := h₁.trans h₂

/-- **3. Az összeadás monotonitási törvénye.** Ha `a < b`, akkor `a + c < b + c`. -/
theorem osszeadas_monotonitas {a b : ℝ} (h : a < b) (c : ℝ) : a + c < b + c := by linarith

/-- **4. A szorzás monotonitási törvénye.** Ha `a < b` és `c > 0`, akkor `ac < bc`. -/
theorem szorzas_monotonitas {a b c : ℝ} (h : a < b) (hc : 0 < c) : a * c < b * c :=
  mul_lt_mul_of_pos_right h hc

/-- A könyvben említett további szabály: ha `a < b`, akkor `-a > -b`. -/
theorem negalas_forditja {a b : ℝ} (h : a < b) : -b < -a := by linarith

/-- A könyvben említett további szabály: ha `a < c` és `b < d`, akkor `a + b < c + d`. -/
theorem osszeg_becsles {a b c d : ℝ} (h₁ : a < c) (h₂ : b < d) : a + b < c + d := by linarith

/-- A könyvben említett további szabály: ha `1 < a`, akkor `1/a < 1`. -/
theorem reciprok_egynel_kisebb {a : ℝ} (h : 1 < a) : 1 / a < 1 := by
  rw [div_lt_one (by linarith)]; exact h

/-! ### Abszolút érték -/

/-- **Definíció.** Az `a` valós szám abszolút értéke `a`, ha `a > 0`; `0`, ha `a = 0`;
és `-a`, ha `a < 0`. -/
noncomputable def abszolutErtek (a : ℝ) : ℝ :=
  if 0 < a then a else if a = 0 then 0 else -a

/-- A könyv definíciója szerinti abszolút érték megegyezik a `|·|` függvénnyel. -/
theorem abszolutErtek_eq_abs (a : ℝ) : abszolutErtek a = |a| := by
  unfold abszolutErtek
  rcases lt_trichotomy a 0 with h | h | h
  · rw [if_neg (by linarith), if_neg (by linarith), abs_of_neg h]
  · simp [h]
  · rw [if_pos h, abs_of_pos h]

/-- **Tétel (Háromszög-egyenlőtlenség).** `|a + b| ≤ |a| + |b|`.

A könyv bizonyítását ("Igazolandó!") az `a + b` előjele szerinti esetszétválasztással
végezzük el: mindkét esetben a `±a ≤ |a|`, `±b ≤ |b|` becslésekre támaszkodunk. -/
theorem haromszog_egyenlotlenseg (a b : ℝ) : |a + b| ≤ |a| + |b| := by
  rcases le_total 0 (a + b) with h | h
  · rw [abs_of_nonneg h]
    exact add_le_add (le_abs_self a) (le_abs_self b)
  · rw [abs_of_nonpos h, neg_add]
    exact add_le_add (neg_le_abs a) (neg_le_abs b)

/-- A háromszög-egyenlőtlenség szokásos következménye: `||a| - |b|| ≤ |a - b|`. -/
theorem forditott_haromszog (a b : ℝ) : |(|a| - |b|)| ≤ |a - b| :=
  abs_abs_sub_abs_le_abs_sub a b

/-! ### Pozitív és negatív rész -/

/-- **Definíció.** Az `a` valós szám pozitív része: `a⁺ = a`, ha `a ≥ 0`, és `0`, ha `a < 0`. -/
noncomputable def pozitivResz (a : ℝ) : ℝ := if 0 ≤ a then a else 0

/-- **Definíció.** Az `a` valós szám negatív része: `a⁻ = 0`, ha `a > 0`, és `-a`, ha `a ≤ 0`. -/
noncomputable def negativResz (a : ℝ) : ℝ := if 0 < a then 0 else -a

/-- "Nyilvánvaló, hogy" `a = a⁺ - a⁻`. -/
theorem resz_kulonbseg (a : ℝ) : a = pozitivResz a - negativResz a := by
  unfold pozitivResz negativResz
  rcases lt_trichotomy a 0 with h | h | h
  · rw [if_neg (by linarith), if_neg (by linarith)]; ring
  · simp [h]
  · rw [if_pos (le_of_lt h), if_pos h]; ring

/-- "Nyilvánvaló, hogy" `|a| = a⁺ + a⁻`. -/
theorem resz_osszeg (a : ℝ) : |a| = pozitivResz a + negativResz a := by
  unfold pozitivResz negativResz
  rcases lt_trichotomy a 0 with h | h | h
  · rw [if_neg (by linarith), if_neg (by linarith), abs_of_neg h]; ring
  · simp [h]
  · rw [if_pos (le_of_lt h), if_pos h, abs_of_pos h]; ring

/-- Mindkét rész nemnegatív. -/
theorem resz_nemnegativ (a : ℝ) : 0 ≤ pozitivResz a ∧ 0 ≤ negativResz a := by
  unfold pozitivResz negativResz
  constructor
  · split
    · assumption
    · exact le_refl 0
  · split
    · exact le_refl 0
    · next h => linarith [not_lt.mp h]

/-! ### Egész rész és tört rész -/

/-- **Definíció.** Az `a` szám egész része a nála nem nagyobb legnagyobb egész szám,
jele `[a]`.  (Mathlib: `⌊a⌋`.) -/
theorem egeszResz_karakterizacio (a : ℝ) (m : ℤ) : m = ⌊a⌋ ↔ ((m : ℝ) ≤ a ∧ a < m + 1) := by
  constructor
  · rintro rfl
    exact ⟨Int.floor_le a, Int.lt_floor_add_one a⟩
  · rintro ⟨h₁, h₂⟩
    exact (Int.floor_eq_iff.mpr ⟨h₁, h₂⟩).symm

/-- **Definíció.** Az `a` szám tört része `a - [a]`, jele `{a}`; erre `0 ≤ {a} < 1`. -/
theorem tortResz_hatarok (a : ℝ) : 0 ≤ a - ⌊a⌋ ∧ a - ⌊a⌋ < 1 :=
  ⟨by linarith [Int.floor_le a], by linarith [Int.lt_floor_add_one a]⟩

/-! ## 3.4. További összefüggések -/

/-- Az összeadás egyszerűsítési törvénye: ha `a + b = a + c`, akkor `b = c`. -/
theorem osszeadas_egyszerusites {a b c : ℝ} (h : a + b = a + c) : b = c := by linarith

/-- `-(-a) = a`. -/
theorem neg_neg_valos (a : ℝ) : -(-a) = a := neg_neg a

/-- `a(b - c) = ab - ac`. -/
theorem szorzas_kivonas (a b c : ℝ) : a * (b - c) = a * b - a * c := mul_sub a b c

/-- Ha `a ≠ 0`, akkor `(a⁻¹)⁻¹ = a`. -/
theorem inv_inv_valos (a : ℝ) : (a⁻¹)⁻¹ = a := inv_inv a

/-- **Tétel (Arkhimédeszi axióma).** Bármely pozitív `x` és `y` szám esetén megadható
olyan `n` természetes szám, hogy `n·x > y`. -/
theorem arkhimedeszi {x y : ℝ} (hx : 0 < x) : ∃ n : ℕ, (n : ℝ) * x > y := by
  obtain ⟨n, hn⟩ := exists_nat_gt (y / x)
  exact ⟨n, by rwa [gt_iff_lt, ← div_lt_iff₀ hx]⟩

/-- **Tétel (Newton-féle binomiális tétel).**
`(a+b)^n = ∑_{k=0}^{n} C(n,k) a^{n-k} b^k`.  ("Ezt teljes indukcióval könnyű bizonyítani.") -/
theorem binomialis_tetel (a b : ℝ) (n : ℕ) :
    (a + b) ^ n = ∑ k ∈ Finset.range (n + 1), (n.choose k : ℝ) * a ^ (n - k) * b ^ k := by
  rw [add_comm a b, add_pow]
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

/-- A binomiális együtthatók alapösszefüggése (Pascal-szabály):
`C(n,k) + C(n,k+1) = C(n+1,k+1)`. -/
theorem pascal_szabaly (n k : ℕ) : n.choose k + n.choose (k + 1) = (n + 1).choose (k + 1) :=
  (Nat.choose_succ_succ n k).symm

/-- A binomiális együtthatók szimmetriája: `C(n,k) = C(n, n-k)`, ha `k ≤ n`. -/
theorem binom_szimmetria {n k : ℕ} (h : k ≤ n) : n.choose k = n.choose (n - k) :=
  (Nat.choose_symm h).symm

/-- A binomiális együtthatók összege: `∑_{k=0}^n C(n,k) = 2^n`. -/
theorem binom_osszeg (n : ℕ) : ∑ k ∈ Finset.range (n + 1), n.choose k = 2 ^ n :=
  Nat.sum_range_choose n

/-! ## 3.5. Környezet és intervallum -/

/-- **Definíció.** Nyitott intervallum: az `a < x < b` feltételt kielégítő `x` számok
halmaza, jele `(a,b)`. -/
def nyitottIntervallum (a b : ℝ) : Set ℝ := {x : ℝ | a < x ∧ x < b}

/-- **Definíció.** Zárt intervallum: az `a ≤ x ≤ b` feltételt kielégítő `x`-ek halmaza. -/
def zartIntervallum (a b : ℝ) : Set ℝ := {x : ℝ | a ≤ x ∧ x ≤ b}

/-- **Definíció.** Balról zárt, jobbról nyitott intervallum. -/
def balrolZartIntervallum (a b : ℝ) : Set ℝ := {x : ℝ | a ≤ x ∧ x < b}

/-- **Definíció.** Balról nyitott, jobbról zárt intervallum. -/
def jobbrolZartIntervallum (a b : ℝ) : Set ℝ := {x : ℝ | a < x ∧ x ≤ b}

theorem nyitottIntervallum_eq (a b : ℝ) : nyitottIntervallum a b = Set.Ioo a b := rfl
theorem zartIntervallum_eq (a b : ℝ) : zartIntervallum a b = Set.Icc a b := rfl

/-- "Ha `a = b`, akkor elfajult intervallumról beszélünk": a nyitott intervallum ilyenkor
üres, a zárt pedig egyetlen pontból áll. -/
theorem elfajult_intervallum (a : ℝ) :
    nyitottIntervallum a a = ∅ ∧ zartIntervallum a a = {a} := by
  constructor
  · ext x
    simp only [nyitottIntervallum, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
    intro h
    linarith
  · ext x
    simp only [zartIntervallum, Set.mem_setOf_eq, Set.mem_singleton_iff]
    exact ⟨fun h => le_antisymm h.2 h.1, fun h => by simp [h]⟩

/-- **Definíció.** Az `x₀` pont *belső pontja* az `(a,b)` intervallumnak, ha `a < x₀ < b`. -/
def BelsoPont (a b x₀ : ℝ) : Prop := a < x₀ ∧ x₀ < b

/-- **Definíció.** Az `x₀` pont *környezetén* olyan nyitott intervallumot értünk,
amelynek `x₀` belső pontja. -/
def Kornyezet (x₀ : ℝ) (U : Set ℝ) : Prop :=
  ∃ a b : ℝ, a < x₀ ∧ x₀ < b ∧ U = nyitottIntervallum a b

/-- **Definíció.** Az `x₀` *szimmetrikus környezete* olyan környezete, amelynek `x₀` a
középpontja, azaz `(x₀ - r, x₀ + r)` alakú valamely `r > 0`-ra. -/
def SzimmetrikusKornyezet (x₀ : ℝ) (U : Set ℝ) : Prop :=
  ∃ r : ℝ, 0 < r ∧ U = nyitottIntervallum (x₀ - r) (x₀ + r)

/-- Minden szimmetrikus környezet valóban környezet. -/
theorem szimmetrikus_kornyezet_kornyezet {x₀ : ℝ} {U : Set ℝ}
    (h : SzimmetrikusKornyezet x₀ U) : Kornyezet x₀ U := by
  obtain ⟨r, hr, rfl⟩ := h
  exact ⟨x₀ - r, x₀ + r, by linarith, by linarith, rfl⟩

/-- Minden környezet tartalmaz szimmetrikus környezetet.  (Ez indokolja, hogy a
konvergencia definíciójában elég szimmetrikus környezetekkel dolgozni.) -/
theorem kornyezet_tartalmaz_szimmetrikusat {x₀ : ℝ} {U : Set ℝ} (h : Kornyezet x₀ U) :
    ∃ V, SzimmetrikusKornyezet x₀ V ∧ V ⊆ U := by
  obtain ⟨a, b, ha, hb, rfl⟩ := h
  refine ⟨nyitottIntervallum (x₀ - min (x₀ - a) (b - x₀)) (x₀ + min (x₀ - a) (b - x₀)),
    ⟨min (x₀ - a) (b - x₀), lt_min (by linarith) (by linarith), rfl⟩, ?_⟩
  rintro x ⟨h₁, h₂⟩
  constructor
  · have : min (x₀ - a) (b - x₀) ≤ x₀ - a := min_le_left _ _
    linarith
  · have : min (x₀ - a) (b - x₀) ≤ b - x₀ := min_le_right _ _
    linarith

/-- **Definíció.** `x₀` baloldali környezete egy `(a, x₀]` alakú intervallum. -/
def BaloldaliKornyezet (x₀ : ℝ) (U : Set ℝ) : Prop :=
  ∃ a : ℝ, a < x₀ ∧ U = jobbrolZartIntervallum a x₀

/-- **Definíció.** `x₀` jobb oldali környezete egy `[x₀, b)` alakú intervallum. -/
def JobboldaliKornyezet (x₀ : ℝ) (U : Set ℝ) : Prop :=
  ∃ b : ℝ, x₀ < b ∧ U = balrolZartIntervallum x₀ b

end Ch03
end Leindler
