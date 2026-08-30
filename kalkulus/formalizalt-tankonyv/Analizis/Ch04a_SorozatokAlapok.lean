import Analizis.Ch03_ValosSzamok

/-!
# Leindler László: Analízis — 4. fejezet: Számsorozatok (4.1–4.8. szakasz)

A 4. fejezet első fele: a sorozat, a korlátosság, a monotonitás, a részsorozat és a
határérték fogalma, a nevezetes sorozatok határértékei, valamint a konvergens
sorozatok alaptulajdonságai (13–24. oldal).

**Indexelés.** A könyv a sorozatokat `n = 1, 2, …` szerint indexeli; a formalizálásban
`ℕ`-nel indexelünk (`n = 0, 1, 2, …`).  Ez a határértékkel kapcsolatos állításokat nem
befolyásolja, hiszen a 4.8.4. Következmény szerint véges sok tag elhagyása vagy
hozzávétele a konvergencián nem változtat.

**Küszöbszám.** A könyv `ν` küszöbszáma tetszőleges valós szám lehet; a 4.7.2. Tétel
utáni megjegyzés szerint "ha már választottunk egy alkalmas `ν`-t, akkor bármely ennél
nagyobb egész szám szintén alkalmas küszöbszám lesz".  Ezért a definíciókban `ν`-t
természetes számnak vesszük.
-/

namespace Leindler
namespace Ch04

open scoped BigOperators

/-! ## 4.2. A számsorozat fogalma -/

/-- **4.2.1. Definíció.** Számsorozat: minden természetes számhoz egy-egy valós számot
rendelő hozzárendelés. -/
abbrev Sorozat := ℕ → ℝ

/-! ## 4.3. Korlátos sorozatok -/

/-- **4.3.1. Definíció.** Az `{aₙ}` sorozat *felülről korlátos*, ha van olyan `K` szám,
hogy a sorozat minden tagja kisebb vagy egyenlő `K`-val. -/
def FelulrolKorlatos (a : Sorozat) : Prop := ∃ K : ℝ, ∀ n, a n ≤ K

/-- **4.3.1. Definíció.** Az `{aₙ}` sorozat *alulról korlátos*, ha van olyan `k` szám,
hogy a sorozat minden tagja nagyobb vagy egyenlő `k`-val. -/
def AlulrolKorlatos (a : Sorozat) : Prop := ∃ k : ℝ, ∀ n, k ≤ a n

/-- **4.3.1. Definíció.** A sorozat *korlátos*, ha alulról és felülről is korlátos. -/
def Korlatos (a : Sorozat) : Prop := AlulrolKorlatos a ∧ FelulrolKorlatos a

/-- Korlátosság ekvivalens alakja: `|aₙ| ≤ K` minden `n`-re. -/
theorem korlatos_iff_abs (a : Sorozat) : Korlatos a ↔ ∃ K : ℝ, ∀ n, |a n| ≤ K := by
  constructor
  · rintro ⟨⟨k, hk⟩, ⟨K, hK⟩⟩
    refine ⟨max |k| |K|, fun n => abs_le.mpr ⟨?_, ?_⟩⟩
    · have h1 : -|k| ≤ k := neg_abs_le k
      have h2 : |k| ≤ max |k| |K| := le_max_left _ _
      linarith [hk n]
    · exact le_trans (le_trans (hK n) (le_abs_self K)) (le_max_right _ _)
  · rintro ⟨K, hK⟩
    exact ⟨⟨-K, fun n => neg_le_of_abs_le (hK n)⟩, ⟨K, fun n => le_of_abs_le (hK n)⟩⟩

/-- **4.3.3. Definíció.** Az `{aₙ}` sorozat felülről nem korlátos azt jelenti, hogy
bármely `M` számhoz megadható olyan tag, amely `M`-nél nagyobb. -/
theorem nem_felulrol_korlatos_iff (a : Sorozat) :
    ¬ FelulrolKorlatos a ↔ ∀ M : ℝ, ∃ n, a n > M := by
  unfold FelulrolKorlatos
  push_neg
  rfl

/-- **4.3.4. Tétel.** Az alsó korlátok közt van legnagyobb.

*Bizonyítás.* A `{-aₙ}` sorozatra alkalmazzuk a teljességi axiómát: ha `k ≤ aₙ`, akkor
`-aₙ ≤ -k`, azaz `{-aₙ}` felülről korlátos, tehát felső korlátai közt van legkisebb;
jelölje ezt `-k*`.  Ekkor `k*` az `{aₙ}` legnagyobb alsó korlátja. -/
theorem also_korlatok_kozt_van_legnagyobb {a : Sorozat} (h : AlulrolKorlatos a) :
    ∃ ks : ℝ, (∀ n, ks ≤ a n) ∧ ∀ k : ℝ, (∀ n, k ≤ a n) → k ≤ ks := by
  obtain ⟨k, hk⟩ := h
  set S : Set ℝ := Set.range fun n => -a n with hSdef
  have hne : S.Nonempty := ⟨-a 0, ⟨0, rfl⟩⟩
  have hbdd : BddAbove S := ⟨-k, by rintro x ⟨n, rfl⟩; simpa using hk n⟩
  refine ⟨-sSup S, fun n => ?_, fun k' hk' => ?_⟩
  · have : -a n ≤ sSup S := le_csSup hbdd ⟨n, rfl⟩
    linarith
  · have : sSup S ≤ -k' := csSup_le hne (by rintro x ⟨n, rfl⟩; simpa using hk' n)
    linarith

/-- **4.3.5. Definíció.** Felülről korlátos sorozat legkisebb felső korlátja a sorozat
*felső határa* (szuprémuma). -/
def FelsoHatar (a : Sorozat) (K : ℝ) : Prop :=
  (∀ n, a n ≤ K) ∧ ∀ K' : ℝ, (∀ n, a n ≤ K') → K ≤ K'

/-- **4.3.5. Definíció.** Alulról korlátos sorozat legnagyobb alsó korlátja a sorozat
*alsó határa* (infimuma). -/
def AlsoHatar (a : Sorozat) (k : ℝ) : Prop :=
  (∀ n, k ≤ a n) ∧ ∀ k' : ℝ, (∀ n, k' ≤ a n) → k' ≤ k

/-- **4.3.6. Tétel.** Felülről korlátos sorozatnak van felső határa, alulról korlátos
sorozatnak van alsó határa; korlátos sorozatnak van alsó és felső határa egyaránt. -/
theorem van_felso_hatar {a : Sorozat} (h : FelulrolKorlatos a) : ∃ K, FelsoHatar a K := by
  obtain ⟨K, hK⟩ := h
  have hne : (Set.range a).Nonempty := ⟨a 0, ⟨0, rfl⟩⟩
  have hbdd : BddAbove (Set.range a) := ⟨K, by rintro x ⟨n, rfl⟩; exact hK n⟩
  exact ⟨sSup (Set.range a), fun n => le_csSup hbdd ⟨n, rfl⟩,
    fun K' hK' => csSup_le hne (by rintro x ⟨n, rfl⟩; exact hK' n)⟩

theorem van_also_hatar {a : Sorozat} (h : AlulrolKorlatos a) : ∃ k, AlsoHatar a k :=
  also_korlatok_kozt_van_legnagyobb h

theorem korlatos_hatarok {a : Sorozat} (h : Korlatos a) :
    (∃ k, AlsoHatar a k) ∧ ∃ K, FelsoHatar a K :=
  ⟨van_also_hatar h.1, van_felso_hatar h.2⟩

/-- **4.3.7. Tétel.** Ha az `{aₙ}` korlátos sorozatnak `K*` felső határa és `k*` alsó
határa, akkor a `{-aₙ}` sorozatnak `-K*` az alsó határa és `-k*` a felső határa. -/
theorem hatarok_negalasa {a : Sorozat} {K k : ℝ} (hK : FelsoHatar a K) (hk : AlsoHatar a k) :
    AlsoHatar (fun n => -a n) (-K) ∧ FelsoHatar (fun n => -a n) (-k) := by
  constructor
  · refine ⟨fun n => by simpa using neg_le_neg (hK.1 n), fun k' hk' => ?_⟩
    have : K ≤ -k' := hK.2 (-k') fun n => by linarith [hk' n]
    linarith
  · refine ⟨fun n => by simpa using neg_le_neg (hk.1 n), fun K' hK' => ?_⟩
    have : -K' ≤ k := hk.2 (-K') fun n => by linarith [hK' n]
    linarith

/-! ## 4.4. Monoton sorozatok -/

/-- **4.4.1. Definíció.** Az `{aₙ}` sorozat *növekedő*, ha `aₙ₋₁ ≤ aₙ`. -/
def Novekedo (a : Sorozat) : Prop := ∀ n, a n ≤ a (n + 1)

/-- **4.4.1. Definíció.** Az `{aₙ}` sorozat *szigorúan növekedő*, ha `aₙ₋₁ < aₙ`. -/
def SzigoruanNovekedo (a : Sorozat) : Prop := ∀ n, a n < a (n + 1)

/-- **4.4.1. Definíció.** Az `{aₙ}` sorozat *csökkenő*, ha `aₙ ≤ aₙ₋₁`. -/
def Csokkeno (a : Sorozat) : Prop := ∀ n, a (n + 1) ≤ a n

/-- **4.4.1. Definíció.** Az `{aₙ}` sorozat *szigorúan csökkenő*, ha `aₙ < aₙ₋₁`. -/
def SzigoruanCsokkeno (a : Sorozat) : Prop := ∀ n, a (n + 1) < a n

/-- **4.4.1. Definíció.** *Monoton* sorozat: növekedő vagy csökkenő. -/
def Monoton (a : Sorozat) : Prop := Novekedo a ∨ Csokkeno a

/-- Növekedő sorozatra `m ≤ n` esetén `aₘ ≤ aₙ`. -/
theorem novekedo_le {a : Sorozat} (h : Novekedo a) {m n : ℕ} (hmn : m ≤ n) : a m ≤ a n := by
  induction n with
  | zero => simp_all
  | succ k ih =>
      rcases Nat.lt_or_ge m (k + 1) with hlt | hge
      · exact le_trans (ih (Nat.lt_succ_iff.mp hlt)) (h k)
      · have : m = k + 1 := le_antisymm hmn hge
        simp [this]

/-- Csökkenő sorozatra `m ≤ n` esetén `aₙ ≤ aₘ`. -/
theorem csokkeno_le {a : Sorozat} (h : Csokkeno a) {m n : ℕ} (hmn : m ≤ n) : a n ≤ a m := by
  induction n with
  | zero => simp_all
  | succ k ih =>
      rcases Nat.lt_or_ge m (k + 1) with hlt | hge
      · exact le_trans (h k) (ih (Nat.lt_succ_iff.mp hlt))
      · have : m = k + 1 := le_antisymm hmn hge
        simp [this]

/-! ## 4.5. A részsorozat fogalma -/

/-- **4.5.1. Definíció.** Ha egy sorozatból végtelen sok tagot kiveszünk az eredeti
sorrendben, a sorozat egy *részsorozatát* kapjuk; az `{nₖ}` indexsorozat szükségképpen
szigorúan monoton növekedő. -/
def Reszsorozat (b a : Sorozat) : Prop :=
  ∃ φ : ℕ → ℕ, StrictMono φ ∧ b = a ∘ φ

/-- Szigorúan monoton indexsorozatra `k ≤ φ k`. -/
theorem strictMono_id_le {φ : ℕ → ℕ} (h : StrictMono φ) (k : ℕ) : k ≤ φ k :=
  h.le_apply

/-- Korlátos sorozat bármely részsorozata korlátos. -/
theorem reszsorozat_korlatos {a b : Sorozat} (hb : Reszsorozat b a) (ha : Korlatos a) :
    Korlatos b := by
  obtain ⟨φ, -, rfl⟩ := hb
  obtain ⟨⟨k, hk⟩, ⟨K, hK⟩⟩ := ha
  exact ⟨⟨k, fun n => hk _⟩, ⟨K, fun n => hK _⟩⟩

/-- Monoton (növekedő) sorozat bármely részsorozata is növekedő. -/
theorem reszsorozat_novekedo {a b : Sorozat} (hb : Reszsorozat b a) (ha : Novekedo a) :
    Novekedo b := by
  obtain ⟨φ, hφ, rfl⟩ := hb
  intro n
  exact novekedo_le ha (le_of_lt (hφ (Nat.lt_succ_self n)))

/-! ## 4.6. Sorozat határértéke -/

/-- **4.6.2. Definíció.** Az `{aₙ}` sorozat konvergens az `A` számhoz, ha bármely
`ε > 0`-hoz megadható olyan `ν` küszöbszám, hogy `n > ν` esetén `|aₙ - A| < ε`. -/
def HatarErtek (a : Sorozat) (A : ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n > N, |a n - A| < ε

/-- **4.6.1. Definíció.** Az `{aₙ}` sorozat *konvergens*, ha van határértéke. -/
def Konvergens (a : Sorozat) : Prop := ∃ A, HatarErtek a A

/-- **4.6.8. Definíció.** Az olyan sorozatot, amelynek nincs határértéke, *divergensnek*
nevezzük. -/
def Divergens (a : Sorozat) : Prop := ¬ Konvergens a

/-- **4.6.4. Definíció.** Az `{aₙ}` sorozat konvergens az `A` számhoz, ha `A` bármely
pozitív sugarú szimmetrikus környezetébe valamely tagtól kezdve a sorozat minden tagja
beleesik. -/
def HatarErtekKornyezettel (a : Sorozat) (A : ℝ) : Prop :=
  ∀ r > 0, ∃ N : ℕ, ∀ n > N, a n ∈ Ch03.nyitottIntervallum (A - r) (A + r)

/-- **4.6.7. Tétel.** A sorozat konvergenciájának 4.6.1. és 4.6.4. definíciója ekvivalens.

*Bizonyítás.* `4.6.2. ⇒ 4.6.4.`: ha a környezet sugara `ρ > 0`, akkor válasszuk
`ε = ρ`-t; ekkor `n > ν(ρ)` esetén `|aₙ - A| < ρ`, azaz `aₙ` beleesik a környezetbe.
`4.6.4. ⇒ 4.6.2.`: az adott `ε`-t válasszuk a környezet sugarának; ekkor `n > ν`-re
`A - ε < aₙ < A + ε`, ami éppen `|aₙ - A| < ε`. -/
theorem hatarErtek_iff_kornyezet (a : Sorozat) (A : ℝ) :
    HatarErtek a A ↔ HatarErtekKornyezettel a A := by
  constructor
  · intro h r hr
    obtain ⟨N, hN⟩ := h r hr
    refine ⟨N, fun n hn => ?_⟩
    have := abs_lt.mp (hN n hn)
    exact ⟨by linarith [this.1], by linarith [this.2]⟩
  · intro h ε hε
    obtain ⟨N, hN⟩ := h ε hε
    refine ⟨N, fun n hn => ?_⟩
    obtain ⟨h₁, h₂⟩ := hN n hn
    exact abs_lt.mpr ⟨by linarith, by linarith⟩

/-- A `HatarErtek` fogalom megegyezik a Mathlib `Filter.Tendsto ... atTop (nhds A)`
fogalmával; ez teszi lehetővé, hogy a későbbi fejezetekben a Mathlib eszköztárát is
használjuk. -/
theorem hatarErtek_iff_tendsto (a : Sorozat) (A : ℝ) :
    HatarErtek a A ↔ Filter.Tendsto a Filter.atTop (nhds A) := by
  rw [Metric.tendsto_atTop]
  constructor
  · intro h ε hε
    obtain ⟨N, hN⟩ := h ε hε
    exact ⟨N + 1, fun n hn => by simpa [Real.dist_eq] using hN n (by omega)⟩
  · intro h ε hε
    obtain ⟨N, hN⟩ := h ε hε
    exact ⟨N, fun n hn => by simpa [Real.dist_eq] using hN n (le_of_lt hn)⟩

/-- **4.6.11. Tétel (unicitástétel).** Konvergens sorozatnak csak egy határértéke lehet.

*Bizonyítás.* Indirekt: legyen `aₙ → A` és `aₙ → A'`, `A ≠ A'`, és `ρ = |A - A'| > 0`.
Az `ε = ρ/2` választással `n` elég nagy indexére a háromszög-egyenlőtlenség szerint
`ρ = |A - A'| ≤ |A - aₙ| + |aₙ - A'| < ρ/2 + ρ/2 = ρ`, ami ellentmondás. -/
theorem hatarErtek_unicitas {a : Sorozat} {A A' : ℝ} (h : HatarErtek a A)
    (h' : HatarErtek a A') : A = A' := by
  by_contra hne
  set ρ := |A - A'| with hρdef
  have hρ : 0 < ρ := abs_pos.mpr (sub_ne_zero.mpr hne)
  obtain ⟨N₁, hN₁⟩ := h (ρ / 2) (by linarith)
  obtain ⟨N₂, hN₂⟩ := h' (ρ / 2) (by linarith)
  set n := max N₁ N₂ + 1 with hn
  have h₁ : |a n - A| < ρ / 2 := hN₁ n (by omega)
  have h₂ : |a n - A'| < ρ / 2 := hN₂ n (by omega)
  have : ρ ≤ |A - a n| + |a n - A'| := by
    calc ρ = |A - A'| := rfl
    _ = |(A - a n) + (a n - A')| := by ring_nf
    _ ≤ |A - a n| + |a n - A'| := Ch03.haromszog_egyenlotlenseg _ _
  rw [abs_sub_comm A (a n)] at this
  linarith

/-! ## 4.7. Nevezetes sorozatok határértékei -/

/-- **4.7.1. Tétel.** Az állandó tagú sorozat mindig konvergens, és limesze önmaga. -/
theorem allando_hatarerteke (c : ℝ) : HatarErtek (fun _ => c) c := by
  intro ε hε
  exact ⟨0, fun n _ => by simpa using hε⟩

/-- **4.7.2. Tétel.** `1/n → 0`.

*Bizonyítás.* `|1/n - 0| = 1/n < ε`, ha `n > 1/ε`; tehát `ν(ε) = 1/ε` megfelelő
küszöbszám (elég egy nála nagyobb egész számot venni). -/
theorem egy_per_n_hatarerteke : HatarErtek (fun n : ℕ => 1 / (n : ℝ)) 0 := by
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / ε)
  refine ⟨N, fun n hn => ?_⟩
  have hn0 : (0 : ℝ) < n := by
    have : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have : (N : ℝ) < n := by exact_mod_cast hn
    have h1 : 0 < 1 / ε := by positivity
    linarith
  have : 1 / ε < (n : ℝ) := lt_of_lt_of_le hN (by exact_mod_cast le_of_lt hn)
  rw [sub_zero, abs_of_pos (by positivity)]
  rwa [div_lt_iff₀ hn0, ← div_lt_iff₀' hε] at *

/-- **4.7.4. Tétel (Bernoulli-féle egyenlőtlenség).** `(1 + α)ⁿ ≥ 1 + nα`, ha `α ≥ -1`.

*Bizonyítás.* Teljes indukcióval: `n = 1`-re igaz; ha `n`-re igaz, akkor
`(1+α)ⁿ⁺¹ = (1+α)ⁿ(1+α) ≥ (1+nα)(1+α) = 1 + nα + α + nα² ≥ 1 + (n+1)α`,
ahol kihasználtuk, hogy `1 + α ≥ 0`. -/
theorem bernoulli {α : ℝ} (hα : -1 ≤ α) (n : ℕ) : 1 + n * α ≤ (1 + α) ^ n := by
  induction n with
  | zero => simp
  | succ k ih =>
      have h1 : (0 : ℝ) ≤ 1 + α := by linarith
      have hk : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
      have step₁ : 1 + ((k : ℝ) + 1) * α ≤ (1 + (k : ℝ) * α) * (1 + α) := by
        nlinarith [sq_nonneg α]
      have step₂ : (1 + (k : ℝ) * α) * (1 + α) ≤ (1 + α) ^ k * (1 + α) := by nlinarith
      push_cast
      rw [pow_succ]
      linarith

/-- **4.7.4. Tétel (2).** `βⁿ ≥ 1 + n(β - 1)`, ha `β ≥ 0`.  (A (1)-ből `β = 1 + α`
helyettesítéssel adódik.) -/
theorem bernoulli' {β : ℝ} (hβ : 0 ≤ β) (n : ℕ) : 1 + n * (β - 1) ≤ β ^ n := by
  have := bernoulli (α := β - 1) (by linarith) n
  simpa using this

/-- **4.7.3. Tétel (a) rész.** Ha `|q| < 1`, akkor `qⁿ → 0`.

*Bizonyítás.* `|qⁿ - 0| = |q|ⁿ < ε` ekvivalens `(1/|q|)ⁿ > 1/ε`-nal.  A Bernoulli-féle
egyenlőtlenség szerint `(1/|q|)ⁿ ≥ 1 + n(1/|q| - 1)`, így elég, ha
`1 + n(1/|q| - 1) > 1/ε`, azaz ha `n > (1/ε - 1)/(1/|q| - 1) = ν(ε)`. -/
theorem q_hatvany_nullahoz {q : ℝ} (hq : |q| < 1) : HatarErtek (fun n => q ^ n) 0 := by
  intro ε hε
  rcases eq_or_ne q 0 with rfl | hq0
  · refine ⟨0, fun n hn => ?_⟩
    have h0 : (0 : ℝ) ^ n = 0 := zero_pow (by omega)
    simpa [h0] using hε
  have habs : 0 < |q| := abs_pos.mpr hq0
  set α : ℝ := 1 / |q| - 1 with hα
  have hαpos : 0 < α := by
    rw [hα, sub_pos, lt_div_iff₀ habs]
    linarith
  obtain ⟨N, hN⟩ := exists_nat_gt ((1 / ε - 1) / α)
  refine ⟨N, fun n hn => ?_⟩
  have hnN : ((N : ℝ)) < n := by exact_mod_cast hn
  have hn' : (1 / ε - 1) / α < (n : ℝ) := lt_trans hN hnN
  have key : 1 / ε < 1 + n * α := by
    have := (div_lt_iff₀ hαpos).mp hn'
    linarith
  have hb : 1 + (n : ℝ) * α ≤ (1 / |q|) ^ n := by
    have := bernoulli (α := α) (by linarith) n
    simpa [hα] using this
  have hqn : (0 : ℝ) < |q| ^ n := pow_pos habs n
  have hlt : 1 / ε < (1 / |q|) ^ n := lt_of_lt_of_le key hb
  have hrw : (1 / |q|) ^ n = (|q| ^ n)⁻¹ := by rw [one_div, inv_pow]
  rw [hrw, one_div] at hlt
  rw [sub_zero, abs_pow]
  exact (inv_lt_inv₀ hε hqn).mp hlt

/-- **4.7.3. Tétel (β) rész.** Ha `q = 1`, akkor `qⁿ → 1`. -/
theorem egy_hatvany : HatarErtek (fun n : ℕ => (1 : ℝ) ^ n) 1 := by
  intro ε hε
  exact ⟨0, fun n _ => by simpa using hε⟩

/-- **4.8.1. Tétel.** Konvergens sorozat korlátos.

*Bizonyítás.* Ha `aₙ → A`, akkor `ε = 1`-hez is van olyan `ν₁`, hogy `n > ν₁` esetén
`A - 1 < aₙ < A + 1`.  Ekkor `K = max(A+1, a₀, …, a_{ν₁})` és
`k = min(A-1, a₀, …, a_{ν₁})` a sorozat felső, illetve alsó korlátja. -/
theorem konvergens_korlatos {a : Sorozat} (h : Konvergens a) : Korlatos a := by
  obtain ⟨A, hA⟩ := h
  obtain ⟨N, hN⟩ := hA 1 one_pos
  set K : ℝ := max (A + 1) ((Finset.range (N + 1)).sup' (by simp) a) with hK
  set k : ℝ := min (A - 1) ((Finset.range (N + 1)).inf' (by simp) a) with hk
  refine ⟨⟨k, fun n => ?_⟩, ⟨K, fun n => ?_⟩⟩
  · rcases Nat.lt_or_ge N n with hlt | hge
    · have := abs_lt.mp (hN n hlt)
      have : A - 1 < a n := by linarith [this.1]
      exact le_trans (min_le_left _ _) (le_of_lt this)
    · refine le_trans (min_le_right _ _) ?_
      exact Finset.inf'_le _ (by simp [hge])
  · rcases Nat.lt_or_ge N n with hlt | hge
    · have := abs_lt.mp (hN n hlt)
      have : a n < A + 1 := by linarith [this.2]
      exact le_trans (le_of_lt this) (le_max_left _ _)
    · refine le_trans ?_ (le_max_right _ _)
      exact Finset.le_sup' _ (by simp [hge])

/-- **4.8.2. Megjegyzés.** Az állítás nem fordítható meg: a `{(-1)ⁿ}` sorozat korlátos,
de nem konvergens. -/
theorem valto_elojel_divergens : Divergens (fun n : ℕ => (-1 : ℝ) ^ n) := by
  rintro ⟨A, hA⟩
  obtain ⟨N, hN⟩ := hA 1 one_pos
  have h1 : |(-1 : ℝ) ^ (2 * N + 2) - A| < 1 := hN _ (by omega)
  have h2 : |(-1 : ℝ) ^ (2 * N + 3) - A| < 1 := hN _ (by omega)
  have e1 : (-1 : ℝ) ^ (2 * N + 2) = 1 := by
    rw [show 2 * N + 2 = 2 * (N + 1) by ring, pow_mul]; norm_num
  have e2 : (-1 : ℝ) ^ (2 * N + 3) = -1 := by
    rw [show 2 * N + 3 = 2 * (N + 1) + 1 by ring, pow_succ, pow_mul]; norm_num
  rw [e1] at h1
  rw [e2] at h2
  linarith [(abs_lt.mp h1).1, (abs_lt.mp h1).2, (abs_lt.mp h2).1, (abs_lt.mp h2).2]

/-- **4.8.3. Tétel.** Konvergens sorozat minden részsorozata konvergens, és határértéke
megegyezik a sorozat határértékével.

*Bizonyítás.* Ha `A` bármely `ε` sugarú környezetébe véges sok tag kivételével a sorozat
minden tagja beleesik, akkor a részsorozatból sem maradhat ki több tag, mint az
eredetiből.  Formálisan: `nₖ ≥ k`, így `k > ν` esetén `nₖ > ν`. -/
theorem reszsorozat_hatarerteke {a b : Sorozat} {A : ℝ} (hb : Reszsorozat b a)
    (hA : HatarErtek a A) : HatarErtek b A := by
  obtain ⟨φ, hφ, rfl⟩ := hb
  intro ε hε
  obtain ⟨N, hN⟩ := hA ε hε
  exact ⟨N, fun k hk => hN (φ k) (lt_of_lt_of_le hk (strictMono_id_le hφ k))⟩

/-- **4.8.4. Következmény.** Véges sok tag elhagyása a konvergencián (és a határértéken)
nem változtat: az `{a_{n+m}}` eltolt sorozat ugyanahhoz tart. -/
theorem eltolt_hatarerteke {a : Sorozat} {A : ℝ} (m : ℕ) (hA : HatarErtek a A) :
    HatarErtek (fun n => a (n + m)) A := by
  intro ε hε
  obtain ⟨N, hN⟩ := hA ε hε
  exact ⟨N, fun n hn => hN (n + m) (by omega)⟩

/-- **4.8.5. Tétel.** Konvergens sorozat tagjai sorrendjének bármely megváltoztatása
után is konvergens marad, és határértéke sem változik.

*Bizonyítás (a könyv szerint).* Legyen `ε > 0` adott, és `μ` olyan küszöbszám, hogy
`k > μ` esetén `|a_k - A| < ε`.  Nézzük meg, hogy az átrendezett sorozatban hova esnek
az `a₀, …, a_μ` tagok: legyenek ezek az `n₀, …, n_μ` helyeken, és legyen
`ν = max(n₀, …, n_μ)`.  Ha `n > ν`, akkor `a_{pₙ}` tagok közt nem szerepelhet
`a₀, …, a_μ`, tehát `pₙ > μ`, s így `|a_{pₙ} - A| < ε`. -/
theorem atrendezes_hatarerteke {a : Sorozat} {A : ℝ} (p : ℕ ≃ ℕ) (hA : HatarErtek a A) :
    HatarErtek (fun n => a (p n)) A := by
  intro ε hε
  obtain ⟨μ, hμ⟩ := hA ε hε
  refine ⟨(Finset.range (μ + 1)).sup fun j => p.symm j, fun n hn => ?_⟩
  refine hμ (p n) ?_
  by_contra hcon
  push_neg at hcon
  have hmem : p n ∈ Finset.range (μ + 1) := by simp [hcon]
  have : n ≤ (Finset.range (μ + 1)).sup fun j => p.symm j := by
    have := Finset.le_sup (f := fun j => p.symm j) hmem
    simpa using this
  omega

/-- **4.8.9. Tétel (fésűs egyesítés).** Ha az `{fₙ}` sorozat két olyan részsorozatra
bontható (azaz az `m` és `μ` szigorúan monoton indexsorozatok együtt minden indexet
lefednek), amelyek ugyanahhoz az `A` számhoz konvergálnak, akkor `{fₙ}` is konvergens,
és határértéke `A`.

*Bizonyítás.* Legyen `ν = max(m_{ν₁}, μ_{ν₂})`.  Ha `n > ν`, akkor `n` csak olyan
`m_k`-val, illetve `μ_l`-lel lehet egyenlő, amelyre `k > ν₁`, illetve `l > ν₂`, így
mindkét esetben `|fₙ - A| < ε`. -/
theorem fesus_egyesites {f : Sorozat} {A : ℝ} {m μ : ℕ → ℕ}
    (hm : StrictMono m) (hμ : StrictMono μ)
    (hcover : ∀ n : ℕ, (∃ k, m k = n) ∨ ∃ l, μ l = n)
    (h₁ : HatarErtek (fun k => f (m k)) A) (h₂ : HatarErtek (fun l => f (μ l)) A) :
    HatarErtek f A := by
  intro ε hε
  obtain ⟨ν₁, hν₁⟩ := h₁ ε hε
  obtain ⟨ν₂, hν₂⟩ := h₂ ε hε
  refine ⟨max (m ν₁) (μ ν₂), fun n hn => ?_⟩
  rcases hcover n with ⟨k, rfl⟩ | ⟨l, rfl⟩
  · exact hν₁ k (hm.lt_iff_lt.mp (lt_of_le_of_lt (le_max_left _ _) hn))
  · exact hν₂ l (hμ.lt_iff_lt.mp (lt_of_le_of_lt (le_max_right _ _) hn))

end Ch04
end Leindler
