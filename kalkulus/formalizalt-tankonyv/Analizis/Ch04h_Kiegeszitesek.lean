import Mathlib
import Analizis.Ch04a_SorozatokAlapok
import Analizis.Ch04b_SorozatokMuveletek

/-!
# Leindler László: Analízis — kiegészítések a 4. fejezethez

Ez a fájl a 4. fejezet azon pontjait formalizálja, amelyek a korábbi modulokból
kimaradtak:

* **4.6.3., 4.6.5., 4.6.6.** a konvergencia további — a 4.6.1–4.6.2. definícióval
  egyenértékű — megfogalmazásai („majdnem minden tagra”, „szimmetrikus környezet és
  küszöbszám”, „a környezetbe majdnem minden tag beleesik”),
* **4.8.6.** az átrendezett sorozat fogalma (és a 4.8.5. Tétel ezzel a fogalommal),
* **4.8.8–4.8.9.** a fésűs egyesítés fogalma és a rá vonatkozó tétel,
* **4.8.10–4.8.11.** következmények két, illetve véges sok részsorozatra bontásról,
* **4.9.3. Tétel.** két polinomiális kifejezés hányadosának határértéke.

A „majdnem minden `n`-re” a könyv szerint azt jelenti, hogy véges sok `n` kivételével
mindig teljesül az állítás; ezt a `Set.Finite` predikátummal fejezzük ki.
-/

namespace Leindler.Ch04

open Filter Set Topology

/-! ## 4.6.3., 4.6.5., 4.6.6. A konvergencia további definíciói -/

/-- **4.6.3. Definíció.** Az `{aₙ}` sorozat konvergens az `A` számhoz, ha bármely `ε > 0`
esetén az `|aₙ - A| < ε` egyenlőtlenség *majdnem minden* `n`-re teljesül, azaz véges sok
`n` kivételével mindig. -/
def HatarErtekMajdnemMinden (a : Sorozat) (A : ℝ) : Prop :=
  ∀ ε > 0, {n : ℕ | ¬ |a n - A| < ε}.Finite

/-- **4.6.5. Definíció.** Az `{aₙ}` sorozat konvergens az `A` számhoz, ha `A` bármely
szimmetrikus környezetéhez megadható olyan `ν` küszöbszám, hogy `n > ν` esetén `aₙ`
beleesik ebbe a környezetbe. -/
def HatarErtekKornyezetKuszobbel (a : Sorozat) (A : ℝ) : Prop :=
  ∀ r > 0, ∃ N : ℕ, ∀ n > N, a n ∈ Metric.ball A r

/-- **4.6.6. Definíció.** Az `{aₙ}` sorozat konvergens az `A` számhoz, ha `A` bármely
környezetébe a sorozatnak majdnem minden tagja beleesik. -/
def HatarErtekKornyezetMajdnemMinden (a : Sorozat) (A : ℝ) : Prop :=
  ∀ r > 0, {n : ℕ | a n ∉ Metric.ball A r}.Finite

/-- **4.6.7. Tétel** (a 4.6.2. ⇔ 4.6.3. irány). A „majdnem minden tagra teljesül”
megfogalmazás egyenértékű a küszöbszámos definícióval.

*Bizonyítás.* Ha `n > ν` esetén `|aₙ - A| < ε`, akkor a kivételes indexek halmaza része
a `{0, 1, …, ν}` véges halmaznak. Fordítva: ha a kivételes indexek halmaza véges, akkor
van legnagyobb eleme (vagy üres), és e fölött már minden index jó. -/
theorem hatarErtek_iff_majdnemMinden (a : Sorozat) (A : ℝ) :
    HatarErtek a A ↔ HatarErtekMajdnemMinden a A := by
  constructor
  · intro h ε hε
    obtain ⟨N, hN⟩ := h ε hε
    refine Set.Finite.subset (Set.finite_Icc 0 N) ?_
    intro n hn
    simp only [Set.mem_setOf_eq] at hn
    by_contra hcon
    simp only [Set.mem_Icc, not_and, not_le] at hcon
    exact hn (hN n (hcon (Nat.zero_le n)))
  · intro h ε hε
    obtain ⟨N, hN⟩ := (h ε hε).bddAbove
    refine ⟨N, fun n hn => ?_⟩
    by_contra hcon
    exact absurd (hN (show n ∈ {m : ℕ | ¬ |a m - A| < ε} from hcon)) (by omega)

/-- **4.6.7. Tétel** (a 4.6.2. ⇔ 4.6.5. irány). A szimmetrikus környezetekkel és
küszöbszámmal megfogalmazott definíció egyenértékű a `|aₙ - A| < ε` alakúval. -/
theorem hatarErtek_iff_kornyezetKuszobbel (a : Sorozat) (A : ℝ) :
    HatarErtek a A ↔ HatarErtekKornyezetKuszobbel a A := by
  constructor
  · intro h r hr
    obtain ⟨N, hN⟩ := h r hr
    exact ⟨N, fun n hn => by simpa [Real.dist_eq] using hN n hn⟩
  · intro h ε hε
    obtain ⟨N, hN⟩ := h ε hε
    exact ⟨N, fun n hn => by simpa [Real.dist_eq] using hN n hn⟩

/-- **4.6.7. Tétel** (a 4.6.2. ⇔ 4.6.6. irány). Az „`A` bármely környezetébe majdnem
minden tag beleesik” megfogalmazás is egyenértékű a többivel. -/
theorem hatarErtek_iff_kornyezetMajdnemMinden (a : Sorozat) (A : ℝ) :
    HatarErtek a A ↔ HatarErtekKornyezetMajdnemMinden a A := by
  rw [hatarErtek_iff_majdnemMinden]
  constructor
  · intro h r hr
    refine Set.Finite.subset (h r hr) ?_
    intro n hn
    simpa [Real.dist_eq] using hn
  · intro h ε hε
    refine Set.Finite.subset (h ε hε) ?_
    intro n hn
    simpa [Real.dist_eq] using hn

/-! ## 4.8.6. Az átrendezett sorozat -/

/-- **4.8.6. Definíció.** Az `{aₙ}` sorozat *átrendezésén* olyan `{a_{pₙ}}` sorozatot
értünk, amely „végtelen permutációval” jön létre az eredeti sorozatból: az eredeti
sorozat minden tagja fellép, és csak egyszer lép fel az átrendezett sorozatban. -/
def Atrendezes (b a : Sorozat) : Prop :=
  ∃ p : ℕ ≃ ℕ, b = fun n => a (p n)

/-- **4.8.5. Tétel** (a 4.8.6. Definíció fogalmával). Konvergens sorozat bármely
átrendezése konvergens, és határértéke ugyanaz. -/
theorem atrendezes_konvergens {a b : Sorozat} {A : ℝ} (hb : Atrendezes b a)
    (hA : HatarErtek a A) : HatarErtek b A := by
  obtain ⟨p, rfl⟩ := hb
  exact atrendezes_hatarerteke p hA

/-- Az átrendezés reflexív: minden sorozat önmagának is átrendezése. -/
theorem atrendezes_refl (a : Sorozat) : Atrendezes a a :=
  ⟨Equiv.refl ℕ, rfl⟩

/-! ## 4.8.8–4.8.11. Fésűs egyesítés -/

/-- **4.8.8. Definíció.** Két sorozat, `{aₖ}` és `{bₗ}` *fésűs egyesítésén* olyan `{fₙ}`
sorozatot értünk, amely felbontható két részsorozatra úgy, hogy az egyik részsorozat
tagjai — az eredeti sorrendben — az `{aₖ}`, a másiké a `{bₗ}` sorozat tagjai. -/
def FesusEgyesitese (f a b : Sorozat) : Prop :=
  ∃ m mu : ℕ → ℕ, StrictMono m ∧ StrictMono mu ∧
    (∀ n : ℕ, (∃ k, m k = n) ∨ ∃ l, mu l = n) ∧
    (∀ k, f (m k) = a k) ∧ (∀ l, f (mu l) = b l)

/-- **4.8.9. Tétel.** Két konvergens, közös határértékkel rendelkező sorozatból bármely
fésűs egyesítéssel kapott sorozat konvergens, és határértéke az eredeti közös
határérték. -/
theorem fesusEgyesitese_hatarerteke {f a b : Sorozat} {A : ℝ}
    (hf : FesusEgyesitese f a b) (ha : HatarErtek a A) (hb : HatarErtek b A) :
    HatarErtek f A := by
  obtain ⟨m, mu, hm, hmu, hcover, hfa, hfb⟩ := hf
  refine fesus_egyesites hm hmu hcover ?_ ?_
  · intro ε hε
    obtain ⟨N, hN⟩ := ha ε hε
    exact ⟨N, fun k hk => by simpa [hfa k] using hN k hk⟩
  · intro ε hε
    obtain ⟨N, hN⟩ := hb ε hε
    exact ⟨N, fun l hl => by simpa [hfb l] using hN l hl⟩

/-- **4.8.10. Következmény.** Ha egy sorozat felbontható két konvergens, közös
határértékkel rendelkező részsorozatra, akkor az eredeti sorozat is konvergens, és
határértéke a részsorozatok közös határértéke. -/
theorem ket_reszsorozatra_bonthato {f : Sorozat} {A : ℝ} {m mu : ℕ → ℕ}
    (hm : StrictMono m) (hmu : StrictMono mu)
    (hcover : ∀ n : ℕ, (∃ k, m k = n) ∨ ∃ l, mu l = n)
    (h₁ : HatarErtek (fun k => f (m k)) A) (h₂ : HatarErtek (fun l => f (mu l)) A) :
    HatarErtek f A :=
  fesus_egyesites hm hmu hcover h₁ h₂

/-- **4.8.11. Következmény.** Ha egy sorozat felbontható véges sok konvergens, közös
határértékkel rendelkező részsorozatra, akkor az eredeti sorozat is konvergens, és
határértéke a részsorozatok közös határértéke.

*Bizonyítás (a könyv gondolatmenete).* A 4.8.9. Tételt előbb az első két részsorozatra,
majd ezek fésűs egyesítésére és a harmadikra alkalmazzuk, és így tovább. Itt közvetlenül
járunk el: az `ε`-hoz tartozó `νᵢ` küszöbök közül az `mᵢ(νᵢ)` értékek maximuma megfelelő
küszöb, hiszen `n > max` esetén az `n = mᵢ(k)` előállításban szükségképpen `k > νᵢ`. -/
theorem veges_sok_reszsorozatra_bonthato {f : Sorozat} {A : ℝ} {N : ℕ}
    {m : Fin N → ℕ → ℕ} (hm : ∀ i, StrictMono (m i))
    (hcover : ∀ n : ℕ, ∃ i k, m i k = n)
    (hlim : ∀ i, HatarErtek (fun k => f (m i k)) A) :
    HatarErtek f A := by
  intro ε hε
  choose nu hnu using fun i => hlim i ε hε
  refine ⟨Finset.univ.sup fun i => m i (nu i), fun n hn => ?_⟩
  obtain ⟨i, k, rfl⟩ := hcover n
  refine hnu i k ?_
  have hle : m i (nu i) ≤ Finset.univ.sup fun j => m j (nu j) :=
    Finset.le_sup (f := fun j => m j (nu j)) (Finset.mem_univ i)
  have : m i (nu i) < m i k := lt_of_le_of_lt hle hn
  exact (hm i).lt_iff_lt.mp this

/-! ## 4.9.3. Tétel: polinomok hányadosának határértéke -/

/-- Segédlemma: `(∑_{i≤k} cᵢ nⁱ)/nᵏ → c_k`, ha `n → ∞`.

*Bizonyítás.* A számlálót tagonként elosztva `nᵏ`-val a `cᵢ·n^{i-k}` alakú tagokat
kapjuk; ezek `i < k` esetén nullához tartanak, az `i = k` tag pedig maga `c_k`. -/
theorem tendsto_polinom_per_hatvany (c : ℕ → ℝ) (k : ℕ) :
    Tendsto (fun n : ℕ => (∑ i ∈ Finset.range (k + 1), c i * (n : ℝ) ^ i) / (n : ℝ) ^ k)
      atTop (𝓝 (c k)) := by
  have hsum : (c k) = ∑ i ∈ Finset.range (k + 1), (if i = k then c i else 0) := by
    rw [Finset.sum_ite_eq' (Finset.range (k + 1)) k (fun i => c i)]
    simp
  rw [hsum]
  have heq : (fun n : ℕ => (∑ i ∈ Finset.range (k + 1), c i * (n : ℝ) ^ i) / (n : ℝ) ^ k)
      =ᶠ[atTop] fun n : ℕ => ∑ i ∈ Finset.range (k + 1), c i * ((n : ℝ) ^ i / (n : ℝ) ^ k) := by
    filter_upwards [eventually_gt_atTop 0] with n _
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by ring
  refine Tendsto.congr' heq.symm ?_
  refine tendsto_finset_sum _ fun i hi => ?_
  rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi)) with hik | hik
  · -- `i = k`: a tag konstans `c k`
    subst hik
    have hif : (if i = i then c i else 0) = c i := if_pos rfl
    rw [hif]
    refine Tendsto.congr' ?_
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => c i) atTop (𝓝 (c i)))
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hne : ((n : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    rw [div_self (pow_ne_zero _ hne), mul_one]
  · -- `i < k`: a tag nullához tart
    rw [if_neg (by omega)]
    have hlim : Tendsto (fun n : ℕ => ((n : ℝ) ^ (k - i))⁻¹) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n : ℕ => ((n : ℝ) ^ (k - i))) atTop atTop :=
        (tendsto_pow_atTop (n := k - i) (by omega)).comp tendsto_natCast_atTop_atTop
      exact h1.inv_tendsto_atTop
    have h2 : Tendsto (fun n : ℕ => c i * ((n : ℝ) ^ (k - i))⁻¹) atTop (𝓝 0) := by
      simpa using hlim.const_mul (c i)
    refine Tendsto.congr' ?_ h2
    filter_upwards [eventually_gt_atTop 0] with n hn
    have hne : ((n : ℝ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have hsplit : (n : ℝ) ^ k = (n : ℝ) ^ i * (n : ℝ) ^ (k - i) := by
      rw [← pow_add]
      congr 1
      omega
    rw [hsplit]
    field_simp

/-- **4.9.3. Tétel.** Ha `a₀, …, a_k` és `b₀, …, b_k` valós számok és `b_k ≠ 0`, akkor
`n → ∞` esetén

`(a_k nᵏ + ⋯ + a₀)/(b_k nᵏ + ⋯ + b₀) → a_k/b_k`.

*Bizonyítás.* A számlálót is, a nevezőt is `nᵏ`-val osztva az első tagok kivételével
minden tag nullához tart, így a műveleti szabályok (4.9.1. Tétel) ismételt
alkalmazásával adódik az állítás. -/
theorem racionalis_kifejezes_hatarerteke (a b : ℕ → ℝ) (k : ℕ) (hbk : b k ≠ 0) :
    HatarErtek
      (fun n : ℕ => (∑ i ∈ Finset.range (k + 1), a i * (n : ℝ) ^ i) /
        (∑ i ∈ Finset.range (k + 1), b i * (n : ℝ) ^ i)) (a k / b k) := by
  rw [hatarErtek_iff_tendsto]
  have hnum := tendsto_polinom_per_hatvany a k
  have hden := tendsto_polinom_per_hatvany b k
  have hquot := hnum.div hden hbk
  refine Tendsto.congr' ?_ hquot
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hne : ((n : ℝ) ^ k) ≠ 0 := pow_ne_zero _ (Nat.cast_ne_zero.mpr (by omega))
  simp only [Pi.div_apply]
  rcases eq_or_ne (∑ i ∈ Finset.range (k + 1), b i * (n : ℝ) ^ i) 0 with hz | hz
  · simp [hz]
  · field_simp

end Leindler.Ch04
