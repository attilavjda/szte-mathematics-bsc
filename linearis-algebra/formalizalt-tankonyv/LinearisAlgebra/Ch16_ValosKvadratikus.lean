import LinearisAlgebra.Ch15_BilinearisKvadratikus

/-!
# Szabó László: Bevezetés a lineáris algebrába — 16. fejezet

**Valós kvadratikus alakok** (a jegyzet 78–80. oldala).

* **16.1. Definíció** — normálalakú (valós) kvadratikus alak,
* **16.2. Tétel** — bármely valós kvadratikus alak nemelfajuló lineáris helyettesítéssel
  (azaz alkalmas bázisra áttérve) normálalakra hozható,
* **16.3. Tehetetlenségi tétel** — a pozitív, illetve a negatív tagok száma a
  normálalakban egyértelműen meghatározott,
* **16.4. Definíció** — pozitív/negatív definit, szemidefinit, indefinit kvadratikus alak,
* **16.5. Tétel** — a definitség jellemzése a normálalak `k` és `r` paraméterével,
* **16.6. Következmény** — pozitív definit szimmetrikus valós `A` mátrixhoz van olyan
  nemelfajuló `P`, melyre `A = PPᵀ`.

**Megjegyzés a megfogalmazásról.** A könyv a normálalakot
`x₁² + … + x_k² − x_{k+1}² − … − x_r²` alakban írja fel, azaz a bázisvektorokat úgy
sorszámozza, hogy előbb a `+1`, majd a `−1`, végül a `0` együtthatók álljanak. Ez
pusztán a bázisvektorok sorrendjének kérdése (egy bázispermutáció), ezért itt a
sorrendtől független megfogalmazást használjuk: a mátrix diagonális, főátlójának elemei
`1`, `−1` vagy `0`; a `k` és az `r − k` szerepét a `pozitivTagok`, illetve a
`negativTagok` függvény veszi át.
-/

namespace SzaboLinAlg
namespace Ch16

open scoped BigOperators
open SzaboLinAlg.Ch02 SzaboLinAlg.Ch03 SzaboLinAlg.Ch04 SzaboLinAlg.Ch06 SzaboLinAlg.Ch07
  SzaboLinAlg.Ch08 SzaboLinAlg.Ch09 SzaboLinAlg.Ch10 SzaboLinAlg.Ch12 SzaboLinAlg.Ch13
  SzaboLinAlg.Ch15
open Matrix

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}

/-! ## 16.1. Definíció -/

/-- **16.1. Definíció.** A valós `q` kvadratikus alak (illetve a hozzá tartozó `l`
szimmetrikus bilineáris leképezés) *normálalakú* az `ℰ` bázisban, ha mátrixa diagonális,
és a főátlóban csak `1`, `−1` és `0` áll. -/
def Normalalaku (l : V → V → ℝ) (e : Fin n → V) : Prop :=
  (∀ i j, i ≠ j → l (e i) (e j) = 0) ∧
    ∀ i, l (e i) (e i) = 1 ∨ l (e i) (e i) = -1 ∨ l (e i) (e i) = 0

/-- A normálalak *pozitív tagjainak* száma (a könyv jelölésében `k`). -/
noncomputable def pozitivTagok (l : V → V → ℝ) (e : Fin n → V) : ℕ :=
  Nat.card {i : Fin n // l (e i) (e i) = 1}

/-- A normálalak *negatív tagjainak* száma (a könyv jelölésében `r − k`). -/
noncomputable def negativTagok (l : V → V → ℝ) (e : Fin n → V) : ℕ :=
  Nat.card {i : Fin n // l (e i) (e i) = -1}

/-- A normálalak *rangja* (a könyv jelölésében `r`): a nemnulla tagok száma. -/
noncomputable def normalRang (l : V → V → ℝ) (e : Fin n → V) : ℕ :=
  pozitivTagok l e + negativTagok l e

/-! ### A normálalak értéke -/

/-- Normálalakban `q(∑ xᵢeᵢ) = ∑ᵢ l(eᵢ,eᵢ)xᵢ²`, azaz a pozitív indexeken `+xᵢ²`,
a negatívakon `−xᵢ²`, a többin `0` áll. -/
theorem normalalak_ertek {l : V → V → ℝ} (hl : BilinearisLekepezes ℝ l) {e : Fin n → V}
    (hne : Normalalaku l e) (x : Fin n → ℝ) :
    l (∑ i, x i • e i) (∑ i, x i • e i) = ∑ i, l (e i) (e i) * x i ^ 2 :=
  bilin_diagonalis_ertek hl e hne.1 x

/-! ## 16.2. Tétel -/

/-- **16.2. Tétel.** Bármely valós kvadratikus alak nemelfajuló lineáris helyettesítéssel
normálalakra hozható.

*Bizonyítás.* A 15.7. alaptétel szerint van olyan bázis, melyben `q` kanonikus alakú,
azaz `q = a₁x₁² + … + aₙxₙ²`. Az `aᵢ ≠ 0` indexeken az `xᵢ = yᵢ/√|aᵢ|` (nemelfajuló)
helyettesítést elvégezve az együttható `aᵢ/|aᵢ| = ±1` lesz. -/
theorem letezik_normalalak {l : V → V → ℝ} (hl : SzimmetrikusBilinearis ℝ l)
    {e : Fin n → V} (he : Bazis ℝ e) : ∃ f : Fin n → V, Bazis ℝ f ∧ Normalalaku l f := by
  obtain ⟨g, hg, hkan⟩ := kvadratikus_alaptetel (T := ℝ) two_ne_zero hl he
  have key : ∀ t : ℝ, ∃ s : ℝ, s ≠ 0 ∧
      (s * s * t = 1 ∨ s * s * t = -1 ∨ s * s * t = 0) := by
    intro t
    rcases eq_or_ne t 0 with rfl | ht
    · exact ⟨1, one_ne_zero, Or.inr (Or.inr (by ring))⟩
    · have hs : Real.sqrt |t| ≠ 0 := by
        rw [Ne, Real.sqrt_eq_zero (abs_nonneg t)]
        exact abs_ne_zero.2 ht
      refine ⟨1 / Real.sqrt |t|, one_div_ne_zero hs, ?_⟩
      have hsq : Real.sqrt |t| * Real.sqrt |t| = |t| :=
        Real.mul_self_sqrt (abs_nonneg t)
      have hprod : (1 / Real.sqrt |t|) * (1 / Real.sqrt |t|) = 1 / |t| := by
        rw [div_mul_div_comm, hsq, one_mul]
      rw [hprod]
      rcases lt_or_gt_of_ne ht with hneg | hpos
      · right; left
        rw [abs_of_neg hneg]
        field_simp
      · left
        rw [abs_of_pos hpos]
        field_simp
  choose c hcne hcval using fun i : Fin n => key (l (g i) (g i))
  refine ⟨fun i => c i • g i, bazis_scale hg hcne, fun i j hij => ?_, fun i => ?_⟩
  · have hzero : l (g i) (g j) = 0 := hkan i j hij
    show l (c i • g i) (c j • g j) = 0
    rw [hl.1.2.2.1, hl.1.2.2.2, hzero, mul_zero, mul_zero]
  · have hEq : l (c i • g i) (c i • g i) = c i * c i * l (g i) (g i) := by
      rw [hl.1.2.2.1, hl.1.2.2.2]; ring
    show l (c i • g i) (c i • g i) = 1 ∨ l (c i • g i) (c i • g i) = -1 ∨
      l (c i • g i) (c i • g i) = 0
    rw [hEq]
    exact hcval i

/-! ## 16.3. Tehetetlenségi tétel -/

/-- Segédlemma a tehetetlenségi tételhez: ha `q` normálalakú mind az `ℰ`, mind az `ℱ`
bázisban, akkor `ℰ` pozitív tagjainak száma legfeljebb annyi, mint `ℱ`-é.

*Bizonyítás (a könyv gondolatmenete altér-alakban).* Legyen `P` az `ℰ` pozitív indexű
bázisvektorai által kifeszített altér, `N` pedig az `ℱ` nem pozitív indexű
bázisvektoraié. `P`-n `q` pozitív definit, `N`-en `q ≤ 0`, ezért `P ∩ N = {0}`. Így
`dim P + dim N ≤ n`, azaz `k + (n − k') ≤ n`. -/
theorem pozitivTagok_le {l : V → V → ℝ} (hl : SzimmetrikusBilinearis ℝ l)
    {e f : Fin n → V} (he : Bazis ℝ e) (hf : Bazis ℝ f)
    (hne : Normalalaku l e) (hnf : Normalalaku l f) :
    pozitivTagok l e ≤ pozitivTagok l f := by
  classical
  haveI : Module.Finite ℝ V := Module.Finite.of_basis (toModuleBasis he)
  have hdim : Module.finrank ℝ V = n := by
    rw [Module.finrank_eq_card_basis (toModuleBasis he), Fintype.card_fin]
  set u : {i : Fin n // l (e i) (e i) = 1} → V := fun i => e i with hu
  set w : {i : Fin n // ¬ l (f i) (f i) = 1} → V := fun i => f i with hw
  have hu_li : LinearIndependent ℝ u :=
    ((linFuggetlen_iff_linearIndependent e).1 he.1).comp _ Subtype.val_injective
  have hw_li : LinearIndependent ℝ w :=
    ((linFuggetlen_iff_linearIndependent f).1 hf.1).comp _ Subtype.val_injective
  have hPdim : Module.finrank ℝ (Submodule.span ℝ (Set.range u))
      = Fintype.card {i : Fin n // l (e i) (e i) = 1} := finrank_span_eq_card hu_li
  have hNdim : Module.finrank ℝ (Submodule.span ℝ (Set.range w))
      = Fintype.card {i : Fin n // ¬ l (f i) (f i) = 1} := finrank_span_eq_card hw_li
  have hdisj : Disjoint (Submodule.span ℝ (Set.range u)) (Submodule.span ℝ (Set.range w)) := by
    rw [Submodule.disjoint_def]
    intro v hv hv'
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hv
    obtain ⟨d, hd⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hv'
    have hq1 : l v v = ∑ i, c i ^ 2 := by
      rw [← hc, bilin_diagonalis_ertek hl.1 u
        (fun i j hij => hne.1 _ _ fun h => hij (Subtype.ext h)) c]
      exact Finset.sum_congr rfl fun i _ => by rw [hu]; rw [i.2, one_mul]
    have hq2 : l v v ≤ 0 := by
      rw [← hd, bilin_diagonalis_ertek hl.1 w
        (fun i j hij => hnf.1 _ _ fun h => hij (Subtype.ext h)) d]
      refine Finset.sum_nonpos fun i _ => ?_
      have hcase := hnf.2 i
      rcases hcase with h | h | h
      · exact absurd h i.2
      · show l (f i) (f i) * d i ^ 2 ≤ 0
        rw [h]
        nlinarith [sq_nonneg (d i)]
      · show l (f i) (f i) * d i ^ 2 ≤ 0
        rw [h, zero_mul]
    have hq0 : ∑ i, c i ^ 2 = 0 :=
      le_antisymm (hq1 ▸ hq2) (Finset.sum_nonneg fun i _ => sq_nonneg _)
    have hc0 : ∀ i, c i = 0 := by
      intro i
      have h := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => sq_nonneg (c j)).1 hq0 i
        (Finset.mem_univ i)
      exact pow_eq_zero_iff (two_ne_zero) |>.1 h
    rw [← hc]
    simp [hc0]
  have hle := Submodule.finrank_add_finrank_le_of_disjoint hdisj
  rw [hPdim, hNdim, hdim] at hle
  have hcompl : Fintype.card {i : Fin n // ¬ l (f i) (f i) = 1}
      = n - Fintype.card {i : Fin n // l (f i) (f i) = 1} := by
    rw [Fintype.card_subtype_compl, Fintype.card_fin]
  have hposf : Fintype.card {i : Fin n // l (f i) (f i) = 1} ≤ n :=
    (Fintype.card_subtype_le fun i : Fin n => l (f i) (f i) = 1).trans_eq (Fintype.card_fin n)
  rw [hcompl] at hle
  rw [pozitivTagok, pozitivTagok, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  omega

/-- **16.3. Tehetetlenségi tétel.** Bármilyen módon is hozzuk normálalakra a valós
kvadratikus alakot, a pozitív, illetve a negatív tagok száma mindig ugyanaz. -/
theorem tehetetlensegi_tetel {l : V → V → ℝ} (hl : SzimmetrikusBilinearis ℝ l)
    {e f : Fin n → V} (he : Bazis ℝ e) (hf : Bazis ℝ f)
    (hne : Normalalaku l e) (hnf : Normalalaku l f) :
    pozitivTagok l e = pozitivTagok l f ∧ negativTagok l e = negativTagok l f := by
  have hpos : pozitivTagok l e = pozitivTagok l f :=
    le_antisymm (pozitivTagok_le hl he hf hne hnf) (pozitivTagok_le hl hf he hnf hne)
  refine ⟨hpos, ?_⟩
  -- a negatív tagokra a `−l` alakra alkalmazzuk ugyanezt
  set m : V → V → ℝ := fun x y => -(l x y) with hm
  have hml : SzimmetrikusBilinearis ℝ m := by
    refine ⟨⟨fun u₁ u₂ v => ?_, fun u v₁ v₂ => ?_, fun c u v => ?_, fun c u v => ?_⟩,
      fun u v => ?_⟩
    · show -(l (u₁ + u₂) v) = -(l u₁ v) + -(l u₂ v)
      rw [hl.1.1]; ring
    · show -(l u (v₁ + v₂)) = -(l u v₁) + -(l u v₂)
      rw [hl.1.2.1]; ring
    · show -(l (c • u) v) = c * -(l u v)
      rw [hl.1.2.2.1]; ring
    · show -(l u (c • v)) = c * -(l u v)
      rw [hl.1.2.2.2]; ring
    · show -(l u v) = -(l v u)
      rw [hl.2]
  have hmnorm : ∀ {g : Fin n → V}, Normalalaku l g → Normalalaku m g := by
    intro g hg
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · show -(l (g i) (g j)) = 0
      rw [hg.1 i j hij, neg_zero]
    · show -(l (g i) (g i)) = 1 ∨ -(l (g i) (g i)) = -1 ∨ -(l (g i) (g i)) = 0
      rcases hg.2 i with h | h | h
      · right; left; rw [h]
      · left; rw [h]; norm_num
      · right; right; rw [h, neg_zero]
  have hneg : ∀ g : Fin n → V, negativTagok l g = pozitivTagok m g := by
    intro g
    rw [negativTagok, pozitivTagok]
    refine Nat.card_congr (Equiv.subtypeEquivRight fun i => ?_)
    show l (g i) (g i) = -1 ↔ -(l (g i) (g i)) = 1
    constructor
    · intro h; rw [h]; norm_num
    · intro h; linarith
  rw [hneg, hneg]
  exact le_antisymm (pozitivTagok_le hml he hf (hmnorm hne) (hmnorm hnf))
    (pozitivTagok_le hml hf he (hmnorm hnf) (hmnorm hne))

/-! ### Számlálási segédlemmák -/

theorem card_le_n {p : Fin n → Prop} : Nat.card {i : Fin n // p i} ≤ n := by
  classical
  rw [Nat.card_eq_fintype_card]
  exact (Fintype.card_subtype_le p).trans_eq (Fintype.card_fin n)

theorem card_eq_n_iff_forall {p : Fin n → Prop} :
    Nat.card {i : Fin n // p i} = n ↔ ∀ i, p i := by
  classical
  constructor
  · intro h i
    by_contra hi
    have hc : Fintype.card {i : Fin n // ¬ p i} = 0 := by
      rw [Fintype.card_subtype_compl, Fintype.card_fin, ← Nat.card_eq_fintype_card, h,
        Nat.sub_self]
    rw [Fintype.card_eq_zero_iff] at hc
    exact hc.false ⟨i, hi⟩
  · intro h
    rw [Nat.card_eq_fintype_card, Fintype.card_congr (Equiv.subtypeUnivEquiv h),
      Fintype.card_fin]

theorem card_eq_zero_iff_forall_not {p : Fin n → Prop} :
    Nat.card {i : Fin n // p i} = 0 ↔ ∀ i, ¬ p i := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_eq_zero_iff, isEmpty_subtype]

theorem card_pos_iff_exists {p : Fin n → Prop} :
    0 < Nat.card {i : Fin n // p i} ↔ ∃ i, p i := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_pos_iff, nonempty_subtype]

theorem card_lt_n_iff_exists_not {p : Fin n → Prop} :
    Nat.card {i : Fin n // p i} < n ↔ ∃ i, ¬ p i := by
  classical
  rw [lt_iff_le_and_ne, and_iff_right card_le_n, Ne, card_eq_n_iff_forall]
  exact not_forall

/-! ## 16.4. Definíció -/

/-- **16.4. Definíció.** A `q` kvadratikus alak *pozitív definit*, ha `q(v) ≥ 0` minden
`v`-re, és `q(v) = 0` csak `v = 0` esetén. -/
def PozitivDefinit (q : V → ℝ) : Prop := (∀ v, 0 ≤ q v) ∧ ∀ v, q v = 0 → v = 0

/-- **16.4. Definíció.** A `q` kvadratikus alak *negatív definit*, ha `q(v) ≤ 0` minden
`v`-re, és `q(v) = 0` csak `v = 0` esetén. -/
def NegativDefinit (q : V → ℝ) : Prop := (∀ v, q v ≤ 0) ∧ ∀ v, q v = 0 → v = 0

/-- **16.4. Definíció.** A `q` kvadratikus alak *pozitív szemidefinit*, ha `q(v) ≥ 0`
minden `v`-re, de `q(v) = 0` nem csak `v = 0` esetén fordul elő. -/
def PozitivSzemidefinit (q : V → ℝ) : Prop := (∀ v, 0 ≤ q v) ∧ ∃ v, v ≠ 0 ∧ q v = 0

/-- **16.4. Definíció.** A `q` kvadratikus alak *negatív szemidefinit*, ha `q(v) ≤ 0`
minden `v`-re, de `q(v) = 0` nem csak `v = 0` esetén fordul elő. -/
def NegativSzemidefinit (q : V → ℝ) : Prop := (∀ v, q v ≤ 0) ∧ ∃ v, v ≠ 0 ∧ q v = 0

/-- **16.4. Definíció.** A `q` kvadratikus alak *indefinit*, ha pozitív és negatív
értéket is felvesz. -/
def Indefinit (q : V → ℝ) : Prop := (∃ v, 0 < q v) ∧ ∃ v, q v < 0

/-! ## 16.5. Tétel -/

/-- Bázisvektor nem a nullvektor. -/
theorem bazisvektor_ne_zero {e : Fin n → V} (he : Bazis ℝ e) (i : Fin n) : e i ≠ 0 := by
  classical
  intro h
  have hsum : ∑ j, (if j = i then (1 : ℝ) else 0) • e j = 0 := by
    rw [Finset.sum_eq_single i]
    · rw [if_pos rfl, one_smul, h]
    · intro j _ hj
      rw [if_neg hj, zero_smul]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  have := he.1 _ hsum i
  rw [if_pos rfl] at this
  exact one_ne_zero this

/-- Normál alakban `q(∑ xᵢeᵢ) = ∑ l(eᵢ,eᵢ)xᵢ²`. -/
theorem ertek_kombinacio {l : V → V → ℝ} (hl : SzimmetrikusBilinearis ℝ l) {q : V → ℝ}
    (hq : ∀ v, q v = l v v) {e : Fin n → V} (hne : Normalalaku l e) (x : Fin n → ℝ) :
    q (∑ i, x i • e i) = ∑ i, l (e i) (e i) * x i ^ 2 := by
  rw [hq, normalalak_ertek hl.1 hne]

/-- Ha a normálalak minden együtthatója nemnegatív, akkor `q` nemnegatív. -/
theorem nemnegativ_of_egyutthatok {l : V → V → ℝ} (hl : SzimmetrikusBilinearis ℝ l)
    {q : V → ℝ} (hq : ∀ v, q v = l v v) {e : Fin n → V} (he : Bazis ℝ e)
    (hne : Normalalaku l e) (h : ∀ i, 0 ≤ l (e i) (e i)) : ∀ v, 0 ≤ q v := by
  intro v
  rw [koordinatai_spec he v, ertek_kombinacio hl hq hne]
  exact Finset.sum_nonneg fun i _ => mul_nonneg (h i) (sq_nonneg _)

/-- Ha a normálalak minden együtthatója nempozitív, akkor `q` nempozitív. -/
theorem nempozitiv_of_egyutthatok {l : V → V → ℝ} (hl : SzimmetrikusBilinearis ℝ l)
    {q : V → ℝ} (hq : ∀ v, q v = l v v) {e : Fin n → V} (he : Bazis ℝ e)
    (hne : Normalalaku l e) (h : ∀ i, l (e i) (e i) ≤ 0) : ∀ v, q v ≤ 0 := by
  intro v
  rw [koordinatai_spec he v, ertek_kombinacio hl hq hne]
  exact Finset.sum_nonpos fun i _ => mul_nonpos_of_nonpos_of_nonneg (h i) (sq_nonneg _)

/-- **(16.5.1)** `q` pontosan akkor pozitív definit, ha a normálalakjában `k = r = n`,
azaz minden tag pozitív. -/
theorem pozitivDefinit_iff {l : V → V → ℝ} (hl : SzimmetrikusBilinearis ℝ l) {q : V → ℝ}
    (hq : ∀ v, q v = l v v) {e : Fin n → V} (he : Bazis ℝ e) (hne : Normalalaku l e) :
    PozitivDefinit q ↔ pozitivTagok l e = n := by
  rw [pozitivTagok, card_eq_n_iff_forall]
  constructor
  · rintro ⟨hnn, hdef⟩ i
    rcases hne.2 i with h | h | h
    · exact h
    · exact absurd (hnn (e i)) (by rw [hq, h]; norm_num)
    · exact absurd (hdef (e i) (by rw [hq, h])) (bazisvektor_ne_zero he i)
  · intro h
    refine ⟨nemnegativ_of_egyutthatok hl hq he hne fun i => by rw [h i]; norm_num, ?_⟩
    intro v hv
    rw [koordinatai_spec he v, ertek_kombinacio hl hq hne] at hv
    have hz : ∀ i, koordinatai he v i = 0 := by
      intro i
      have hsum : ∀ j ∈ Finset.univ, (0 : ℝ) ≤ l (e j) (e j) * koordinatai he v j ^ 2 :=
        fun j _ => by rw [h j]; simpa using sq_nonneg (koordinatai he v j)
      have := (Finset.sum_eq_zero_iff_of_nonneg hsum).1 hv i (Finset.mem_univ i)
      rw [h i, one_mul] at this
      exact pow_eq_zero_iff two_ne_zero |>.1 this
    rw [koordinatai_spec he v]
    simp [hz]

/-- **(16.5.2)** `q` pontosan akkor negatív definit, ha a normálalakjában `k = 0` és
`r = n`, azaz minden tag negatív. -/
theorem negativDefinit_iff {l : V → V → ℝ} (hl : SzimmetrikusBilinearis ℝ l) {q : V → ℝ}
    (hq : ∀ v, q v = l v v) {e : Fin n → V} (he : Bazis ℝ e) (hne : Normalalaku l e) :
    NegativDefinit q ↔ negativTagok l e = n := by
  rw [negativTagok, card_eq_n_iff_forall]
  constructor
  · rintro ⟨hnp, hdef⟩ i
    rcases hne.2 i with h | h | h
    · exact absurd (hnp (e i)) (by rw [hq, h]; norm_num)
    · exact h
    · exact absurd (hdef (e i) (by rw [hq, h])) (bazisvektor_ne_zero he i)
  · intro h
    refine ⟨nempozitiv_of_egyutthatok hl hq he hne fun i => by rw [h i]; norm_num, ?_⟩
    intro v hv
    rw [koordinatai_spec he v, ertek_kombinacio hl hq hne] at hv
    have hz : ∀ i, koordinatai he v i = 0 := by
      intro i
      have hsum : ∀ j ∈ Finset.univ,
          (0 : ℝ) ≤ -(l (e j) (e j) * koordinatai he v j ^ 2) :=
        fun j _ => by rw [h j]; simpa using sq_nonneg (koordinatai he v j)
      have hv' : ∑ j, -(l (e j) (e j) * koordinatai he v j ^ 2) = 0 := by
        rw [Finset.sum_neg_distrib, hv, neg_zero]
      have := (Finset.sum_eq_zero_iff_of_nonneg hsum).1 hv' i (Finset.mem_univ i)
      rw [h i] at this
      have h2 : koordinatai he v i ^ 2 = 0 := by linarith
      exact pow_eq_zero_iff two_ne_zero |>.1 h2
    rw [koordinatai_spec he v]
    simp [hz]

/-- **(16.5.3)** `q` pontosan akkor pozitív szemidefinit, ha nincs negatív tag, de a
pozitív tagok száma kisebb `n`-nél (`k = r < n`). -/
theorem pozitivSzemidefinit_iff {l : V → V → ℝ} (hl : SzimmetrikusBilinearis ℝ l)
    {q : V → ℝ} (hq : ∀ v, q v = l v v) {e : Fin n → V} (he : Bazis ℝ e)
    (hne : Normalalaku l e) :
    PozitivSzemidefinit q ↔ negativTagok l e = 0 ∧ pozitivTagok l e < n := by
  constructor
  · rintro ⟨hnn, v, hv0, hqv⟩
    constructor
    · rw [negativTagok, card_eq_zero_iff_forall_not]
      intro i hi
      exact absurd (hnn (e i)) (by rw [hq, hi]; norm_num)
    · rw [pozitivTagok, card_lt_n_iff_exists_not]
      by_contra hcon
      push_neg at hcon
      have hall : ∀ i, l (e i) (e i) = 1 := hcon
      have := ((pozitivDefinit_iff hl hq he hne).2
        (by rw [pozitivTagok, card_eq_n_iff_forall]; exact hall)).2 v hqv
      exact hv0 this
  · rintro ⟨hneg, hpos⟩
    rw [negativTagok, card_eq_zero_iff_forall_not] at hneg
    rw [pozitivTagok, card_lt_n_iff_exists_not] at hpos
    obtain ⟨i, hi⟩ := hpos
    have hzero : l (e i) (e i) = 0 := by
      rcases hne.2 i with h | h | h
      · exact absurd h hi
      · exact absurd h (hneg i)
      · exact h
    refine ⟨nemnegativ_of_egyutthatok hl hq he hne fun j => ?_, e i,
      bazisvektor_ne_zero he i, by rw [hq, hzero]⟩
    rcases hne.2 j with h | h | h
    · rw [h]; norm_num
    · exact absurd h (hneg j)
    · rw [h]

/-- **(16.5.4)** `q` pontosan akkor negatív szemidefinit, ha nincs pozitív tag, de a
negatív tagok száma kisebb `n`-nél (`k = 0`, `r < n`). -/
theorem negativSzemidefinit_iff {l : V → V → ℝ} (hl : SzimmetrikusBilinearis ℝ l)
    {q : V → ℝ} (hq : ∀ v, q v = l v v) {e : Fin n → V} (he : Bazis ℝ e)
    (hne : Normalalaku l e) :
    NegativSzemidefinit q ↔ pozitivTagok l e = 0 ∧ negativTagok l e < n := by
  constructor
  · rintro ⟨hnp, v, hv0, hqv⟩
    constructor
    · rw [pozitivTagok, card_eq_zero_iff_forall_not]
      intro i hi
      exact absurd (hnp (e i)) (by rw [hq, hi]; norm_num)
    · rw [negativTagok, card_lt_n_iff_exists_not]
      by_contra hcon
      push_neg at hcon
      have hall : ∀ i, l (e i) (e i) = -1 := hcon
      have := ((negativDefinit_iff hl hq he hne).2
        (by rw [negativTagok, card_eq_n_iff_forall]; exact hall)).2 v hqv
      exact hv0 this
  · rintro ⟨hpos, hneg⟩
    rw [pozitivTagok, card_eq_zero_iff_forall_not] at hpos
    rw [negativTagok, card_lt_n_iff_exists_not] at hneg
    obtain ⟨i, hi⟩ := hneg
    have hzero : l (e i) (e i) = 0 := by
      rcases hne.2 i with h | h | h
      · exact absurd h (hpos i)
      · exact absurd h hi
      · exact h
    refine ⟨nempozitiv_of_egyutthatok hl hq he hne fun j => ?_, e i,
      bazisvektor_ne_zero he i, by rw [hq, hzero]⟩
    rcases hne.2 j with h | h | h
    · exact absurd h (hpos j)
    · rw [h]; norm_num
    · rw [h]

/-- **(16.5.5)** `q` pontosan akkor indefinit, ha van pozitív és negatív tag is
(`0 < k < r`). -/
theorem indefinit_iff {l : V → V → ℝ} (hl : SzimmetrikusBilinearis ℝ l) {q : V → ℝ}
    (hq : ∀ v, q v = l v v) {e : Fin n → V} (he : Bazis ℝ e) (hne : Normalalaku l e) :
    Indefinit q ↔ 0 < pozitivTagok l e ∧ 0 < negativTagok l e := by
  rw [pozitivTagok, negativTagok, card_pos_iff_exists, card_pos_iff_exists]
  constructor
  · rintro ⟨⟨v, hv⟩, ⟨w, hw⟩⟩
    constructor
    · by_contra hcon
      push_neg at hcon
      have hnp : ∀ i, l (e i) (e i) ≤ 0 := by
        intro i
        rcases hne.2 i with h | h | h
        · exact absurd h (hcon i)
        · rw [h]; norm_num
        · rw [h]
      exact absurd (nempozitiv_of_egyutthatok hl hq he hne hnp v) (by linarith)
    · by_contra hcon
      push_neg at hcon
      have hnn : ∀ i, 0 ≤ l (e i) (e i) := by
        intro i
        rcases hne.2 i with h | h | h
        · rw [h]; norm_num
        · exact absurd h (hcon i)
        · rw [h]
      exact absurd (nemnegativ_of_egyutthatok hl hq he hne hnn w) (by linarith)
  · rintro ⟨⟨i, hi⟩, ⟨j, hj⟩⟩
    exact ⟨⟨e i, by rw [hq, hi]; norm_num⟩, ⟨e j, by rw [hq, hj]; norm_num⟩⟩

/-! ## 16.6. Következmény -/

/-- **16.6. Következmény.** Ha `A` valós szimmetrikus mátrix, és a hozzá tartozó
`q(x) = x A xᵀ` kvadratikus alak pozitív definit, akkor van olyan nemelfajuló `P` mátrix,
amelyre `A = P Pᵀ`.

*Bizonyítás (a jegyzet szerint).* A `q` alak a standard bázisban éppen `A` mátrixú.
A 16.2. Tétel szerint van olyan `f` bázis, amelyben `q` normálalakú; mivel `q` pozitív
definit, a 16.5. Tétel szerint a normálalak minden együtthatója `1`, azaz `q` mátrixa az
`f` bázisban az `E` egységmátrix. Ha `S` az `f`-ről a standard bázisra való áttérés
mátrixa, akkor a 15.5. Tétel szerint `E = S A Sᵀ`. Az `S` mátrix nemelfajuló (áttérési
mátrix), inverzével, `P := S⁻¹` jelöléssel
`A = E A E = (P S) A (Sᵀ Pᵀ) = P (S A Sᵀ) Pᵀ = P E Pᵀ = P Pᵀ`. -/
theorem pozitivDefinit_felbontas {A : Matrix' ℝ n n} (hA : Szimmetrikus A)
    (hpd : PozitivDefinit fun x : Fin n → ℝ => ∑ i, ∑ j, x i * A i j * x j) :
    ∃ P : Matrix' ℝ n n, det' P ≠ 0 ∧ A = P * Pᵀ := by
  classical
  -- Az `A`-hoz tartozó bilineáris alak.
  set l : (Fin n → ℝ) → (Fin n → ℝ) → ℝ := fun x y => Matrix.toBilin' A x y with hl_def
  have hbil : BilinearisLekepezes ℝ l := by
    refine ⟨?_, ?_, ?_, ?_⟩ <;> intros <;> simp [hl_def]
  have hAij : ∀ i j, A j i = A i j := fun i j => congrFun (congrFun hA i) j
  have hsym : ∀ u v, l u v = l v u := by
    intro u v
    simp only [hl_def, Matrix.toBilin'_apply]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
      rw [hAij i j]; ring
  have hl : SzimmetrikusBilinearis ℝ l := ⟨hbil, hsym⟩
  -- A standard bázis, amelyben `l` mátrixa `A`.
  set B : Module.Basis (Fin n) ℝ (Fin n → ℝ) := Pi.basisFun ℝ (Fin n) with hB_def
  have hstd : Bazis ℝ ⇑B := bazis_of_moduleBasis B
  have hmatA : bilinMatrixa (⇑B) (⇑B) l = A := by
    funext i j
    simp [bilinMatrixa, hl_def, hB_def, Pi.basisFun_apply, Matrix.toBilin'_single]
  -- A kvadratikus alak `l`-lel kifejezve.
  have hqeq : (fun x : Fin n → ℝ => ∑ i, ∑ j, x i * A i j * x j) = fun x => l x x := by
    funext x
    simp [hl_def, Matrix.toBilin'_apply]
  rw [hqeq] at hpd
  -- 16.2: normálalakú bázis.
  obtain ⟨f, hf, hnf⟩ := letezik_normalalak hl hstd
  -- 16.5: pozitív definit ⇒ minden együttható `1`.
  have hall : ∀ i, l (f i) (f i) = 1 := by
    have := (pozitivDefinit_iff hl (fun v => rfl) hf hnf).1 hpd
    rwa [pozitivTagok, card_eq_n_iff_forall] at this
  have hmat1 : bilinMatrixa f f l = 1 := by
    funext i j
    rcases eq_or_ne i j with rfl | hij
    · simp [bilinMatrixa, hall i]
    · simp [bilinMatrixa, hnf.1 i j hij, Matrix.one_apply_ne hij]
  -- Áttérési mátrixok az `f` és a standard bázis között.
  obtain ⟨S, hS, -⟩ := letezik_egyertelmu_atteres (T := ℝ) (e := f) hstd
  obtain ⟨S', hS', -⟩ := letezik_egyertelmu_atteres (T := ℝ) (e := ⇑B) hf
  have hinv : Inverze S S' := atteres_inverze hf hstd hS hS'
  refine ⟨S', det_ne_zero_of_inverze (inverz_inverze hinv), ?_⟩
  -- 15.5: `E = S A Sᵀ`.
  have hkulcs : (1 : Matrix' ℝ n n) = S * A * Sᵀ := by
    rw [← hmat1, ← hmatA]
    exact bilinMatrixa_baziscsere hbil hS
  have hT : Sᵀ * S'ᵀ = 1 := by
    rw [← Matrix.transpose_mul, hinv.1, Matrix.transpose_one]
  calc A = (S' * S) * A * (Sᵀ * S'ᵀ) := by rw [hinv.1, hT, Matrix.one_mul, Matrix.mul_one]
    _ = S' * (S * A * Sᵀ) * S'ᵀ := by simp [Matrix.mul_assoc]
    _ = S' * S'ᵀ := by rw [← hkulcs, Matrix.mul_one]

end Ch16
end SzaboLinAlg
