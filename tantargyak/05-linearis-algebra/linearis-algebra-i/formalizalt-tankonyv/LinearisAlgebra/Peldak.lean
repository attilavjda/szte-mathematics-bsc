import LinearisAlgebra.Ch05_Egyenletrendszerek
import LinearisAlgebra.Ch06_Vektorterek

/-!
# Szabó László: Bevezetés a lineáris algebrába — kidolgozott példák

Ebben a modulban a jegyzet *számozott példáit* formalizáljuk, azokat, amelyek a
fejezetenkénti modulokban még nem szerepelnek:

* **5.6.1. Példa** — az `x₁ + x₂ + 2x₃ = 3`, `4x₁ + 4x₂ + 5x₃ = 6`, `7x₁ + 7x₂ + 8x₃ = 10`
  egyenletrendszer *ellentmondó*,
* **5.6.2. Példa** — az `x₁ + 2x₂ + 3x₃ = 4`, `5x₁ + 6x₂ + 7x₃ = 8`, `9x₁ + 10x₂ + 11x₃ = 12`,
  `13x₁ + 14x₂ + 15x₃ = 16` egyenletrendszer megoldásai éppen az
  `x₁ = −2 + x₃`, `x₂ = 3 − 2x₃` alakú elem-hármasok (`x₃` a szabad ismeretlen),
* **6.2.1. Példa** — a síkbeli, illetve a térbeli vektorok vektorteret alkotnak `ℝ` felett,
* **6.8.2. Példa** — a sorozatok vektorterében altér az `I ⊆ ℕ` indexhalmazon eltűnő
  sorozatok halmaza, és altér a csak véges sok nem nulla tagú sorozatok halmaza is,
* **6.8.3. Példa** — a valós függvények vektorterében altér a polinomfüggvények halmaza,
  és altér az adott `X ⊆ ℝ` halmazon eltűnő függvények halmaza.

A jegyzet további számozott példái már a megfelelő fejezetmodulokban megtalálhatók:
a (6.2.2)–(6.2.5) példák a `Ch06_Vektorterek` `matrixVektorter`, `sorozatVektorter`,
`fuggvenyVektorter`, `tupleVektorter` definícióiként, a (6.8.1) triviális alterek az
`alter_zero`, `alter_univ` állításokként, a 17.2. Példa pedig a `Ch17_EuklidesziTerek`
`standardBSZ`, `standardBSZ_belsoSzorzat` párosaként.
-/

namespace SzaboLinAlg
namespace Peldak

open scoped BigOperators
open SzaboLinAlg.Ch02 SzaboLinAlg.Ch05 SzaboLinAlg.Ch06

/-! ## 5.6.1. Példa: ellentmondó egyenletrendszer -/

/-- Az (5.6.1) példa egyenletrendszerének mátrixa. -/
def A561 : Matrix' ℝ 3 3 := !![1, 1, 2; 4, 4, 5; 7, 7, 8]

/-- Az (5.6.1) példa egyenletrendszerének konstansvektora. -/
def b561 : Fin 3 → ℝ := ![3, 6, 10]

/-- **(5.6.1) Példa.** Az

`x₁ + x₂ + 2x₃ = 3`, `4x₁ + 4x₂ + 5x₃ = 6`, `7x₁ + 7x₂ + 8x₃ = 10`

egyenletrendszer ellentmondó.

*Bizonyítás.* A könyv Gauss-eliminációval lépcsős alakra hozza a bővített mátrixot, és az
utolsó sorból olvassa le az ellentmondást. Ez a lépéssorozat épp azt mutatja, hogy az
első sor, a második sor `(−2)`-szerese és a harmadik sor összege a `(0,0,0)` együtthatós
sort adja, a jobb oldalon viszont `3 − 12 + 10 = 1 ≠ 0` áll. -/
theorem pelda_5_6_1 : Ellentmondo A561 b561 := by
  rintro ⟨c, hc⟩
  have h0 := hc 0
  have h1 := hc 1
  have h2 := hc 2
  simp [A561, b561, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one] at h0 h1 h2
  linarith

/-! ## 5.6.2. Példa: egyparaméteres megoldáshalmaz -/

/-- Az (5.6.2) példa egyenletrendszerének mátrixa. -/
def A562 : Matrix' ℝ 4 3 := !![1, 2, 3; 5, 6, 7; 9, 10, 11; 13, 14, 15]

/-- Az (5.6.2) példa egyenletrendszerének konstansvektora. -/
def b562 : Fin 4 → ℝ := ![4, 8, 12, 16]

/-- **(5.6.2) Példa.** Az

`x₁ + 2x₂ + 3x₃ = 4`, `5x₁ + 6x₂ + 7x₃ = 8`, `9x₁ + 10x₂ + 11x₃ = 12`,
`13x₁ + 14x₂ + 15x₃ = 16`

egyenletrendszer megoldásai pontosan azok az elem-hármasok, amelyekre

`x₁ = −2 + x₃` és `x₂ = 3 − 2x₃`,

azaz `x₃` az egyetlen szabad ismeretlen. -/
theorem pelda_5_6_2 (c : Fin 3 → ℝ) :
    Megoldasa A562 b562 c ↔ (c 0 = -2 + c 2 ∧ c 1 = 3 - 2 * c 2) := by
  constructor
  · intro hc
    have h0 := hc 0
    have h1 := hc 1
    simp [A562, b562, Fin.sum_univ_three] at h0 h1
    constructor <;> linarith
  · rintro ⟨h0, h1⟩
    intro i
    fin_cases i <;>
      simp [A562, b562, Fin.sum_univ_three, h0, h1] <;> ring

/-- **(5.6.2) Példa.** Az (5.6.2) egyenletrendszer megoldáshalmaza egyparaméteres:
`{(−2 + t, 3 − 2t, t) : t ∈ ℝ}`. -/
theorem pelda_5_6_2_megoldashalmaz :
    {c : Fin 3 → ℝ | Megoldasa A562 b562 c} = {c | ∃ t : ℝ, c = ![-2 + t, 3 - 2 * t, t]} := by
  ext c
  simp only [Set.mem_setOf_eq, pelda_5_6_2]
  constructor
  · rintro ⟨h0, h1⟩
    refine ⟨c 2, ?_⟩
    funext i
    fin_cases i <;> simp [h0, h1]
  · rintro ⟨t, rfl⟩
    refine ⟨by norm_num [Matrix.cons_val_two, Matrix.tail_cons],
      by norm_num [Matrix.cons_val_two, Matrix.tail_cons]⟩

/-! ## 6.2.1. Példa: a síkbeli és a térbeli vektorok vektortere -/

/-- **(6.2.1) Példa.** A síkbeli vektorok (a szokásos összeadással és skalárral való
szorzással) vektorteret alkotnak a valós számtest felett. -/
noncomputable def sikVektorter : Vektorter ℝ (Fin 2 → ℝ) := tupleVektorter ℝ 2

/-- **(6.2.1) Példa.** A térbeli vektorok vektorteret alkotnak a valós számtest felett. -/
noncomputable def terVektorter : Vektorter ℝ (Fin 3 → ℝ) := tupleVektorter ℝ 3

/-! ## 6.8.2. Példa: alterek a sorozatok vektorterében -/

/-- **(6.8.2) Példa.** A sorozatok vektorterében altér azoknak a sorozatoknak a halmaza,
melyek `i`-edik tagja nulla minden `i ∈ I` esetén, ahol `I ⊆ ℕ` egy rögzített halmaz. -/
theorem alter_eltuno_sorozatok (I : Set ℕ) :
    Alter ℝ {a : ℕ → ℝ | ∀ i ∈ I, a i = 0} := by
  refine ⟨⟨0, fun i _ => rfl⟩, ?_, ?_⟩
  · intro a ha b hb i hi
    simp [ha i hi, hb i hi]
  · intro l a ha i hi
    simp [ha i hi]

/-- **(6.8.2) Példa.** Altér azoknak a sorozatoknak a halmaza is, melyeknek csak véges sok
tagja nem nulla. -/
theorem alter_veges_tartoju_sorozatok :
    Alter ℝ {a : ℕ → ℝ | {i | a i ≠ 0}.Finite} := by
  refine ⟨⟨0, by simp⟩, ?_, ?_⟩
  · intro a ha b hb
    refine Set.Finite.subset (ha.union hb) ?_
    intro i hi
    by_contra hcon
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hcon
    exact hi (by simp [hcon.1, hcon.2])
  · intro l a ha
    refine Set.Finite.subset ha ?_
    intro i hi
    simp only [Set.mem_setOf_eq] at hi ⊢
    intro hai
    exact hi (by simp [hai])

/-! ## 6.8.3. Példa: alterek a valós függvények vektorterében -/

/-- **(6.8.3) Példa.** A valós függvények vektorterében altér a polinomfüggvények
halmaza. -/
theorem alter_polinomfuggvenyek :
    Alter ℝ {f : ℝ → ℝ | ∃ p : Polynomial ℝ, f = fun x => p.eval x} := by
  refine ⟨⟨0, ⟨0, by funext x; simp⟩⟩, ?_, ?_⟩
  · rintro f ⟨p, rfl⟩ g ⟨q, rfl⟩
    exact ⟨p + q, by funext x; simp⟩
  · rintro l f ⟨p, rfl⟩
    exact ⟨Polynomial.C l * p, by funext x; simp⟩

/-- **(6.8.3) Példa.** Altér azoknak az `f(x)` függvényeknek a halmaza is, melyekre
`f(x) = 0` minden `x ∈ X` esetén, ahol `X ⊆ ℝ` egy rögzített halmaz. -/
theorem alter_eltuno_fuggvenyek (X : Set ℝ) :
    Alter ℝ {f : ℝ → ℝ | ∀ x ∈ X, f x = 0} := by
  refine ⟨⟨0, fun x _ => rfl⟩, ?_, ?_⟩
  · intro f hf g hg x hx
    simp [hf x hx, hg x hx]
  · intro l f hf x hx
    simp [hf x hx]

end Peldak
end SzaboLinAlg
