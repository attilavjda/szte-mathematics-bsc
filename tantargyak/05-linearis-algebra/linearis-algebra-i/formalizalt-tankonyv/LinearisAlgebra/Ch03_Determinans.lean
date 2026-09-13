import LinearisAlgebra.Ch02_Matrixok

/-!
# Szabó László: Bevezetés a lineáris algebrába — 3. fejezet: Az n-edrendű determináns

A jegyzet 3. fejezetének (9–15. oldal) formalizálása: a determináns rekurzív definíciója,
a komplementer és adjungált aldeterminánsok, a sorcsere előjelváltó hatása, a determináns
kifejtése tetszőleges sora szerint, a sorokra vonatkozó tulajdonságok, valamint a
transzponáltra vonatkozó tétel.

**Előjelkonvenció.** A jegyzet az `1`-től induló indexelést használja, így a kifejtésben
`(-1)^{k+1}` szerepel; a Lean `Fin n` típusa `0`-tól indexel, ezért nálunk ugyanez az
előjel `(-1)^k` alakot ölt.
-/

namespace SzaboLinAlg
namespace Ch03

open scoped BigOperators
open Matrix

variable {T : Type*} [CommRing T]

/-! ## 3.1. Definíció: az n-edrendű determináns -/

/-- **3.1. Definíció.** Az `A` mátrix determinánsa rekurzív definícióval:
`|A| = a₁₁`, ha `n = 1`, és
`|A| = a₁₁D₁₁ - a₁₂D₁₂ + … + (-1)^{n+1}a₁ₙD₁ₙ`, ha `n ≥ 2`,
ahol `D₁ₖ` az első sor `k`-adik eleméhez tartozó komplementer aldetermináns
(az első sor és a `k`-adik oszlop törlésével keletkező `(n-1)`-edrendű determináns).

A `0`-adrendű (üres) determináns értéke — a szokásos konvenció szerint — `1`. -/
def det' : {n : ℕ} → Matrix (Fin n) (Fin n) T → T
  | 0, _ => 1
  | n + 1, A =>
      ∑ k : Fin (n + 1), (-1) ^ (k : ℕ) * A 0 k * det' (A.submatrix Fin.succ k.succAbove)

/-- A jegyzet rekurzív determináns-definíciója megegyezik a Mathlib `Matrix.det`
fogalmával (a Mathlib szerinti kifejtés az első sor szerint). -/
theorem det'_eq_det : ∀ {n : ℕ} (A : Matrix (Fin n) (Fin n) T), det' A = A.det
  | 0, A => by simp [det']
  | n + 1, A => by
      rw [det', Matrix.det_succ_row_zero]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [det'_eq_det (A.submatrix Fin.succ k.succAbove)]

/-- Elsőrendű determináns: `|A| = a₁₁`. -/
theorem det'_one (A : Matrix (Fin 1) (Fin 1) T) : det' A = A 0 0 := by
  rw [det'_eq_det, Matrix.det_fin_one]

/-- Másodrendű determináns: `|A| = a₁₁a₂₂ - a₁₂a₂₁`. -/
theorem det'_two (A : Matrix (Fin 2) (Fin 2) T) :
    det' A = A 0 0 * A 1 1 - A 0 1 * A 1 0 := by
  rw [det'_eq_det, Matrix.det_fin_two]

/-- Harmadrendű determináns kifejtett alakja (a jegyzet 9–10. oldala). -/
theorem det'_three (A : Matrix (Fin 3) (Fin 3) T) :
    det' A = A 0 0 * A 1 1 * A 2 2 - A 0 0 * A 1 2 * A 2 1 - A 0 1 * A 1 0 * A 2 2
      + A 0 1 * A 1 2 * A 2 0 + A 0 2 * A 1 0 * A 2 1 - A 0 2 * A 1 1 * A 2 0 := by
  rw [det'_eq_det, Matrix.det_fin_three]

/-! ## 3.2. Definíció: komplementer és adjungált aldetermináns -/

variable {n : ℕ}

/-- **3.2. Definíció.** Az `aᵢⱼ` elemhez tartozó *komplementer aldetermináns* `Dᵢⱼ`: az
`i`-edik sor és a `j`-edik oszlop törlésével kapott `(n-1)`-edrendű determináns. -/
def komplementerAldeterminans (A : Matrix (Fin (n + 1)) (Fin (n + 1)) T)
    (i j : Fin (n + 1)) : T :=
  det' (A.submatrix i.succAbove j.succAbove)

/-- **3.2. Definíció.** Az `aᵢⱼ` elemhez tartozó *adjungált aldetermináns*:
`Aᵢⱼ = (-1)^{i+j}Dᵢⱼ`. -/
def adjungaltAldeterminans (A : Matrix (Fin (n + 1)) (Fin (n + 1)) T)
    (i j : Fin (n + 1)) : T :=
  (-1) ^ ((i : ℕ) + (j : ℕ)) * komplementerAldeterminans A i j

/-! ## 3.3. Tétel: sorcsere -/

/-- **3.3. Tétel.** Ha egy determináns két sorát felcseréljük, akkor értéke
`(-1)`-szeresére változik.

A jegyzet a determináns rendje szerinti teljes indukcióval bizonyít; itt a sorok
permutálására vonatkozó általános tételt használjuk, amely szerint a sorok `σ` szerinti
permutálása a determinánst `sgn σ`-val szorozza, s a transzpozíció előjele `-1`. -/
theorem det_sorcsere (A : Matrix (Fin n) (Fin n) T) {i j : Fin n} (hij : i ≠ j) :
    det' (A.submatrix (Equiv.swap i j) id) = -det' A := by
  rw [det'_eq_det, det'_eq_det, Matrix.det_permute, Equiv.Perm.sign_swap hij]
  simp

/-! ## 3.4. Tétel: kifejtés az i-edik sor szerint -/

/-- **3.4. Tétel.** Tetszőleges `i` esetén `|A| = ∑ₖ aᵢₖAᵢₖ`, azaz a determináns
kifejthető bármely sora szerint. -/
theorem det_kifejtes_sor (A : Matrix (Fin (n + 1)) (Fin (n + 1)) T) (i : Fin (n + 1)) :
    det' A = ∑ k, A i k * adjungaltAldeterminans A i k := by
  rw [det'_eq_det, Matrix.det_succ_row A i]
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold adjungaltAldeterminans komplementerAldeterminans
  rw [det'_eq_det]
  ring

/-! ## 3.5. Tétel: a determináns soraira vonatkozó tulajdonságok -/

/-- **(3.5.1)** Ha egy sor minden elemét `c`-vel szorozzuk, a determináns `c`-szeresére
változik. -/
theorem det_sor_skalarszoros (A : Matrix (Fin n) (Fin n) T) (i : Fin n) (c : T) :
    det' (A.updateRow i (c • A i)) = c * det' A := by
  rw [det'_eq_det, det'_eq_det, Matrix.det_updateRow_smul, Matrix.updateRow_eq_self]

/-- **(3.5.2)** A determináns értéke nulla, ha valamelyik sorában mindegyik elem nulla. -/
theorem det_nulla_sor (A : Matrix (Fin n) (Fin n) T) (i : Fin n) (h : ∀ j, A i j = 0) :
    det' A = 0 := by
  rw [det'_eq_det]
  exact Matrix.det_eq_zero_of_row_eq_zero i h

/-- **(3.5.3)** A determináns értéke nulla, ha van két egyforma sora.

*Bizonyítás (a jegyzet szerint).* Ha a `D` determináns két sora megegyezik, akkor az e
két sor felcserélésével kapott `D̄` determinánsra `D̄ = D` és `D̄ = -D`, amiből `D = 0`
következik. -/
theorem det_egyforma_sor (A : Matrix (Fin n) (Fin n) T) {i j : Fin n} (hij : i ≠ j)
    (h : A i = A j) : det' A = 0 := by
  rw [det'_eq_det]
  exact Matrix.det_zero_of_row_eq hij (by rw [h])

/-- **(3.5.4)** A determináns additív az `i`-edik sorában:
ha az `i`-edik sor `bᵢⱼ + cᵢⱼ` alakú, akkor a determináns a két megfelelő determináns
összege. -/
theorem det_sor_additiv (A : Matrix (Fin n) (Fin n) T) (i : Fin n) (b c : Fin n → T) :
    det' (A.updateRow i (b + c))
      = det' (A.updateRow i b) + det' (A.updateRow i c) := by
  rw [det'_eq_det, det'_eq_det, det'_eq_det]
  exact Matrix.det_updateRow_add A i b c

/-- **(3.5.5)** Ha egy sorhoz egy másik sor `c`-szeresét adjuk, a determináns értéke nem
változik.

*Bizonyítás (a jegyzet szerint).* A (3.5.4), (3.5.1) és (3.5.3) állításokból: a felbontás
második tagjában két egyforma sor szerepel, így az nulla. -/
theorem det_sor_hozzaadas (A : Matrix (Fin n) (Fin n) T) {i j : Fin n} (hij : i ≠ j)
    (c : T) : det' (A.updateRow i (A i + c • A j)) = det' A := by
  have hzero : (A.updateRow i (A j)).det = 0 := by
    refine Matrix.det_zero_of_row_eq hij ?_
    rw [Matrix.updateRow_self, Matrix.updateRow_ne (Ne.symm hij)]
  rw [det'_eq_det, det'_eq_det, Matrix.det_updateRow_add, Matrix.updateRow_eq_self,
    Matrix.det_updateRow_smul, hzero]
  ring

/-! ## 3.6. Tétel: a transzponált determinánsa -/

/-- **3.6. Tétel.** Bármely négyzetes mátrix determinánsa megegyezik transzponáltjának
determinánsával. -/
theorem det_transzponalt (A : Matrix (Fin n) (Fin n) T) : det' Aᵀ = det' A := by
  rw [det'_eq_det, det'_eq_det, Matrix.det_transpose]

/-- A transzponált komplementer aldeterminánsai: `Dᵀ_{ji} = D_{ij}`. -/
theorem komplementer_transzponalt (A : Matrix (Fin (n + 1)) (Fin (n + 1)) T)
    (i j : Fin (n + 1)) :
    komplementerAldeterminans Aᵀ j i = komplementerAldeterminans A i j := by
  unfold komplementerAldeterminans
  rw [det'_eq_det, det'_eq_det, ← Matrix.det_transpose (A.submatrix i.succAbove j.succAbove)]
  congr 1

/-- A 3.6. Tétel következménye: minden, a sorokra vonatkozó tulajdonság érvényes az
oszlopokra is; például a determináns kifejthető bármely oszlopa szerint. -/
theorem det_kifejtes_oszlop (A : Matrix (Fin (n + 1)) (Fin (n + 1)) T) (j : Fin (n + 1)) :
    det' A = ∑ k, A k j * adjungaltAldeterminans A k j := by
  rw [← det_transzponalt A, det_kifejtes_sor Aᵀ j]
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold adjungaltAldeterminans
  rw [Matrix.transpose_apply, komplementer_transzponalt, Nat.add_comm]

end Ch03
end SzaboLinAlg
