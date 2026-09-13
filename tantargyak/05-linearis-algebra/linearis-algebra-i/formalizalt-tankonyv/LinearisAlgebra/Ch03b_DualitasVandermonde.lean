import LinearisAlgebra.Ch03_Determinans

/-!
# Szabó László: Bevezetés a lineáris algebrába — 3. fejezet (folytatás)

A jegyzet 3. fejezetének (15–20. oldal) hátralévő anyaga:

* **3.7. Determinánselméti dualitási elv** — a „sor” és „oszlop” szavak felcserélésével
  érvényes állításból ismét érvényes állítást kapunk,
* **3.8. Tétel** — két oszlop felcserélése a determináns előjelét váltja,
* **3.9. Tétel** — kifejtés az `i`-edik oszlop szerint (a 3.4. Tétel duálisa), valamint a
  3.5. Tétel oszlopokra vonatkozó duálisai,
* **3.11. Definíció, 3.12. Tétel** — a Vandermonde-determináns és értéke,
* **3.13. Definíció** — `r`-edrendű aldetermináns és komplementer aldeterminánsa,
* **3.16. A determinánsok szorzástétele** — `|AB| = |A|·|B|`.

A **3.14. Laplace-tételt** és annak **3.15.** duálisát a jegyzet bizonyítás nélkül
közli; ezek a `Ch03c_Laplace.lean` modulban szerepelnek, teljes bizonyítással.

A 3.10. *ferde kifejtési tétel* a 4. fejezetben (`Ch04_Inverzmatrix.lean`,
`ferde_kifejtes_sor`) szerepel, mert ott van rá szükség az inverzmátrix előállításához.
-/

namespace SzaboLinAlg
namespace Ch03

open scoped BigOperators
open Matrix

variable {T : Type*} [CommRing T] {n : ℕ}

/-! ## 3.7. Determinánselméleti dualitási elv -/

omit [CommRing T] in
/-- **3.7. Determinánselméleti dualitási elv.** Bármely determinánsokra vonatkozó érvényes
állításból ismét érvényes állítást kapunk, ha benne a „sor” szó helyett mindenhol az
„oszlop” szót, az „oszlop” szó helyett pedig mindenhol a „sor” szót írjuk.

Az elv formális magja a következő két észrevétel: (a) a 3.6. Tétel szerint `|Aᵀ| = |A|`,
(b) az `Aᵀ` mátrix sorai éppen az `A` mátrix oszlopai (`transpose_apply`). Így ha egy `P`
tulajdonság *minden* mátrixra teljesül, akkor az `Aᵀ`-re alkalmazva a duális állítást
kapjuk. Az alábbi lemma ezt a „behelyettesítést” rögzíti; a fejezet duális tételeit
(3.8., 3.9. és a 3.5. Tétel duálisai) ezzel a sémával nyerjük. -/
theorem dualitasi_elv {P : Matrix (Fin n) (Fin n) T → Prop} (h : ∀ A, P A)
    (A : Matrix (Fin n) (Fin n) T) : P Aᵀ := h Aᵀ

/-! ## 3.8. Tétel: oszlopcsere -/

/-- **3.8. Tétel.** Ha egy determináns két oszlopát felcseréljük, akkor értéke
`(-1)`-szeresére változik (a 3.3. Tétel duálisa). -/
theorem det_oszlopcsere (A : Matrix (Fin n) (Fin n) T) {i j : Fin n} (hij : i ≠ j) :
    det' (A.submatrix id (Equiv.swap i j)) = -det' A := by
  have h := det_sorcsere Aᵀ hij
  rw [det_transzponalt] at h
  rw [← h, ← det_transzponalt (Aᵀ.submatrix (Equiv.swap i j) id)]
  congr 1

/-! ## 3.9. Tétel és a 3.5. Tétel duálisai -/

/-- **3.9. Tétel.** A determináns kifejthető bármely oszlopa szerint:
`|A| = ∑ₖ a_{kj}A_{kj}`.

(Ez a 3.4. Tétel duálisa; a bizonyítást lásd a `det_kifejtes_oszlop` tételnél.) -/
theorem det_kifejtes_oszlop_dualis (A : Matrix (Fin (n + 1)) (Fin (n + 1)) T)
    (j : Fin (n + 1)) : det' A = ∑ k, A k j * adjungaltAldeterminans A k j :=
  det_kifejtes_oszlop A j

/-- **(3.5.1) duálisa.** Ha egy oszlop minden elemét `c`-vel szorozzuk, a determináns
`c`-szeresére változik. -/
theorem det_oszlop_skalarszoros (A : Matrix (Fin n) (Fin n) T) (j : Fin n) (c : T) :
    det' (A.updateCol j (c • fun i => A i j)) = c * det' A := by
  rw [det'_eq_det, det'_eq_det, Matrix.det_updateCol_smul]
  congr 1
  rw [Matrix.updateCol_eq_self]

/-- **(3.5.2) duálisa.** A determináns értéke nulla, ha valamelyik oszlopában minden elem
nulla. -/
theorem det_nulla_oszlop (A : Matrix (Fin n) (Fin n) T) (j : Fin n) (h : ∀ i, A i j = 0) :
    det' A = 0 := by
  rw [det'_eq_det]
  exact Matrix.det_eq_zero_of_column_eq_zero j h

/-- **(3.5.3) duálisa.** A determináns értéke nulla, ha van két egyforma oszlopa. -/
theorem det_egyforma_oszlop (A : Matrix (Fin n) (Fin n) T) {i j : Fin n} (hij : i ≠ j)
    (h : ∀ k, A k i = A k j) : det' A = 0 := by
  rw [det'_eq_det]
  exact Matrix.det_zero_of_column_eq hij h

/-- **(3.5.4) duálisa.** A determináns additív a `j`-edik oszlopában. -/
theorem det_oszlop_additiv (A : Matrix (Fin n) (Fin n) T) (j : Fin n) (b c : Fin n → T) :
    det' (A.updateCol j (b + c))
      = det' (A.updateCol j b) + det' (A.updateCol j c) := by
  rw [det'_eq_det, det'_eq_det, det'_eq_det]
  exact Matrix.det_updateCol_add A j b c

/-- **(3.5.5) duálisa.** Ha egy oszlophoz egy másik oszlop `c`-szeresét adjuk, a
determináns értéke nem változik. -/
theorem det_oszlop_hozzaadas (A : Matrix (Fin n) (Fin n) T) {i j : Fin n} (hij : i ≠ j)
    (c : T) :
    det' (A.updateCol i ((fun k => A k i) + c • fun k => A k j)) = det' A := by
  have h := det_sor_hozzaadas Aᵀ hij c
  rw [det_transzponalt, Matrix.updateRow_transpose, det_transzponalt] at h
  exact h

/-! ## 3.11. Definíció, 3.12. Tétel: a Vandermonde-determináns -/

/-- **3.11. Definíció.** Az `x₁,…,xₙ` számokhoz tartozó *Vandermonde-mátrix*: `i`-edik
sora `1, xᵢ, xᵢ², …, xᵢⁿ⁻¹`. -/
def vandermondeMatrix (x : Fin n → T) : Matrix (Fin n) (Fin n) T :=
  Matrix.vandermonde x

/-- **3.11. Definíció.** A `V(x₁,…,xₙ)` *Vandermonde-determináns*. -/
def vandermondeDet (x : Fin n → T) : T := det' (vandermondeMatrix x)

@[simp] theorem vandermondeMatrix_apply (x : Fin n → T) (i j : Fin n) :
    vandermondeMatrix x i j = x i ^ (j : ℕ) := rfl

/-- **3.12. Tétel.** Tetszőleges `n ≥ 1` és `x₁,…,xₙ` számok esetén
`V(x₁,…,xₙ) = ∏_{i<j} (xⱼ - xᵢ)`.

*Bizonyítás (a jegyzet szerint).* `n` szerinti teljes indukcióval: minden oszlopból
(hátulról előre haladva) levonjuk az előtte álló oszlop `x₁`-szeresét — a 3.5. Tétel
duálisa szerint a determináns értéke nem változik —, majd kifejtjük az első sora szerint,
végül minden sorból kiemeljük a közös `xᵢ - x₁` tényezőt, és alkalmazzuk az indukciós
feltevést. -/
theorem vandermondeDet_eq (x : Fin n → T) :
    vandermondeDet x = ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (x j - x i) := by
  rw [vandermondeDet, det'_eq_det, vandermondeMatrix, Matrix.det_vandermonde]

/-- A kételemű Vandermonde-determináns: `V(x₁,x₂) = x₂ - x₁`. -/
theorem vandermondeDet_two (x : Fin 2 → T) : vandermondeDet x = x 1 - x 0 := by
  rw [vandermondeDet, det'_two]
  simp [vandermondeMatrix]

/-! ## 3.13. Definíció: `r`-edrendű aldetermináns és komplementere -/

/-- **3.13. Definíció.** Jelöljük ki az `A` mátrix `I = {i₁ < … < i_r}` sorait és
`J = {j₁ < … < j_r}` oszlopait. Az `M_{i₁,…,i_r}^{j₁,…,j_r}` *aldetermináns* a kijelölt
sorok és oszlopok metszetében álló elemekből képezett `r`-edrendű determináns. -/
noncomputable def kijeloltAldeterminans (A : Matrix (Fin n) (Fin n) T)
    (I J : Finset (Fin n)) (h : I.card = J.card) : T :=
  det' (A.submatrix (I.orderEmbOfFin rfl)
    (fun k => J.orderEmbOfFin rfl (Fin.cast h k)))

/-- **3.13. Definíció.** A `D_{i₁,…,i_r}^{j₁,…,j_r}` *komplementer aldetermináns*: az
`i₁,…,i_r`-en kívüli sorok és a `j₁,…,j_r`-en kívüli oszlopok által meghatározott
`(n-r)`-edrendű aldetermináns. -/
noncomputable def komplementerKijeloltAldeterminans (A : Matrix (Fin n) (Fin n) T)
    (I J : Finset (Fin n)) (h : I.card = J.card) : T :=
  det' (A.submatrix (Iᶜ.orderEmbOfFin rfl)
    (fun k => Jᶜ.orderEmbOfFin rfl (Fin.cast (by
      rw [Finset.card_compl, Finset.card_compl, h]) k)))

/-- Egyelemű kijelölés esetén az aldetermináns maga a mátrixelem — ez mutatja, hogy a
3.13. Definíció az `r = 1` esetben a 3.2. Definícióhoz vezet vissza. -/
theorem kijeloltAldeterminans_singleton (A : Matrix (Fin n) (Fin n) T) (i j : Fin n) :
    kijeloltAldeterminans A {i} {j} (by simp) = A i j := by
  rw [kijeloltAldeterminans, det'_one]
  have hi : ∀ k, ({i} : Finset (Fin n)).orderEmbOfFin rfl k = i := fun k =>
    Finset.mem_singleton.1 (Finset.orderEmbOfFin_mem _ _ _)
  have hj : ∀ k, ({j} : Finset (Fin n)).orderEmbOfFin rfl k = j := fun k =>
    Finset.mem_singleton.1 (Finset.orderEmbOfFin_mem _ _ _)
  simp [Matrix.submatrix_apply, hi, hj]

/-! ## 3.16. A determinánsok szorzástétele -/

/-- **3.16. A determinánsok szorzástétele.** Tetszőleges azonos méretű `A`, `B` négyzetes
mátrixokra `|AB| = |A|·|B|`.

*Bizonyítás (a jegyzet szerint).* Tekintjük azt a `2n`-edrendű `D` determinánst, melynek
bal felső blokkja `A`, jobb alsó blokkja `B`, bal alsó blokkja `-E`, jobb felső blokkja
pedig a nullmátrix. `D`-t az első `n` sora szerint kifejtve (Laplace-tétel) `D = |A|·|B|`
adódik; ha viszont az `n+j`-edik oszlophoz hozzáadjuk az első `n` oszlop
`b_{1j},…,b_{nj}`-szeresét, akkor a jobb felső blokkban `AB` jelenik meg, és az első `n`
sor szerinti kifejtésből `D = |AB|` következik. -/
theorem det_szorzat (A B : Matrix (Fin n) (Fin n) T) :
    det' (A * B) = det' A * det' B := by
  rw [det'_eq_det, det'_eq_det, det'_eq_det, Matrix.det_mul]

end Ch03
end SzaboLinAlg
