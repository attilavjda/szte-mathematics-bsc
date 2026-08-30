import LinearisAlgebra.Ch16_ValosKvadratikus

/-!
# Szabó László: Bevezetés a lineáris algebrába — 16. fejezet (folytatás): főminorok

A jegyzet 16. fejezetének záró része (80. oldal):

* **16.7. Definíció** — egy valós `A = (aᵢⱼ)ₙₓₙ` mátrix *főminorai* az első `k` sor és az
  első `k` oszlop metszetében álló elemekből képezett determinánsok, `1 ≤ k ≤ n`
  (`foMinor`),
* **16.8. Tétel** — egy valós kvadratikus alak akkor és csak akkor pozitív definit, ha
  a (valamely bázisbeli) `A` mátrixának minden főminora pozitív
  (`pozitivDefinit_iff_foMinorok_pozitivak`).

A jegyzet a 16.8. Tételt bizonyítás nélkül közli. Az itt szereplő bizonyítás a szokásos
**Sylvester-kritérium**:

* (⇒) ha az alak pozitív definit, akkor bármely `k` esetén az első `k` koordinátára
  szorítkozva ismét pozitív definit alakot kapunk, melynek mátrixa az `A` mátrix bal felső
  `k × k`-as blokkja; pozitív definit mátrix determinánsa pedig pozitív;
* (⇐) `n` szerinti indukció: az első `n` sor és oszlop alkotta `A'` blokk az indukciós
  feltevés szerint pozitív definit, ezért invertálható, és a
  `|A| = |A'| · |c − bᵀA'⁻¹b|` (Schur-féle) felbontás miatt a `c − bᵀA'⁻¹b` Schur-komplemens
  determinánsa pozitív; innen a blokkmátrixokra vonatkozó kritériummal `A` pozitív
  szemidefinit, `|A| ≠ 0` miatt pedig pozitív definit.

A Lean-beli `Matrix.PosDef` fogalom és a jegyzet `PozitivDefinit` fogalma közötti hidat a
`posDef_iff_pozitivDefinit` lemma adja.
-/

namespace SzaboLinAlg
namespace Ch16

open scoped BigOperators
open SzaboLinAlg.Ch02 SzaboLinAlg.Ch03
open Matrix

variable {n : ℕ}

/-! ## 16.7. Definíció: főminorok -/

/-- **16.7. Definíció.** Az `A = (aᵢⱼ)ₙₓₙ` valós mátrix *főminorai* az

`|a₁₁ … a_{1k}; … ; a_{k1} … a_{kk}|`, `1 ≤ k ≤ n`

determinánsok. Itt a `k`-adik (azaz `k+1`-edrendű) főminort a `k : Fin n` index adja meg. -/
noncomputable def foMinor (A : Matrix' ℝ n n) (k : Fin n) : ℝ :=
  det' (A.submatrix (Fin.castLE k.isLt) (Fin.castLE k.isLt))

/-- Az `n`-edik (legnagyobb) főminor maga a determináns. -/
theorem foMinor_last (A : Matrix' ℝ (n + 1) (n + 1)) :
    foMinor A (Fin.last n) = det' A := by
  have hid : (Fin.castLE (Fin.last n).isLt : Fin (n + 1) → Fin (n + 1)) = id := by
    funext i; ext; rfl
  rw [foMinor, hid, Matrix.submatrix_id_id]

/-! ## Segédeszközök a Sylvester-kritériumhoz -/

/-- Pozitív definit mátrix injektív indexkiválasztással kapott részmátrixa is pozitív
definit. -/
theorem posDef_submatrix {m k : Type*} [Fintype m] [Fintype k] [DecidableEq m] [DecidableEq k]
    {A : Matrix k k ℝ} (hA : A.PosDef) {e : m → k} (he : Function.Injective e) :
    (A.submatrix e e).PosDef := by
  classical
  set E : Matrix k m ℝ := (1 : Matrix k k ℝ).submatrix id e with hE
  have hEmul : Function.Injective E.mulVec := by
    intro x y hxy
    funext i
    have h := congrFun hxy (e i)
    simpa [hE, Matrix.mulVec, dotProduct, Matrix.one_apply, he.eq_iff, eq_comm] using h
  have hmul : Eᴴ * A * E = A.submatrix e e := by
    ext i j
    simp [hE, Matrix.mul_apply, Matrix.one_apply, eq_comm]
  have := hA.conjTranspose_mul_mul_same hEmul
  rwa [hmul] at this

/-- Pozitív szemidefinit, nemelfajuló mátrix pozitív definit. -/
theorem posDef_of_posSemidef_of_det_ne_zero {k : Type*} [Fintype k] [DecidableEq k]
    {A : Matrix k k ℝ} (hA : A.PosSemidef) (hdet : A.det ≠ 0) : A.PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hA.1 fun x hx => ?_
  rcases lt_or_eq_of_le (hA.dotProduct_mulVec_nonneg x) with h | h
  · exact h
  · exact absurd (Matrix.eq_zero_of_mulVec_eq_zero hdet
      ((hA.dotProduct_mulVec_zero_iff x).1 h.symm)) hx

/-- Egyelemű mátrix pontosan akkor pozitív definit, ha egyetlen eleme pozitív. -/
theorem posDef_egyelemu {A : Matrix (Fin 1) (Fin 1) ℝ} (h : 0 < A 0 0) : A.PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos ?_ fun x hx => ?_
  · ext i j
    fin_cases i; fin_cases j; simp
  · have hx0 : x 0 ≠ 0 := fun h0 => hx (by funext i; fin_cases i; simpa using h0)
    have he : star x ⬝ᵥ A *ᵥ x = A 0 0 * (x 0 * x 0) := by
      simp [dotProduct, Matrix.mulVec]; ring
    rw [he]
    have : 0 < x 0 * x 0 := mul_self_pos.2 hx0
    positivity

/-- **A Sylvester-kritérium indukciós lépése.** Ha az `A` szimmetrikus mátrix bal felső
`n × n`-es blokkja pozitív definit, és `|A| > 0`, akkor `A` pozitív definit.

*Bizonyítás.* Írjuk `A`-t `[[A', b], [bᵀ, c]]` blokkalakba. Mivel `A'` pozitív definit,
`|A'| > 0`, tehát `A'` invertálható, és `|A| = |A'|·|c − bᵀA'⁻¹b|`, amiből a Schur-komplemens
determinánsa pozitív. Egyelemű mátrixról lévén szó, a Schur-komplemens pozitív definit,
így a blokkmátrixokra vonatkozó kritérium szerint `A` pozitív szemidefinit; `|A| ≠ 0` miatt
pedig pozitív definit. -/
theorem posDef_lepes (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) (hA : A.IsHermitian)
    (hA'pd : (A.submatrix Fin.castSucc Fin.castSucc).PosDef) (hdetA : 0 < A.det) :
    A.PosDef := by
  classical
  set A' : Matrix (Fin n) (Fin n) ℝ := A.submatrix Fin.castSucc Fin.castSucc with hA'def
  set b : Matrix (Fin n) (Fin 1) ℝ := fun i _ => A (Fin.castSucc i) (Fin.last n) with hbdef
  set c : Matrix (Fin 1) (Fin 1) ℝ := fun _ _ => A (Fin.last n) (Fin.last n) with hcdef
  set e : Fin n ⊕ Fin 1 ≃ Fin (n + 1) := finSumFinEquiv with hedef
  have hsym : ∀ i j, A i j = A j i := fun i j => by simpa using (hA.apply i j).symm
  have hnat : ∀ j : Fin 1, (Fin.natAdd n j : Fin (n + 1)) = Fin.last n := by
    intro j; ext; simp [Fin.last]
  have hcast : ∀ i : Fin n, (Fin.castAdd 1 i : Fin (n + 1)) = Fin.castSucc i := fun _ => rfl
  have hblock : A.submatrix e e = Matrix.fromBlocks A' b bᴴ c := by
    ext i j
    cases i with
    | inl i =>
        cases j with
        | inl j => rfl
        | inr j => simp [hbdef, hedef, Matrix.fromBlocks, hnat, hcast]
    | inr i =>
        cases j with
        | inl j => simp [hbdef, hedef, Matrix.fromBlocks, hnat, hcast, hsym]
        | inr j => simp [hcdef, hedef, Matrix.fromBlocks, hnat]
  have hdetA' : 0 < A'.det := hA'pd.det_pos
  haveI : Invertible A' := Matrix.invertibleOfIsUnitDet A' (isUnit_iff_ne_zero.2 hdetA'.ne')
  set S : Matrix (Fin 1) (Fin 1) ℝ := c - bᴴ * A'⁻¹ * b with hSdef
  have hdetM : (Matrix.fromBlocks A' b bᴴ c).det = A.det := by
    rw [← hblock, Matrix.det_submatrix_equiv_self]
  have hdetS : A'.det * S.det = A.det := by
    rw [← hdetM, Matrix.det_fromBlocks₁₁, Matrix.invOf_eq_nonsing_inv, hSdef]
  have hSpos : 0 < S.det := by
    rcases lt_trichotomy S.det 0 with h | h | h
    · nlinarith
    · rw [h, mul_zero] at hdetS; linarith
    · exact h
  have hSpd : S.PosDef := posDef_egyelemu (by rwa [Matrix.det_fin_one] at hSpos)
  have hMsd : (Matrix.fromBlocks A' b bᴴ c).PosSemidef :=
    (Matrix.PosDef.fromBlocks₁₁ b c hA'pd).2 hSpd.posSemidef
  have hMpd : (Matrix.fromBlocks A' b bᴴ c).PosDef :=
    posDef_of_posSemidef_of_det_ne_zero hMsd (by rw [hdetM]; exact hdetA.ne')
  rw [← hblock] at hMpd
  have hfin := posDef_submatrix hMpd (e := (e.symm : Fin (n + 1) → Fin n ⊕ Fin 1))
    e.symm.injective
  rwa [Matrix.submatrix_submatrix, Equiv.self_comp_symm, Matrix.submatrix_id_id] at hfin

/-- **A Sylvester-kritérium (⇐ irány), mátrixalakban.** Ha `A` szimmetrikus és minden
főminora pozitív, akkor `A` pozitív definit. -/
theorem posDef_of_foMinorok : ∀ (m : ℕ) (A : Matrix' ℝ m m), A.IsHermitian →
    (∀ k : Fin m, 0 < foMinor A k) → A.PosDef := by
  intro m
  induction m with
  | zero =>
      intro A hA _
      exact ⟨hA, fun x hx => absurd (by ext i; exact i.elim0) hx⟩
  | succ m ih =>
      intro A hA hmin
      set A' : Matrix (Fin m) (Fin m) ℝ := A.submatrix Fin.castSucc Fin.castSucc with hA'def
      have hA'herm : A'.IsHermitian := hA.submatrix _
      have hA'min : ∀ k : Fin m, 0 < foMinor A' k := by
        intro k
        have hcomp : (Fin.castSucc ∘ Fin.castLE k.isLt : Fin (k + 1) → Fin (m + 1))
            = Fin.castLE k.castSucc.isLt := by
          funext i; ext; rfl
        have hsub : A'.submatrix (Fin.castLE k.isLt) (Fin.castLE k.isLt)
            = A.submatrix (Fin.castLE k.castSucc.isLt) (Fin.castLE k.castSucc.isLt) := by
          rw [hA'def, Matrix.submatrix_submatrix, hcomp]
        rw [foMinor, hsub]
        exact hmin k.castSucc
      have hA'pd : A'.PosDef := ih A' hA'herm hA'min
      have hdetA : 0 < A.det := by
        have h := hmin (Fin.last m)
        rwa [foMinor_last, det'_eq_det] at h
      exact posDef_lepes A hA hA'pd hdetA

/-- **A Sylvester-kritérium (⇒ irány), mátrixalakban.** Pozitív definit mátrix minden
főminora pozitív. -/
theorem foMinorok_of_posDef {A : Matrix' ℝ n n} (hA : A.PosDef) (k : Fin n) :
    0 < foMinor A k := by
  have hinj : Function.Injective (Fin.castLE k.isLt : Fin (k + 1) → Fin n) :=
    fun i j hij => by ext; simpa [Fin.castLE] using congrArg Fin.val hij
  rw [foMinor, det'_eq_det]
  exact (posDef_submatrix hA hinj).det_pos

/-! ## Híd a jegyzet fogalmaihoz -/

/-- A mátrixhoz tartozó kvadratikus alak a Mathlib jelölésével. -/
theorem kvadratikus_eq_dotProduct (A : Matrix' ℝ n n) (x : Fin n → ℝ) :
    (∑ i, ∑ j, x i * A i j * x j) = star x ⬝ᵥ A *ᵥ x := by
  simp [dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]

/-- A jegyzet **16.4. Definíciója** szerinti pozitív definitség ugyanaz, mint a mátrix
`Matrix.PosDef` tulajdonsága. -/
theorem posDef_iff_pozitivDefinit {A : Matrix' ℝ n n} (hA : Szimmetrikus A) :
    A.PosDef ↔ PozitivDefinit (fun x : Fin n → ℝ => ∑ i, ∑ j, x i * A i j * x j) := by
  rw [Matrix.posDef_iff_dotProduct_mulVec]
  constructor
  · rintro ⟨-, h⟩
    refine ⟨fun v => ?_, fun v hv => ?_⟩
    · rcases eq_or_ne v 0 with rfl | hne
      · simp
      · exact le_of_lt (by show 0 < ∑ i, ∑ j, v i * A i j * v j
                           rw [kvadratikus_eq_dotProduct]; exact h hne)
    · by_contra hv0
      have hpos := h hv0
      rw [← kvadratikus_eq_dotProduct] at hpos
      simp only at hv
      linarith
  · rintro ⟨h1, h2⟩
    refine ⟨Matrix.isHermitian_iff_isSelfAdjoint.2 hA, fun x hx => ?_⟩
    rw [← kvadratikus_eq_dotProduct]
    rcases lt_or_eq_of_le (h1 x) with h | h
    · exact h
    · exact absurd (h2 x h.symm) hx

/-! ## 16.8. Tétel -/

/-- **16.8. Tétel.** Legyen `A` egy valós kvadratikus alak mátrixa valamely bázisban.
A kvadratikus alak akkor és csak akkor pozitív definit, ha az `A` mátrix minden főminora
pozitív.

(A jegyzet a tételt bizonyítás nélkül közli; a bizonyítás a Sylvester-kritérium, lásd a
modul bevezetőjét.) -/
theorem pozitivDefinit_iff_foMinorok_pozitivak {A : Matrix' ℝ n n} (hA : Szimmetrikus A) :
    PozitivDefinit (fun x : Fin n → ℝ => ∑ i, ∑ j, x i * A i j * x j)
      ↔ ∀ k : Fin n, 0 < foMinor A k := by
  rw [← posDef_iff_pozitivDefinit hA]
  exact ⟨fun h k => foMinorok_of_posDef h k,
    fun h => posDef_of_foMinorok n A (Matrix.isHermitian_iff_isSelfAdjoint.2 hA) h⟩

end Ch16
end SzaboLinAlg
