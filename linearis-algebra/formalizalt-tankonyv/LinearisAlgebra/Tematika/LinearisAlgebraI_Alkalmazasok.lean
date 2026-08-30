import LinearisAlgebra.Tematika.LinearisAlgebraI

/-!
# Lineáris algebra I. (MBLK15E) — a tematika alkalmazási pontjai

Ez a modul a *Lineáris algebra I.* tantárgy tematikájának azon pontjait formalizálja,
amelyek a Szabó-jegyzet anyagán **túlmutató alkalmazások**, és ezért a
`Tematika/LinearisAlgebraI.lean` modulban még nem szerepeltek:

1. **Mátrixok megadása blokkokkal és számolás velük.**
2. **Mátrixok LU-faktorizációja** (a Gauss-elimináció mátrixos alakja).
3. **A Leontyev-mátrix** (nyílt input–output modell).
4. **A determináns mint előjeles térfogat.**
5. **Merőleges vetítés alkalmazása:** a háromszög nevezetes pontjai és az
   **Euler-vonal**.

A modul a `Tematika.LinearisAlgebraI` névtérben már bevezetett `belsoSzorzat`,
`Meroleges` és `hossz` fogalmakra épül.
-/

namespace Tematika.LinearisAlgebraI

open Matrix MeasureTheory
open scoped BigOperators

/-! ## 1. Mátrixok megadása blokkokkal

Egy mátrix `A = [[A₁₁, A₁₂], [A₂₁, A₂₂]]` blokkalakja a Mathlib `Matrix.fromBlocks`
konstrukciója. A blokkokkal ugyanúgy lehet számolni, mint az elemekkel: a blokkokra
bontott mátrixok szorzata blokkonként a szokásos „sor-oszlop” szabály szerint áll elő.
-/

/-- **Blokkszorzás.** Két, azonos módon blokkokra bontott mátrix szorzata blokkonként
a szokásos szorzási szabály szerint számolható. -/
theorem blokkszorzas {T : Type*} [CommRing T] {k l m p : ℕ}
    (A₁₁ : Matrix (Fin k) (Fin l) T) (A₁₂ : Matrix (Fin k) (Fin m) T)
    (A₂₁ : Matrix (Fin p) (Fin l) T) (A₂₂ : Matrix (Fin p) (Fin m) T)
    {l' m' : ℕ} (B₁₁ : Matrix (Fin l) (Fin l') T) (B₁₂ : Matrix (Fin l) (Fin m') T)
    (B₂₁ : Matrix (Fin m) (Fin l') T) (B₂₂ : Matrix (Fin m) (Fin m') T) :
    Matrix.fromBlocks A₁₁ A₁₂ A₂₁ A₂₂ * Matrix.fromBlocks B₁₁ B₁₂ B₂₁ B₂₂ =
      Matrix.fromBlocks (A₁₁ * B₁₁ + A₁₂ * B₂₁) (A₁₁ * B₁₂ + A₁₂ * B₂₂)
        (A₂₁ * B₁₁ + A₂₂ * B₂₁) (A₂₁ * B₁₂ + A₂₂ * B₂₂) :=
  Matrix.fromBlocks_multiply _ _ _ _ _ _ _ _

/-- **Blokk-háromszögmátrix determinánsa.** Ha a bal alsó blokk nulla, akkor a
determináns a két átlós blokk determinánsának szorzata. -/
theorem blokk_haromszog_det {T : Type*} [CommRing T] {k m : ℕ}
    (A : Matrix (Fin k) (Fin k) T) (B : Matrix (Fin k) (Fin m) T)
    (D : Matrix (Fin m) (Fin m) T) :
    (Matrix.fromBlocks A B 0 D).det = A.det * D.det :=
  Matrix.det_fromBlocks_zero₂₁ A B D

/-- **Blokk-diagonális mátrix determinánsa.** -/
theorem blokk_diagonalis_det {T : Type*} [CommRing T] {k m : ℕ}
    (A : Matrix (Fin k) (Fin k) T) (D : Matrix (Fin m) (Fin m) T) :
    (Matrix.fromBlocks A 0 0 D).det = A.det * D.det :=
  Matrix.det_fromBlocks_zero₂₁ A 0 D

/-! ## 2. LU-faktorizáció

A Gauss-elimináció mátrixos alakja: `A = L · U`, ahol `L` **alsó unitrianguláris**
(a főátlóban csupa 1-es, felette csupa 0), `U` pedig **felső trianguláris** mátrix.
-/

variable {n : ℕ}

/-- Alsó unitrianguláris mátrix: a főátló fölött csupa nulla, a főátlóban csupa `1`. -/
def AlsoUnitharomszog (L : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  L.BlockTriangular OrderDual.toDual ∧ ∀ i, L i i = 1

/-- Felső trianguláris mátrix: a főátló alatt csupa nulla. -/
def Felsoharomszog (U : Matrix (Fin n) (Fin n) ℝ) : Prop := U.BlockTriangular id

/-- **LU-faktorizáció:** `A = L · U` alsó unitrianguláris `L`-lel és felső
trianguláris `U`-val. -/
def LUFelbontas (A L U : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  AlsoUnitharomszog L ∧ Felsoharomszog U ∧ A = L * U

/-- Alsó unitrianguláris mátrix determinánsa `1`. -/
theorem det_alsoUnitharomszog {L : Matrix (Fin n) (Fin n) ℝ} (h : AlsoUnitharomszog L) :
    L.det = 1 := by
  rw [Matrix.det_of_lowerTriangular _ h.1]
  simp [h.2]

/-- LU-faktorizáció esetén `|A|` az `U` főátlóbeli elemeinek szorzata. -/
theorem det_LUFelbontas {A L U : Matrix (Fin n) (Fin n) ℝ} (h : LUFelbontas A L U) :
    A.det = ∏ i, U i i := by
  obtain ⟨hL, hU, hA⟩ := h
  rw [hA, Matrix.det_mul, det_alsoUnitharomszog hL, one_mul,
    Matrix.det_of_upperTriangular hU]

/-- **Az LU-faktorizáció haszna:** az `A · x = b` rendszer két háromszögrendszerre
bomlik: előbb `L · y = b` (előrehelyettesítés), majd `U · x = y` (visszahelyettesítés). -/
theorem lu_megoldas {A L U : Matrix (Fin n) (Fin n) ℝ} (h : LUFelbontas A L U)
    {b x y : Fin n → ℝ} (hy : L *ᵥ y = b) (hx : U *ᵥ x = y) : A *ᵥ x = b := by
  obtain ⟨-, -, hA⟩ := h
  rw [hA, ← Matrix.mulVec_mulVec, hx, hy]

/-- **Az LU-faktorizáció egyértelmű**, ha `A` nem elfajuló (determinánsa egység).

*Bizonyítás.* `L₂⁻¹L₁ = U₂U₁⁻¹` egyszerre alsó és felső trianguláris, tehát diagonális;
mivel `L₁ = L₂ · (L₂⁻¹L₁)` és mindkét `L` főátlója csupa `1`, a közös érték az
egységmátrix. -/
theorem lu_egyertelmu {A L₁ U₁ L₂ U₂ : Matrix (Fin n) (Fin n) ℝ}
    (h₁ : LUFelbontas A L₁ U₁) (h₂ : LUFelbontas A L₂ U₂) (hA : IsUnit A.det) :
    L₁ = L₂ ∧ U₁ = U₂ := by
  obtain ⟨hL₁, hU₁, hA₁⟩ := h₁
  obtain ⟨hL₂, hU₂, hA₂⟩ := h₂
  have hdet₁ : IsUnit U₁.det := by
    have hd : A.det = U₁.det := by
      rw [hA₁, Matrix.det_mul, det_alsoUnitharomszog hL₁, one_mul]
    rwa [hd] at hA
  letI iL₂ : Invertible L₂ :=
    Matrix.invertibleOfIsUnitDet L₂ (by rw [det_alsoUnitharomszog hL₂]; exact isUnit_one)
  letI iU₁ : Invertible U₁ := Matrix.invertibleOfIsUnitDet U₁ hdet₁
  have hL₂inv : L₂⁻¹ * L₂ = 1 :=
    Matrix.nonsing_inv_mul _ (by rw [det_alsoUnitharomszog hL₂]; exact isUnit_one)
  set P : Matrix (Fin n) (Fin n) ℝ := L₂⁻¹ * L₁ with hP
  have hPlow : P.BlockTriangular OrderDual.toDual :=
    (Matrix.blockTriangular_inv_of_blockTriangular hL₂.1).mul hL₁.1
  have h2 : P * U₁ = U₂ := by
    have h : L₂⁻¹ * (L₁ * U₁) = L₂⁻¹ * (L₂ * U₂) := by rw [← hA₁, ← hA₂]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hL₂inv, Matrix.one_mul] at h
    exact h
  have hPup : P.BlockTriangular id := by
    have hPU : P = U₂ * U₁⁻¹ := by
      calc P = P * U₁ * U₁⁻¹ := by
                rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hdet₁, Matrix.mul_one]
        _ = U₂ * U₁⁻¹ := by rw [h2]
    rw [hPU]
    exact hU₂.mul (Matrix.blockTriangular_inv_of_blockTriangular hU₁)
  have hPoff : ∀ i j, i ≠ j → P i j = 0 := by
    intro i j hij
    rcases lt_or_gt_of_ne hij with h | h
    · exact hPlow (by simpa using h)
    · exact hPup (by simpa using h)
  have hL₂P : L₂ * P = L₁ := by
    rw [hP, ← Matrix.mul_assoc,
      Matrix.mul_nonsing_inv _ (by rw [det_alsoUnitharomszog hL₂]; exact isUnit_one),
      Matrix.one_mul]
  have hPone : ∀ i, P i i = 1 := by
    intro i
    have hi := congrArg (fun M => M i i) hL₂P
    simp only [Matrix.mul_apply] at hi
    rw [Finset.sum_eq_single i] at hi
    · rw [hL₂.2 i, one_mul] at hi
      rw [hi, hL₁.2 i]
    · intro b _ hb
      rw [hPoff b i hb, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ i) h
  have hPeq : P = 1 := by
    ext i j
    by_cases h : i = j
    · subst h; simp [hPone i]
    · simp [hPoff i j h, Matrix.one_apply_ne h]
  have hLL : L₁ = L₂ := by rw [← hL₂P, hPeq, Matrix.mul_one]
  refine ⟨hLL, ?_⟩
  have heq : L₁ * U₁ = L₁ * U₂ := by rw [← hA₁, hA₂, hLL]
  letI iL₁ : Invertible L₁ :=
    Matrix.invertibleOfIsUnitDet L₁ (by rw [det_alsoUnitharomszog hL₁]; exact isUnit_one)
  exact Matrix.mul_right_injective_of_invertible L₁ heq

/-- Konkrét `2 × 2`-es LU-faktorizáció: `a ≠ 0` esetén
`[[a, b], [c, d]] = [[1, 0], [c/a, 1]] · [[a, b], [0, d - cb/a]]`. -/
theorem lu_ketszerketto {a b c d : ℝ} (ha : a ≠ 0) :
    LUFelbontas !![a, b; c, d] !![1, 0; c / a, 1] !![a, b; 0, d - c * b / a] := by
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro i j hij
    rw [OrderDual.toDual_lt_toDual] at hij
    fin_cases i <;> fin_cases j <;> simp_all
  · intro i; fin_cases i <;> simp
  · intro i j hij
    simp only [id] at hij
    fin_cases i <;> fin_cases j <;> simp_all
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_succ] <;> field_simp
    ring

/-! ## 3. A Leontyev-mátrix (nyílt input–output modell)

Ha `A` a technológiai (ráfordítási) mátrix, `x` a termelési vektor és `d` a végső
kereslet, akkor a modell egyenlete `x = A·x + d`, azaz `(E − A)·x = d`. Az `E − A`
mátrix a **Leontyev-mátrix**.
-/

/-- A Leontyev-mátrix: `E − A`. -/
def leontyevMatrix (A : Matrix (Fin n) (Fin n) ℝ) : Matrix (Fin n) (Fin n) ℝ := 1 - A

/-- A modell egyenlete: `x = A·x + d` pontosan akkor, ha `(E − A)·x = d`. -/
theorem leontyev_egyenlet (A : Matrix (Fin n) (Fin n) ℝ) (x d : Fin n → ℝ) :
    x = A *ᵥ x + d ↔ leontyevMatrix A *ᵥ x = d := by
  constructor
  · intro h
    rw [leontyevMatrix, Matrix.sub_mulVec, Matrix.one_mulVec]
    nth_rewrite 1 [h]
    abel
  · intro h
    rw [leontyevMatrix, Matrix.sub_mulVec, Matrix.one_mulVec] at h
    rw [← h]
    abel

/-- Ha a Leontyev-mátrix nem elfajuló, akkor a modellnek minden végső kereslethez
pontosan egy termelési vektor felel meg: `x = (E − A)⁻¹·d`. -/
theorem leontyev_megoldas {A : Matrix (Fin n) (Fin n) ℝ}
    (hA : IsUnit (leontyevMatrix A).det) (d : Fin n → ℝ) :
    ∃! x : Fin n → ℝ, x = A *ᵥ x + d := by
  refine ⟨(leontyevMatrix A)⁻¹ *ᵥ d, ?_, ?_⟩
  · show (leontyevMatrix A)⁻¹ *ᵥ d = A *ᵥ ((leontyevMatrix A)⁻¹ *ᵥ d) + d
    rw [leontyev_egyenlet, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hA,
      Matrix.one_mulVec]
  · intro y hy
    rw [leontyev_egyenlet] at hy
    rw [← hy, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hA, Matrix.one_mulVec]

/-! ## 4. A determináns mint előjeles térfogat

Az `M` mátrix oszlopvektorai által kifeszített paralelepipedon az egységkocka képe az
`x ↦ M·x` lineáris leképezésnél; térfogata `|det M|`.
-/

/-- **A determináns geometriai jelentése.** Az egységkocka `x ↦ M·x` képének térfogata
`|det M|`, azaz a determináns abszolút értéke az oszlopvektorok által kifeszített
paralelepipedon térfogata. -/
theorem determinans_terfogat (M : Matrix (Fin n) (Fin n) ℝ) :
    volume (Matrix.toLin' M '' Set.Icc 0 1) = ENNReal.ofReal |M.det| := by
  rw [Measure.addHaar_image_linearMap, LinearMap.det_toLin']
  simp [Real.volume_Icc_pi]

/-- Elfajuló (nulla determinánsú) mátrix képe nullmértékű: a paralelepipedon
„ellapul”. -/
theorem determinans_nulla_terfogat {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.det = 0) :
    volume (Matrix.toLin' M '' Set.Icc 0 1) = 0 := by
  rw [determinans_terfogat, hM]
  simp

/-! ## 5. A háromszög nevezetes pontjai és az Euler-vonal

A merőleges vetítés (a `belsoSzorzat` és a `Meroleges` fogalom) alkalmazása: egy
háromszög körülírt körének középpontja `O`, súlypontja `S` és magasságpontja `M`
egy egyenesre esik, és `M − O = 3(S − O)`.
-/

/-- A háromszög **súlypontja**: `S = (A + B + C)/3`. -/
noncomputable def sulypont (A B C : Fin n → ℝ) : Fin n → ℝ := (3 : ℝ)⁻¹ • (A + B + C)

/-- `O` a háromszög **körülírt körének középpontja**: a három csúcstól egyenlő
távolságra van. -/
def KorulirtKozeppont (O A B C : Fin n → ℝ) : Prop :=
  belsoSzorzat (A - O) (A - O) = belsoSzorzat (B - O) (B - O) ∧
    belsoSzorzat (B - O) (B - O) = belsoSzorzat (C - O) (C - O)

/-- `M` a háromszög **magasságpontja**: a csúcsokból induló magasságvonalak közös
pontja, azaz `M − A ⟂ B − C` és ciklikusan. -/
def Magassagpont (M A B C : Fin n → ℝ) : Prop :=
  Meroleges (M - A) (B - C) ∧ Meroleges (M - B) (C - A) ∧ Meroleges (M - C) (A - B)

/-- **A magasságpont képlete.** Ha `O` a körülírt kör középpontja, akkor
`M = A + B + C − 2O` a háromszög magasságpontja.

*Bizonyítás.* `(M − A)·(B − C) = (B + C − 2O)·(B − C) = |B − O|² − |C − O|² = 0`,
mert `O` egyenlő távol van `B`-től és `C`-től; a másik két magasságvonal ugyanígy. -/
theorem magassagpont_keplet {O A B C : Fin n → ℝ} (h : KorulirtKozeppont O A B C) :
    Magassagpont (A + B + C - (2 : ℝ) • O) A B C := by
  obtain ⟨hAB, hBC⟩ := h
  have key : ∀ X Y Z : Fin n → ℝ,
      belsoSzorzat (X + Y + Z - (2 : ℝ) • O - X) (Y - Z) =
        belsoSzorzat (Y - O) (Y - O) - belsoSzorzat (Z - O) (Z - O) := by
    intro X Y Z
    simp only [belsoSzorzat, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have e2 : A + B + C = B + C + A := by abel
  have e3 : A + B + C = C + A + B := by abel
  refine ⟨?_, ?_, ?_⟩
  · show belsoSzorzat _ _ = 0
    rw [key A B C, hBC, sub_self]
  · show belsoSzorzat _ _ = 0
    rw [e2, key B C A, ← hBC, ← hAB, sub_self]
  · show belsoSzorzat _ _ = 0
    rw [e3, key C A B, hAB, sub_self]

/-- **Euler-vonal.** A magasságpont, a súlypont és a körülírt kör középpontja egy
egyenesre esik: `M − O = 3(S − O)`, azaz a súlypont az `OM` szakaszt `1 : 2` arányban
osztja. -/
theorem euler_vonal (O A B C : Fin n → ℝ) :
    A + B + C - (2 : ℝ) • O - O = (3 : ℝ) • (sulypont A B C - O) := by
  simp only [sulypont]
  ext i
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Az Euler-vonal tétele a magasságpont fogalmával kimondva: ha `O` a körülírt kör
középpontja és `M` a `magassagpont_keplet` szerinti magasságpont, akkor `O`, a súlypont
és `M` kollineáris. -/
theorem euler_vonal_kollinearis {O A B C : Fin n → ℝ} (h : KorulirtKozeppont O A B C) :
    ∃ M : Fin n → ℝ, Magassagpont M A B C ∧ M - O = (3 : ℝ) • (sulypont A B C - O) :=
  ⟨A + B + C - (2 : ℝ) • O, magassagpont_keplet h, euler_vonal O A B C⟩

end Tematika.LinearisAlgebraI
