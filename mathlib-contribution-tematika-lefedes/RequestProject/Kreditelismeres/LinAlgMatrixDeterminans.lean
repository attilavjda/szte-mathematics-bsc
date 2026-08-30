/-
# Lineáris algebra I — kreditelismerési bizonyítéktár, 2. rész

A `LineárisalgebraI.-7.pdf` (MBLK15E) tematikájának **második fele**:

* homogén és nem-homogén lineáris egyenletrendszerek, elemi átalakítások,
  Gauss-elimináció, az általános megoldás szerkezete;
* mátrixműveletek és algebrai szabályaik, kapcsolat az egyenletrendszerekkel;
* mátrixegyenletek, mátrixok inverze, blokkmátrixok;
* determinánsok: kifejtés, elemi átalakítások, szorzástétel, nemelfajuló mátrixok,
  Cramer-szabály;
* lineáris függőség/függetlenség, vektorrendszer rangja, sor-, oszlop- és
  determinánsrang, rangszámtétel, Kronecker–Capelli-tétel.
-/
import Mathlib

namespace SZTE.Kredit.LinAlg

open Matrix Finset

/-! ## Lineáris egyenletrendszerek -/

/-- **Homogén egyenletrendszer megoldáshalmaza altér.** -/
theorem homogeneous_solutions_subspace {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    ∃ W : Submodule ℝ (Fin n → ℝ), (W : Set (Fin n → ℝ)) = {x | A.mulVec x = 0} := by
  refine ⟨LinearMap.ker A.mulVecLin, ?_⟩
  ext x
  simp [LinearMap.mem_ker]

/-- **Az általános megoldás szerkezete:** partikuláris megoldás + a homogén rendszer
megoldásai. -/
theorem general_solution {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    {x₀ : Fin n → ℝ} (hx₀ : A.mulVec x₀ = b) :
    {x | A.mulVec x = b} = {x | ∃ y, A.mulVec y = 0 ∧ x = x₀ + y} := by
  ext x
  simp only [Set.mem_setOf_eq]
  constructor
  · intro hx
    exact ⟨x - x₀, by rw [Matrix.mulVec_sub, hx, hx₀, sub_self], by abel⟩
  · rintro ⟨y, hy, rfl⟩
    rw [Matrix.mulVec_add, hx₀, hy, add_zero]

/-- **Elemi átalakítás I. (sorcsere)** nem változtatja meg a megoldáshalmazt. -/
theorem swap_rows_solutions {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (i j : Fin m) :
    {x | A.mulVec x = b} =
      {x | (A.submatrix (Equiv.swap i j) id).mulVec x = b ∘ (Equiv.swap i j)} := by
  have key : ∀ x : Fin n → ℝ, ∀ k,
      (A.submatrix (Equiv.swap i j) id).mulVec x k = A.mulVec x (Equiv.swap i j k) := by
    intro x k
    simp [Matrix.mulVec, Matrix.submatrix_apply]
  ext x
  simp only [Set.mem_setOf_eq, funext_iff, key, Function.comp_apply]
  constructor
  · intro h k
    exact h _
  · intro h k
    have := h (Equiv.swap i j k)
    simpa using this

/-- **Elemi átalakítás II. (sor szorzása nemnulla skalárral)** nem változtatja meg a
megoldáshalmazt. -/
theorem scale_row_solutions {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (i : Fin m) {c : ℝ} (hc : c ≠ 0) :
    {x | A.mulVec x = b} =
      {x | (Matrix.of fun k j => if k = i then c * A k j else A k j).mulVec x =
        fun k => if k = i then c * b k else b k} := by
  have key : ∀ (x : Fin n → ℝ) (k : Fin m),
      (Matrix.of fun k j => if k = i then c * A k j else A k j).mulVec x k =
        if k = i then c * A.mulVec x k else A.mulVec x k := by
    intro x k
    by_cases hk : k = i <;>
      simp [hk, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]
  ext x
  simp only [Set.mem_setOf_eq, funext_iff, key]
  refine forall_congr' fun k => ?_
  by_cases hk : k = i <;> simp [hk, mul_eq_mul_left_iff, hc]

/-- **Elemi átalakítás III. (egyik sor `c`-szeresének hozzáadása egy másikhoz)** nem
változtatja meg a megoldáshalmazt. -/
theorem add_row_solutions {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    {i j : Fin m} (hij : i ≠ j) (c : ℝ) :
    {x | A.mulVec x = b} =
      {x | (Matrix.of fun k l => if k = i then A i l + c * A j l else A k l).mulVec x =
        fun k => if k = i then b i + c * b j else b k} := by
  have key : ∀ (x : Fin n → ℝ) (k : Fin m),
      (Matrix.of fun k l => if k = i then A i l + c * A j l else A k l).mulVec x k =
        if k = i then A.mulVec x i + c * A.mulVec x j else A.mulVec x k := by
    intro x k
    by_cases hk : k = i <;>
      simp [hk, Matrix.mulVec, dotProduct, Finset.mul_sum, Finset.sum_add_distrib, add_mul,
        mul_assoc]
  ext x
  simp only [Set.mem_setOf_eq, funext_iff, key]
  constructor
  · intro h k
    by_cases hk : k = i <;> simp [hk, h]
  · intro h k
    have hj := h j
    simp only [if_neg (Ne.symm hij)] at hj
    have hi := h i
    simp [hj] at hi
    by_cases hk : k = i
    · rw [hk]; exact hi
    · have := h k
      simpa [hk] using this

/-- **Több ismeretlen, mint egyenlet:** ekkor a homogén rendszernek van nemtriviális
megoldása. -/
theorem exists_nontrivial_of_lt {m n : ℕ} (hmn : m < n) (A : Matrix (Fin m) (Fin n) ℝ) :
    ∃ x : Fin n → ℝ, x ≠ 0 ∧ A.mulVec x = 0 := by
  have hrank : A.rank ≤ m := by simpa using A.rank_le_card_height
  have hrk := LinearMap.finrank_range_add_finrank_ker A.mulVecLin
  have hn : Module.finrank ℝ (Fin n → ℝ) = n := by simp
  rw [hn] at hrk
  have hA : A.rank = Module.finrank ℝ (LinearMap.range A.mulVecLin) := rfl
  have hkerpos : 0 < Module.finrank ℝ (LinearMap.ker A.mulVecLin) := by omega
  have : Nontrivial (LinearMap.ker A.mulVecLin) := Module.finrank_pos_iff.mp hkerpos
  obtain ⟨x, hx⟩ := exists_ne (0 : LinearMap.ker A.mulVecLin)
  have hker : A.mulVecLin (x : Fin n → ℝ) = 0 := LinearMap.mem_ker.1 x.2
  exact ⟨(x : Fin n → ℝ), by simpa using hx, by rwa [Matrix.mulVecLin_apply] at hker⟩

/-! ## Mátrixműveletek -/

/-- A mátrixszorzás asszociatív és disztributív. -/
theorem matrix_algebra {m n p q : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (B C : Matrix (Fin n) (Fin p) ℝ) (D : Matrix (Fin p) (Fin q) ℝ) :
    (A * B) * D = A * (B * D) ∧ A * (B + C) = A * B + A * C :=
  ⟨Matrix.mul_assoc A B D, Matrix.mul_add A B C⟩

/-- A transzponálás megfordítja a szorzás sorrendjét. -/
theorem transpose_mul_eq {m n p : ℕ} (A : Matrix (Fin m) (Fin n) ℝ)
    (B : Matrix (Fin n) (Fin p) ℝ) : (A * B)ᵀ = Bᵀ * Aᵀ :=
  Matrix.transpose_mul A B

/-- **Az inverz egyértelmű.** -/
theorem inverse_unique {n : ℕ} (A B C : Matrix (Fin n) (Fin n) ℝ) (hB : A * B = 1 ∧ B * A = 1)
    (hC : A * C = 1 ∧ C * A = 1) : B = C := by
  calc B = B * (A * C) := by rw [hC.1, Matrix.mul_one]
    _ = (B * A) * C := (Matrix.mul_assoc _ _ _).symm
    _ = C := by rw [hB.2, Matrix.one_mul]

/-- **Szorzat inverze.** -/
theorem inverse_mul {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det)
    (hB : IsUnit B.det) : (A * B)⁻¹ = B⁻¹ * A⁻¹ := by
  refine Matrix.inv_eq_right_inv ?_
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc B, Matrix.mul_nonsing_inv _ hB, Matrix.one_mul,
    Matrix.mul_nonsing_inv _ hA]

/-- **Mátrixegyenlet.** Ha `A` invertálható, akkor `A * X = B` egyértelműen megoldható. -/
theorem matrix_equation_unique {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) (hA : IsUnit A.det) :
    ∃! X : Matrix (Fin n) (Fin n) ℝ, A * X = B := by
  refine ⟨A⁻¹ * B, ?_, ?_⟩
  · show A * (A⁻¹ * B) = B
    rw [← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hA, Matrix.one_mul]
  · rintro X rfl
    rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hA, Matrix.one_mul]

/-- **Blokkmátrixok szorzása** (2×2-es blokkfelbontás esetén). -/
theorem block_mul_eq {n₁ n₂ m₁ m₂ p₁ p₂ : ℕ}
    (A₁₁ : Matrix (Fin n₁) (Fin m₁) ℝ) (A₁₂ : Matrix (Fin n₁) (Fin m₂) ℝ)
    (A₂₁ : Matrix (Fin n₂) (Fin m₁) ℝ) (A₂₂ : Matrix (Fin n₂) (Fin m₂) ℝ)
    (B₁₁ : Matrix (Fin m₁) (Fin p₁) ℝ) (B₁₂ : Matrix (Fin m₁) (Fin p₂) ℝ)
    (B₂₁ : Matrix (Fin m₂) (Fin p₁) ℝ) (B₂₂ : Matrix (Fin m₂) (Fin p₂) ℝ) :
    (Matrix.fromBlocks A₁₁ A₁₂ A₂₁ A₂₂) * (Matrix.fromBlocks B₁₁ B₁₂ B₂₁ B₂₂) =
      Matrix.fromBlocks (A₁₁ * B₁₁ + A₁₂ * B₂₁) (A₁₁ * B₁₂ + A₁₂ * B₂₂)
        (A₂₁ * B₁₁ + A₂₂ * B₂₁) (A₂₁ * B₁₂ + A₂₂ * B₂₂) :=
  Matrix.fromBlocks_multiply _ _ _ _ _ _ _ _

/-! ## Determinánsok -/

/-- **Kifejtési tétel** az első sor szerint. -/
theorem det_expand_row_zero {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ) :
    A.det = ∑ j : Fin (n + 1), (-1) ^ (j : ℕ) * A 0 j *
      (A.submatrix Fin.succ j.succAbove).det :=
  Matrix.det_succ_row_zero A

/-- **Determinánsok szorzástétele.** -/
theorem det_mul' {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) : (A * B).det = A.det * B.det :=
  Matrix.det_mul A B

/-- A determináns értéke nem változik a transzponálástól. -/
theorem det_transpose' {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Aᵀ.det = A.det :=
  Matrix.det_transpose A

/-- Felső háromszögmátrix determinánsa a főátló elemeinek szorzata. -/
theorem det_upper_triangular {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ)
    (h : ∀ i j, j < i → A i j = 0) : A.det = ∏ i, A i i :=
  Matrix.det_of_upperTriangular h

/-- **Nemelfajuló mátrixok.** `A` pontosan akkor invertálható, ha a determinánsa nem nulla. -/
theorem invertible_iff_det_ne_zero {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) :
    (∃ B, A * B = 1 ∧ B * A = 1) ↔ A.det ≠ 0 := by
  constructor
  · rintro ⟨B, h1, -⟩ hd
    have h := Matrix.det_mul A B
    rw [h1, hd] at h
    simp at h
  · intro h
    exact ⟨A⁻¹, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 h),
      Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 h)⟩

/-- **Cramer-szabály** tetszőleges `n`-re: ha `det A ≠ 0`, akkor az `A x = b` rendszer
egyértelmű megoldásának `i`-edik koordinátája `det Aᵢ / det A`, ahol `Aᵢ` az `A` mátrix
`i`-edik oszlopának `b`-re cserélésével keletkezik. -/
theorem cramer_rule {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ) (hA : A.det ≠ 0)
    (x : Fin n → ℝ) (hx : A.mulVec x = b) (i : Fin n) :
    x i = (A.updateCol i b).det / A.det := by
  have hinj : Function.Injective A.mulVec :=
    Matrix.mulVec_injective_iff_isUnit.2
      ((Matrix.isUnit_iff_isUnit_det A).2 (isUnit_iff_ne_zero.2 hA))
  have hsm : A.det • x = A.cramer b := by
    apply hinj
    rw [Matrix.mulVec_smul, hx, Matrix.mulVec_cramer]
  have h := congrFun hsm i
  rw [eq_div_iff hA, mul_comm]
  simpa [Matrix.cramer_apply] using h

/-! ## Lineáris függetlenség és rang -/

/-- Lineárisan független vektorrendszer elemeinek száma legfeljebb `n` a valós
elem-`n`-esek terében. -/
theorem card_le_of_linearIndependent {n m : ℕ} (v : Fin m → (Fin n → ℝ))
    (hv : LinearIndependent ℝ v) : m ≤ n := by
  simpa using hv.fintype_card_le_finrank

/-- **Rangszámtétel (sorrang = oszloprang).** -/
theorem row_rank_eq_col_rank {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : Aᵀ.rank = A.rank :=
  Matrix.rank_transpose A

/-- A rang legfeljebb a sorok, illetve az oszlopok száma. -/
theorem rank_le_min {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) : A.rank ≤ min m n := by
  simp only [le_min_iff]
  exact ⟨by simpa using A.rank_le_card_height, by simpa using A.rank_le_card_width⟩

/-- **Dimenziótétel** (rang–nullitás) mátrixokra. -/
theorem rank_nullity_matrix {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    A.rank + Module.finrank ℝ (LinearMap.ker A.mulVecLin) = n := by
  simpa [Matrix.rank, add_comm] using LinearMap.finrank_range_add_finrank_ker A.mulVecLin

/-- A bővített (kiegészített) együtthatómátrix `[A | b]`. -/
def augment {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    Matrix (Fin m) (Fin (n + 1)) ℝ :=
  Matrix.of fun i j => Fin.lastCases (b i) (fun j' => A i j') j

/-- A bővített mátrixszal való szorzás: az első `n` koordináta `A`-ra, az utolsó `b`-re hat. -/
theorem augment_mulVec {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ)
    (y : Fin (n + 1) → ℝ) :
    (augment A b).mulVec y = A.mulVec (fun j => y j.castSucc) + y (Fin.last n) • b := by
  funext i
  simp only [Matrix.mulVec, dotProduct, augment, Matrix.of_apply, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]
  rw [Fin.sum_univ_castSucc]
  simp [Fin.lastCases_castSucc, mul_comm]

/-- A bővített mátrix oszlopterét az `A` oszloptere és `b` együtt feszíti ki. -/
theorem range_augment {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    LinearMap.range (augment A b).mulVecLin =
      LinearMap.range A.mulVecLin ⊔ Submodule.span ℝ {b} := by
  apply le_antisymm
  · rintro _ ⟨y, rfl⟩
    rw [Matrix.mulVecLin_apply, augment_mulVec]
    exact Submodule.add_mem _
      (Submodule.mem_sup_left ⟨_, rfl⟩)
      (Submodule.mem_sup_right (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self b)))
  · refine sup_le ?_ ?_
    · rintro _ ⟨x, rfl⟩
      refine ⟨Fin.snoc x 0, ?_⟩
      rw [Matrix.mulVecLin_apply, augment_mulVec]
      simp [Fin.snoc_castSucc]
    · rw [Submodule.span_le, Set.singleton_subset_iff]
      refine ⟨(Fin.snoc (0 : Fin n → ℝ) (1 : ℝ) : Fin (n + 1) → ℝ), ?_⟩
      rw [Matrix.mulVecLin_apply, augment_mulVec]
      have h0 : (fun j : Fin n => (Fin.snoc (0 : Fin n → ℝ) (1 : ℝ) : Fin (n + 1) → ℝ) j.castSucc)
          = 0 := by
        funext j; simp
      rw [h0]
      simp

/-- **Kronecker–Capelli-tétel.** Az `A x = b` egyenletrendszer pontosan akkor oldható meg,
ha az együtthatómátrix és a bővített mátrix rangja megegyezik. -/
theorem kronecker_capelli {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    (∃ x : Fin n → ℝ, A.mulVec x = b) ↔ (augment A b).rank = A.rank := by
  have hle : LinearMap.range A.mulVecLin ≤ LinearMap.range (augment A b).mulVecLin := by
    rw [range_augment]; exact le_sup_left
  constructor
  · rintro ⟨x, rfl⟩
    have hb : (A.mulVec x) ∈ LinearMap.range A.mulVecLin := ⟨x, rfl⟩
    have hrange : LinearMap.range (augment A (A.mulVec x)).mulVecLin
        = LinearMap.range A.mulVecLin := by
      rw [range_augment, sup_eq_left, Submodule.span_le, Set.singleton_subset_iff]
      exact hb
    show Module.finrank ℝ (LinearMap.range (augment A (A.mulVec x)).mulVecLin) = _
    rw [hrange]
    rfl
  · intro hrank
    have heq : LinearMap.range (augment A b).mulVecLin = LinearMap.range A.mulVecLin :=
      (Submodule.eq_of_le_of_finrank_le hle (le_of_eq hrank)).symm
    have hb : b ∈ LinearMap.range (augment A b).mulVecLin := by
      rw [range_augment]
      exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self b)
    rw [heq] at hb
    obtain ⟨x, hx⟩ := hb
    exact ⟨x, by rwa [Matrix.mulVecLin_apply] at hx⟩

/-- Ha `det A ≠ 0`, akkor a rendszer egyértelműen megoldható (a Kronecker–Capelli-tétel
speciális esete). -/
theorem unique_solution_of_det_ne_zero {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (b : Fin n → ℝ)
    (hA : A.det ≠ 0) : ∃! x : Fin n → ℝ, A.mulVec x = b := by
  refine ⟨A⁻¹.mulVec b, ?_, ?_⟩
  · show A *ᵥ (A⁻¹ *ᵥ b) = b
    rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.2 hA),
      Matrix.one_mulVec]
  · rintro x rfl
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.2 hA),
      Matrix.one_mulVec]

end SZTE.Kredit.LinAlg
