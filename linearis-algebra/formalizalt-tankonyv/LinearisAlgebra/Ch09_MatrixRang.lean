import LinearisAlgebra.Ch08_VegesDimenzios

/-!
# Szabó László: Bevezetés a lineáris algebrába — 9. fejezet: Mátrixok rangja

A jegyzet 9. fejezetének (47–52. oldal) formalizálása:

* **9.1. Definíció** — oszloprang és sorrang (a vektorrendszer rangja: az általa generált
  altér dimenziója),
* **9.2. Mátrixok rangszámtétele** — `r_o(A) = r_s(A)` (a determinánsrangra vonatkozó rész
  a jegyzet 8.12. Következményére épül, annak formalizálása még hátravan),
* **9.3. Definíció** — a mátrix rangja,
* **9.4., 9.5. Következmény** — `|A| ≠ 0` ⟺ az oszlopvektorok lineárisan függetlenek ⟺ a
  sorvektorok lineárisan függetlenek (és a tagadásaik),
* **9.6. Tétel** — `r(AB) ≤ r(A), r(B)`; invertálható tényező esetén egyenlőség; hasonló
  mátrixok rangja megegyezik,
* **9.7. Kronecker–Capelli-tétel** — az `Ax = b` egyenletrendszer pontosan akkor
  oldható meg, ha `r(A) = r(A|b)`.
-/

namespace SzaboLinAlg
namespace Ch09

open scoped BigOperators
open Matrix SzaboLinAlg.Ch02 SzaboLinAlg.Ch03 SzaboLinAlg.Ch04 SzaboLinAlg.Ch05

variable {T : Type*} [Field T] {m n p : ℕ}

/-! ## 9.1. Definíció: oszloprang, sorrang -/

/-- Az `A` mátrix oszlopvektorainak rendszere (a `Tᵐ` vektortér elemeiként). -/
def oszlopRendszer (A : Matrix' T m n) : Fin n → (Fin m → T) := fun j i => A i j

/-- Az `A` mátrix sorvektorainak rendszere (a `Tⁿ` vektortér elemeiként). -/
def sorRendszer (A : Matrix' T m n) : Fin m → (Fin n → T) := fun i j => A i j

/-- **9.1. Definíció.** Az `A` mátrix *oszloprangja*: oszlopvektorai rendszerének rangja,
azaz az általuk generált altér dimenziója. -/
noncomputable def oszlopRang (A : Matrix' T m n) : ℕ :=
  Module.finrank T (Submodule.span T (Set.range (oszlopRendszer A)))

/-- **9.1. Definíció.** Az `A` mátrix *sorrangja*: sorvektorai rendszerének rangja. -/
noncomputable def sorRang (A : Matrix' T m n) : ℕ :=
  Module.finrank T (Submodule.span T (Set.range (sorRendszer A)))

omit [Field T] in
theorem oszlopRendszer_transpose (A : Matrix' T m n) :
    oszlopRendszer Aᵀ = sorRendszer A := rfl

omit [Field T] in
theorem sorRendszer_transpose (A : Matrix' T m n) :
    sorRendszer Aᵀ = oszlopRendszer A := rfl

theorem sorRang_eq_oszlopRang_transpose (A : Matrix' T m n) :
    sorRang A = oszlopRang Aᵀ := rfl

/-- Az oszloprang megegyezik a Mathlib `Matrix.rank` fogalmával. -/
theorem oszlopRang_eq_rank (A : Matrix' T m n) : oszlopRang A = A.rank := by
  rw [Matrix.rank_eq_finrank_span_cols]
  rfl

/-- **9.2. Mátrixok rangszámtétele (sorrang = oszloprang).**

*Bizonyítás.* Az `A` sorvektorainak rendszere ugyanaz, mint `Aᵀ` oszlopvektorainak
rendszere, ezért `r_s(A) = r_o(Aᵀ)`; a Mathlib `Matrix.rank_transpose` tétele szerint
pedig `r_o(Aᵀ) = r_o(A)`. -/
theorem rangszamtetel (A : Matrix' T m n) : sorRang A = oszlopRang A := by
  rw [sorRang_eq_oszlopRang_transpose, oszlopRang_eq_rank, oszlopRang_eq_rank,
    Matrix.rank_transpose]

/-! ## 9.3. Definíció: a mátrix rangja -/

/-- **9.3. Definíció.** A rangszámtétel szerint az oszloprang és a sorrang megegyezik; ezt
a közös értéket nevezzük az `A` mátrix *rangjának*. -/
noncomputable def rang (A : Matrix' T m n) : ℕ := oszlopRang A

theorem rang_eq_sorRang (A : Matrix' T m n) : rang A = sorRang A := (rangszamtetel A).symm

theorem rang_eq_rank (A : Matrix' T m n) : rang A = A.rank := oszlopRang_eq_rank A

/-! ## 9.4., 9.5. Következmény -/

/-- **9.4. Következmény.** Négyzetes mátrix esetén `|A| ≠ 0` ⟺ az oszlopvektorok
rendszere lineárisan független ⟺ a sorvektorok rendszere lineárisan független. -/
theorem det_ne_zero_tfae (A : Matrix' T n n) :
    List.TFAE [det' A ≠ 0, Ch07.LinFuggetlen T (oszlopRendszer A),
      Ch07.LinFuggetlen T (sorRendszer A)] := by
  have hdet : det' A = A.det := det'_eq_det A
  have hcol : Ch07.LinFuggetlen T (oszlopRendszer A) ↔ IsUnit A := by
    rw [Ch07.linFuggetlen_iff_linearIndependent]
    exact Matrix.linearIndependent_cols_iff_isUnit
  have hrow : Ch07.LinFuggetlen T (sorRendszer A) ↔ IsUnit A := by
    rw [Ch07.linFuggetlen_iff_linearIndependent]
    exact Matrix.linearIndependent_rows_iff_isUnit
  have hunit : det' A ≠ 0 ↔ IsUnit A := by
    rw [hdet, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  tfae_have 1 ↔ 2 := by rw [hunit, hcol]
  tfae_have 1 ↔ 3 := by rw [hunit, hrow]
  tfae_finish

/-- **9.5. Következmény.** A 9.4. Következmény állításainak tagadásai is ekvivalensek:
`|A| = 0` ⟺ az oszlopvektorok lineárisan függők ⟺ a sorvektorok lineárisan függők. -/
theorem det_eq_zero_tfae (A : Matrix' T n n) :
    List.TFAE [det' A = 0, Ch07.LinFuggo T (oszlopRendszer A),
      Ch07.LinFuggo T (sorRendszer A)] := by
  have h := det_ne_zero_tfae A
  have h12 := h.out 0 1
  have h13 := h.out 0 2
  tfae_have 1 ↔ 2 := by
    rw [Ch07.LinFuggo, ← h12, not_not]
  tfae_have 1 ↔ 3 := by
    rw [Ch07.LinFuggo, ← h13, not_not]
  tfae_finish

/-! ## 9.6. Tétel: a szorzat rangja -/

/-- **9.6. Tétel (első fele).** `r(AB) ≤ r(A)` és `r(AB) ≤ r(B)`.

*Bizonyítás.* `AB` oszlopvektorai az `A` oszlopvektorainak, sorvektorai pedig a `B`
sorvektorainak lineáris kombinációi, ezért a generált alterek szűkebbek. -/
theorem rang_mul_le (A : Matrix' T m n) (B : Matrix' T n p) :
    rang (A * B) ≤ rang A ∧ rang (A * B) ≤ rang B := by
  rw [rang_eq_rank, rang_eq_rank, rang_eq_rank]
  exact ⟨Matrix.rank_mul_le_left A B, Matrix.rank_mul_le_right A B⟩

/-- **9.6. Tétel (második fele).** Ha `A` invertálható, akkor `r(AB) = r(B)`. -/
theorem rang_mul_of_inverze_left {A : Matrix' T n n} {X : Matrix' T n n} (hX : Inverze A X)
    (B : Matrix' T n p) : rang (A * B) = rang B := by
  refine le_antisymm (rang_mul_le A B).2 ?_
  have hB : B = X * (A * B) := by
    rw [← Matrix.mul_assoc, hX.1, Matrix.one_mul]
  calc rang B = rang (X * (A * B)) := by rw [← hB]
    _ ≤ rang (A * B) := (rang_mul_le X (A * B)).2

/-- **9.6. Tétel (harmadik fele).** Ha `B` invertálható, akkor `r(AB) = r(A)`. -/
theorem rang_mul_of_inverze_right {B : Matrix' T n n} {X : Matrix' T n n} (hX : Inverze B X)
    (A : Matrix' T m n) : rang (A * B) = rang A := by
  refine le_antisymm (rang_mul_le A B).1 ?_
  have hA : A = (A * B) * X := by
    rw [Matrix.mul_assoc, hX.2, Matrix.mul_one]
  calc rang A = rang ((A * B) * X) := by rw [← hA]
    _ ≤ rang (A * B) := (rang_mul_le (A * B) X).1

/-- **9.6. Tétel (negyedik fele).** Hasonló mátrixok rangja megegyezik. -/
theorem rang_hasonlo {A B : Matrix' T n n} (h : Hasonlo A B) : rang A = rang B := by
  obtain ⟨X, Y, hXY, rfl⟩ := h
  rw [rang_mul_of_inverze_right hXY (Y * A), rang_mul_of_inverze_left ⟨hXY.2, hXY.1⟩ A]

/-! ## 9.7. Kronecker–Capelli-tétel -/

/-- Az `Ax = b` egyenletrendszer pontosan akkor oldható meg, ha `b` benne van az `A`
oszlopvektorai által generált altérben (vektoregyenlet-alak). -/
theorem megoldhato_iff_mem_span (A : Matrix' T m n) (b : Fin m → T) :
    Megoldhato A b ↔ b ∈ Submodule.span T (Set.range (oszlopRendszer A)) := by
  rw [Submodule.mem_span_range_iff_exists_fun]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    funext i
    have := hc i
    simpa [oszlopRendszer, mul_comm] using this
  · rintro ⟨c, hc⟩
    refine ⟨c, fun i => ?_⟩
    have := congrFun hc i
    simpa [oszlopRendszer, mul_comm] using this

/-- Az `A` mátrix `b` konstansvektorral vett *bővített mátrixa*, `(A|b)`. -/
def bovitett (A : Matrix' T m n) (b : Fin m → T) : Matrix' T m (n + 1) :=
  fun i => Fin.snoc (fun j' : Fin n => A i j') (b i)

omit [Field T] in
theorem oszlopRendszer_bovitett (A : Matrix' T m n) (b : Fin m → T) :
    oszlopRendszer (bovitett A b) = Fin.snoc (oszlopRendszer A) b := by
  funext j i
  refine Fin.lastCases ?_ (fun j' => ?_) j
  · simp [bovitett, oszlopRendszer]
  · simp [bovitett, oszlopRendszer]

omit [Field T] in
theorem range_oszlopRendszer_bovitett (A : Matrix' T m n) (b : Fin m → T) :
    Set.range (oszlopRendszer (bovitett A b)) = insert b (Set.range (oszlopRendszer A)) := by
  rw [oszlopRendszer_bovitett]
  ext x
  constructor
  · rintro ⟨j, rfl⟩
    refine Fin.lastCases ?_ (fun j' => ?_) j
    · simp
    · exact Or.inr ⟨j', by simp⟩
  · rintro (rfl | ⟨j, rfl⟩)
    · exact ⟨Fin.last n, by simp⟩
    · exact ⟨j.castSucc, by simp⟩

/-- **9.7. Kronecker–Capelli-tétel.** Az `Ax = b` lineáris egyenletrendszer akkor és csak
akkor oldható meg, ha `r(A) = r(A|b)`.

*Bizonyítás (a könyv szerint).* Az egyenletrendszer vektoregyenlet-alakja
`x₁a₁ + … + xₙaₙ = b`.  Ha van megoldás, akkor `[a₁,…,aₙ] = [a₁,…,aₙ,b]`, tehát a két
rang egyenlő.  Fordítva, ha a két rang egyenlő, akkor a két altér dimenziója egyenlő, és
mivel az egyik tartalmazza a másikat, egyenlők is; így `b ∈ [a₁,…,aₙ]`. -/
theorem kronecker_capelli (A : Matrix' T m n) (b : Fin m → T) :
    Megoldhato A b ↔ rang A = rang (bovitett A b) := by
  have hle : Submodule.span T (Set.range (oszlopRendszer A))
      ≤ Submodule.span T (Set.range (oszlopRendszer (bovitett A b))) := by
    refine Submodule.span_mono ?_
    rw [range_oszlopRendszer_bovitett]
    exact Set.subset_insert _ _
  constructor
  · intro hsol
    have hb : b ∈ Submodule.span T (Set.range (oszlopRendszer A)) :=
      (megoldhato_iff_mem_span A b).1 hsol
    have heq : Submodule.span T (Set.range (oszlopRendszer (bovitett A b)))
        = Submodule.span T (Set.range (oszlopRendszer A)) := by
      rw [range_oszlopRendszer_bovitett]
      exact Submodule.span_insert_eq_span hb
    rw [rang, rang, oszlopRang, oszlopRang, heq]
  · intro hrank
    have hfin : Module.finrank T (Submodule.span T (Set.range (oszlopRendszer (bovitett A b))))
        ≤ Module.finrank T (Submodule.span T (Set.range (oszlopRendszer A))) := by
      rw [← oszlopRang, ← oszlopRang, ← rang, ← rang, hrank]
    have heq := Submodule.eq_of_le_of_finrank_le hle hfin
    have hb : b ∈ Submodule.span T (Set.range (oszlopRendszer (bovitett A b))) := by
      refine Submodule.subset_span ?_
      rw [range_oszlopRendszer_bovitett]
      exact Set.mem_insert _ _
    rw [megoldhato_iff_mem_span]
    rw [← heq] at hb
    exact hb

end Ch09
end SzaboLinAlg
