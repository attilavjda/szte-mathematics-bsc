import LinearisAlgebra.Ch16_ValosKvadratikus

/-!
# Szabó László: Bevezetés a lineáris algebrába — 17. fejezet

**Euklideszi terek** (a jegyzet 81–84. oldala).

* **17.1. Definíció** — belső szorzat, euklideszi tér, hossz (norma), távolság, normált
  vektor,
* **17.2. Példa** — az `ℝⁿ` tér a standard belső szorzattal,
* **17.3. Bunyakovszkij–Cauchy–Schwarz-egyenlőtlenség**,
* **17.4. Háromszög-egyenlőtlenség**,
* **17.5. Definíció** — két vektor szöge, merőlegesség, ortogonális és ortonormált
  vektorrendszer, ortogonális mátrix,
* **17.6. Tétel** — Gram–Schmidt-féle ortogonalizáció,
* **17.7. Megjegyzés** — ortogonális kezdőszelet esetén az ortogonalizáció az első
  vektorokat változatlanul hagyja,
* **17.8. Következmény** — ortonormált vektorrendszer ortonormált bázissá egészíthető
  ki; euklideszi térben van ortonormált bázis,
* **17.9. Definíció, 17.10. Tétel** — euklideszi terek izomorfiája, minden `n`-dimenziós
  euklideszi tér izomorf az `ℝⁿ` euklideszi térrel.

**Megjegyzés a megfogalmazásról.** A könyv az euklideszi teret *véges dimenziós* valós
vektortérként definiálja egy pozitív definit szimmetrikus bilineáris leképezéssel. Itt a
belső szorzat tulajdonságait a `BelsoSzorzat` predikátum fogja össze, a véges
dimenziósságot pedig ott tesszük fel, ahol a bizonyítás valóban használja.
-/

namespace SzaboLinAlg
namespace Ch17

open scoped BigOperators
open SzaboLinAlg.Ch02 SzaboLinAlg.Ch03 SzaboLinAlg.Ch04 SzaboLinAlg.Ch06 SzaboLinAlg.Ch07
  SzaboLinAlg.Ch08 SzaboLinAlg.Ch10 SzaboLinAlg.Ch12 SzaboLinAlg.Ch15
open Matrix

variable {V : Type*} [AddCommGroup V] [Module ℝ V] {n k : ℕ}

/-! ## 17.1. Definíció: belső szorzat, euklideszi tér -/

/-- **17.1. Definíció.** A `b : V × V → ℝ` leképezés *belső szorzat* a valós `V`
vektortéren, ha szimmetrikus bilineáris leképezés, és a hozzá tartozó kvadratikus alak
pozitív definit: `b u u ≥ 0` minden `u`-ra, és `b u u = 0`-ból `u = 0` következik.
A `V` vektortér a `b` belső szorzattal *euklideszi tér*. -/
def BelsoSzorzat (b : V → V → ℝ) : Prop :=
  SzimmetrikusBilinearis ℝ b ∧ (∀ u, 0 ≤ b u u) ∧ ∀ u, b u u = 0 → u = 0

/-- **17.1. Definíció.** Az `u` vektor *hossza* (normája) `‖u‖ = √(b u u)`. -/
noncomputable def hossz (b : V → V → ℝ) (u : V) : ℝ := Real.sqrt (b u u)

/-- **17.1. Definíció.** Az `u` és `v` vektorok *távolsága* `‖u − v‖`. -/
noncomputable def tavolsag (b : V → V → ℝ) (u v : V) : ℝ := hossz b (u - v)

/-- **17.1. Definíció.** Az `u` vektor *normált*, ha hossza `1`. -/
def Normalt (b : V → V → ℝ) (u : V) : Prop := hossz b u = 1

/-! ### A belső szorzat alaptulajdonságai -/

theorem BelsoSzorzat.bilin {b : V → V → ℝ} (hb : BelsoSzorzat b) :
    BilinearisLekepezes ℝ b := hb.1.1

theorem BelsoSzorzat.symm {b : V → V → ℝ} (hb : BelsoSzorzat b) (u v : V) :
    b u v = b v u := hb.1.2 u v

theorem BelsoSzorzat.nonneg {b : V → V → ℝ} (hb : BelsoSzorzat b) (u : V) :
    0 ≤ b u u := hb.2.1 u

theorem BelsoSzorzat.eq_zero {b : V → V → ℝ} (hb : BelsoSzorzat b) {u : V}
    (h : b u u = 0) : u = 0 := hb.2.2 u h

omit [AddCommGroup V] [Module ℝ V] in
theorem hossz_nonneg (b : V → V → ℝ) (u : V) : 0 ≤ hossz b u := Real.sqrt_nonneg _

/-- `‖u‖² = b u u`. -/
theorem hossz_sq {b : V → V → ℝ} (hb : BelsoSzorzat b) (u : V) :
    hossz b u ^ 2 = b u u := Real.sq_sqrt (hb.nonneg u)

/-- A hossz pontosan a nullvektoron `0`. -/
theorem hossz_eq_zero_iff {b : V → V → ℝ} (hb : BelsoSzorzat b) (u : V) :
    hossz b u = 0 ↔ u = 0 := by
  constructor
  · intro h
    refine hb.eq_zero ?_
    have := hossz_sq hb u
    rw [h] at this
    simpa using this.symm
  · rintro rfl
    simp [hossz, bilin_zero_left hb.bilin]

theorem hossz_pos {b : V → V → ℝ} (hb : BelsoSzorzat b) {u : V} (hu : u ≠ 0) :
    0 < hossz b u :=
  lt_of_le_of_ne (hossz_nonneg b u) (fun h => hu ((hossz_eq_zero_iff hb u).1 h.symm))

/-! ## 17.2. Példa: az `ℝⁿ` euklideszi tér -/

/-- **17.2. Példa.** Az `ℝⁿ` vektortér *standard belső szorzata* `⟨x,y⟩ = ∑ xᵢyᵢ`. -/
def standardBSZ (x y : Fin n → ℝ) : ℝ := ∑ i, x i * y i

/-- **17.2. Példa.** A standard belső szorzat valóban belső szorzat, tehát `ℝⁿ`
euklideszi tér. -/
theorem standardBSZ_belsoSzorzat : BelsoSzorzat (standardBSZ (n := n)) := by
  refine ⟨⟨⟨?_, ?_, ?_, ?_⟩, ?_⟩, ?_, ?_⟩
  · intro x y z; simp [standardBSZ, add_mul, Finset.sum_add_distrib]
  · intro x y z; simp [standardBSZ, mul_add, Finset.sum_add_distrib]
  · intro c x y; simp [standardBSZ, Finset.mul_sum, mul_assoc]
  · intro c x y
    simp only [standardBSZ, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  · intro x y; exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  · intro x; exact Finset.sum_nonneg fun i _ => mul_self_nonneg _
  · intro x hx
    funext i
    have h := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j (_ : j ∈ Finset.univ) => mul_self_nonneg (x j))).1 hx i (Finset.mem_univ i)
    simpa using mul_self_eq_zero.1 h

/-! ## 17.3. Bunyakovszkij–Cauchy–Schwarz-egyenlőtlenség -/

/-- Segédazonosság: `‖λu − v‖² = ‖u‖²λ² − 2⟨u,v⟩λ + ‖v‖²`. -/
theorem norm_sq_smul_sub {b : V → V → ℝ} (hb : BelsoSzorzat b) (l : ℝ) (u v : V) :
    b (l • u - v) (l • u - v) = b u u * l ^ 2 - 2 * b u v * l + b v v := by
  have hbl := hb.bilin
  have h1 : ∀ x y z : V, b (x - y) z = b x z - b y z := by
    intro x y z
    have := hbl.1 (x - y) y z
    simp at this
    linarith [this]
  have h2 : ∀ x y z : V, b x (y - z) = b x y - b x z := by
    intro x y z
    have := hbl.2.1 x (y - z) z
    simp at this
    linarith [this]
  rw [h1, h2, h2]
  simp only [hbl.2.2.1, hbl.2.2.2, hb.symm v u]
  ring

/-- **17.3. Bunyakovszkij–Cauchy–Schwarz-egyenlőtlenség.** Euklideszi tér tetszőleges
`u, v` vektora esetén `|⟨u,v⟩| ≤ ‖u‖·‖v‖`.

*Bizonyítás (a könyv szerint).* Ha `u = 0`, mindkét oldal nulla. Egyébként minden `λ`-ra
`0 ≤ ‖λu − v‖² = ‖u‖²λ² − 2⟨u,v⟩λ + ‖v‖²`, tehát a másodfokú polinom diszkriminánsa
nem pozitív: `4⟨u,v⟩² − 4‖u‖²‖v‖² ≤ 0`. -/
theorem bcs_egyenlotlenseg {b : V → V → ℝ} (hb : BelsoSzorzat b) (u v : V) :
    |b u v| ≤ hossz b u * hossz b v := by
  rcases eq_or_ne u 0 with rfl | hu
  · simp [hossz, bilin_zero_left hb.bilin]
  · have hupos : 0 < b u u := by
      have := hb.nonneg u
      rcases this.lt_or_eq with h | h
      · exact h
      · exact absurd (hb.eq_zero h.symm) hu
    -- a `λ = ⟨u,v⟩/‖u‖²` választással
    have hkey := hb.nonneg (( (b u v / b u u) • u - v))
    rw [norm_sq_smul_sub hb] at hkey
    have hsq : b u v ^ 2 ≤ b u u * b v v := by
      have h := hkey
      field_simp at h
      nlinarith [h, hupos]
    have h1 : |b u v| ^ 2 ≤ (hossz b u * hossz b v) ^ 2 := by
      rw [sq_abs, mul_pow, hossz_sq hb, hossz_sq hb]
      exact hsq
    nlinarith [abs_nonneg (b u v),
      mul_nonneg (hossz_nonneg b u) (hossz_nonneg b v), h1]

/-! ## 17.4. Háromszög-egyenlőtlenség -/

theorem hossz_add_sq {b : V → V → ℝ} (hb : BelsoSzorzat b) (u v : V) :
    b (u + v) (u + v) = b u u + 2 * b u v + b v v := by
  have hbl := hb.bilin
  rw [hbl.1, hbl.2.1, hbl.2.1, hb.symm v u]
  ring

/-- **17.4. Háromszög-egyenlőtlenség.** `‖u + v‖ ≤ ‖u‖ + ‖v‖`.

*Bizonyítás (a könyv szerint).* Négyzetre emelve az egyenlőtlenség a
`‖u‖² + 2⟨u,v⟩ + ‖v‖² ≤ ‖u‖² + ‖v‖² + 2‖u‖‖v‖` alakot ölti, ami a BCS-egyenlőtlenség
következménye. -/
theorem haromszog_egyenlotlenseg {b : V → V → ℝ} (hb : BelsoSzorzat b) (u v : V) :
    hossz b (u + v) ≤ hossz b u + hossz b v := by
  have hbcs : b u v ≤ hossz b u * hossz b v :=
    le_trans (le_abs_self _) (bcs_egyenlotlenseg hb u v)
  have h : hossz b (u + v) ^ 2 ≤ (hossz b u + hossz b v) ^ 2 := by
    rw [hossz_sq hb, hossz_add_sq hb, add_sq, hossz_sq hb, hossz_sq hb]
    linarith
  have hnn : 0 ≤ hossz b u + hossz b v := by
    exact add_nonneg (hossz_nonneg b u) (hossz_nonneg b v)
  nlinarith [hossz_nonneg b (u + v), h, hnn]

/-! ## 17.5. Definíció: szög, merőlegesség, ortogonális rendszer -/

/-- **17.5. Definíció.** Nemnulla `u`, `v` vektorok *szöge* az az egyetlen `α ∈ [0,π)`
szög, melyre `cos α = ⟨u,v⟩/(‖u‖‖v‖)`. (A hányados a BCS-egyenlőtlenség szerint a
`[−1,1]` intervallumba esik.) -/
noncomputable def szog (b : V → V → ℝ) (u v : V) : ℝ :=
  Real.arccos (b u v / (hossz b u * hossz b v))

/-- **17.5.** A BCS-egyenlőtlenség szerint a szög definíciójában szereplő hányados
`[−1,1]`-be esik, ezért a szög koszinusza valóban a hányados. -/
theorem cos_szog {b : V → V → ℝ} (hb : BelsoSzorzat b) {u v : V} (hu : u ≠ 0)
    (hv : v ≠ 0) : Real.cos (szog b u v) = b u v / (hossz b u * hossz b v) := by
  have hpos : 0 < hossz b u * hossz b v := mul_pos (hossz_pos hb hu) (hossz_pos hb hv)
  have habs : |b u v / (hossz b u * hossz b v)| ≤ 1 := by
    rw [abs_div, abs_of_pos hpos, div_le_one hpos]
    exact bcs_egyenlotlenseg hb u v
  exact Real.cos_arccos (abs_le.1 habs).1 (abs_le.1 habs).2

omit [AddCommGroup V] [Module ℝ V] in
/-- **17.5.** A szög a `[0,π]` intervallumba esik. -/
theorem szog_mem_Icc (b : V → V → ℝ) (u v : V) : szog b u v ∈ Set.Icc 0 Real.pi :=
  ⟨Real.arccos_nonneg _, Real.arccos_le_pi _⟩

/-- **17.5. Definíció.** Az `u` és `v` vektorok *merőlegesek* (ortogonálisak), ha
`⟨u,v⟩ = 0`. -/
def Meroleges (b : V → V → ℝ) (u v : V) : Prop := b u v = 0

/-- **17.5.** A nullvektor minden vektorra merőleges. -/
theorem meroleges_zero {b : V → V → ℝ} (hb : BelsoSzorzat b) (u : V) :
    Meroleges b 0 u := bilin_zero_left hb.bilin u

/-- **17.5. Definíció.** A `v₁,…,v_k` vektorrendszer *ortogonális*, ha bármely két
különböző tagja merőleges egymásra. -/
def OrtogonalisRendszer (b : V → V → ℝ) (v : Fin k → V) : Prop :=
  ∀ i j, i ≠ j → b (v i) (v j) = 0

/-- **17.5. Definíció.** A vektorrendszer *ortonormált*, ha ortogonális, és minden tagja
normált. -/
def OrtonormaltRendszer (b : V → V → ℝ) (v : Fin k → V) : Prop :=
  OrtogonalisRendszer b v ∧ ∀ i, hossz b (v i) = 1

/-- Ortonormált rendszer belső szorzatai: `⟨vᵢ,vⱼ⟩ = δᵢⱼ`. -/
theorem ortonormalt_apply {b : V → V → ℝ} (hb : BelsoSzorzat b) {v : Fin k → V}
    (hv : OrtonormaltRendszer b v) (i j : Fin k) :
    b (v i) (v j) = if i = j then 1 else 0 := by
  by_cases h : i = j
  · subst h
    have := hossz_sq hb (v i)
    rw [hv.2 i] at this
    simp [this.symm]
  · simp [h, hv.1 i j h]

/-- **17.5. Definíció.** Az `n × n`-es `A` mátrix *ortogonális*, ha sorvektorrendszere
ortonormált az `ℝⁿ` euklideszi térben. -/
def OrtogonalisMatrix (A : Matrix' ℝ n n) : Prop :=
  OrtonormaltRendszer standardBSZ (fun i => A i)

/-- **17.5.** Egy négyzetes mátrix pontosan akkor ortogonális, ha `AAᵀ = E`. -/
theorem ortogonalisMatrix_iff (A : Matrix' ℝ n n) :
    OrtogonalisMatrix A ↔ A * Aᵀ = 1 := by
  constructor
  · intro hA
    ext i j
    have h := ortonormalt_apply standardBSZ_belsoSzorzat hA i j
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply]
    simpa [standardBSZ] using h
  · intro hA
    have h : ∀ i j, standardBSZ (A i) (A j) = if i = j then 1 else 0 := by
      intro i j
      have := congrFun (congrFun hA i) j
      simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply] at this
      simpa [standardBSZ] using this
    refine ⟨fun i j hij => by simpa [hij] using h i j, fun i => ?_⟩
    have hii := h i i
    rw [hossz, hii]
    simp

/-- **17.5.** Ortogonális mátrix inverze a transzponáltja. -/
theorem ortogonalisMatrix_inverze {A : Matrix' ℝ n n} (hA : OrtogonalisMatrix A) :
    Inverze A Aᵀ := by
  have h := (ortogonalisMatrix_iff A).1 hA
  exact ⟨mul_eq_one_comm.1 h, h⟩

/-! ## Ortogonális rendszerek lineáris függetlensége -/

/-- Ortogonális, csupa nemnulla vektorból álló vektorrendszer lineárisan független.

*Bizonyítás (a könyv 17.8. bizonyításának gondolatmenete).* Ha `∑ λᵢvᵢ = 0`, akkor a
`vⱼ`-vel vett belső szorzat `λⱼ⟨vⱼ,vⱼ⟩ = 0`, és `⟨vⱼ,vⱼ⟩ ≠ 0` miatt `λⱼ = 0`. -/
theorem ortogonalis_linFuggetlen {b : V → V → ℝ} (hb : BelsoSzorzat b) {v : Fin k → V}
    (hv : OrtogonalisRendszer b v) (hne : ∀ i, v i ≠ 0) : LinFuggetlen ℝ v := by
  intro g hg j
  have h0 : b (∑ i, g i • v i) (v j) = 0 := by
    rw [hg]
    exact bilin_zero_left hb.bilin _
  have hsum : ∑ i, g i * b (v i) (v j) = 0 := by
    rw [← h0, bilin_sum_left hb.bilin]
    exact Finset.sum_congr rfl fun i _ => (hb.bilin.2.2.1 (g i) (v i) (v j)).symm
  have hsingle : g j * b (v j) (v j) = 0 := by
    rw [Finset.sum_eq_single j (fun i _ hij => by rw [hv i j hij, mul_zero])
      (fun h => absurd (Finset.mem_univ j) h)] at hsum
    exact hsum
  have hjj : b (v j) (v j) ≠ 0 := fun h => hne j (hb.eq_zero h)
  exact (mul_eq_zero.1 hsingle).resolve_right hjj

/-- Ortonormált vektorrendszer lineárisan független. -/
theorem ortonormalt_linFuggetlen {b : V → V → ℝ} (hb : BelsoSzorzat b) {v : Fin k → V}
    (hv : OrtonormaltRendszer b v) : LinFuggetlen ℝ v := by
  refine ortogonalis_linFuggetlen hb hv.1 fun i hi => ?_
  have := hv.2 i
  rw [hi, (hossz_eq_zero_iff hb 0).2 rfl] at this
  exact zero_ne_one this

/-! ## 17.6. Tétel: Gram–Schmidt-féle ortogonalizáció -/

/-- Bilineáris leképezés az első változójában additív a különbségre is. -/
theorem bilin_sub_left {b : V → V → ℝ} (hb : BilinearisLekepezes ℝ b) (x y z : V) :
    b (x - y) z = b x z - b y z := by
  have h := hb.1 (x - y) y z
  simp only [sub_add_cancel] at h
  linarith

/-- Bilineáris leképezés a második változójában additív a különbségre is. -/
theorem bilin_sub_right {b : V → V → ℝ} (hb : BilinearisLekepezes ℝ b) (x y z : V) :
    b x (y - z) = b x y - b x z := by
  have h := hb.2.1 x (y - z) z
  simp only [sub_add_cancel] at h
  linarith

/-- A hossz és a skalárszoros kapcsolata: `‖cu‖ = |c|·‖u‖`. -/
theorem hossz_smul {b : V → V → ℝ} (hb : BelsoSzorzat b) (c : ℝ) (u : V) :
    hossz b (c • u) = |c| * hossz b u := by
  rw [hossz, hossz, hb.bilin.2.2.1, hb.bilin.2.2.2, ← mul_assoc,
    show c * c = c ^ 2 by ring, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs]

/-- **17.6. Tétel — a Gram–Schmidt-féle ortogonalizáció konstrukciója.**
A könyv bizonyításában szereplő rekurzió: `v_m = u_m − ∑_{i<m} (⟨u_m,v_i⟩/⟨v_i,v_i⟩)v_i`.
(A vektorrendszert itt `ℕ`-nel indexeljük; a könyv véges vektorrendszerre vonatkozó
alakja ebből a `gram_schmidt_ortogonalizacio` tételben adódik.) -/
noncomputable def gs (b : V → V → ℝ) (u : ℕ → V) : ℕ → V
  | m => u m - ∑ i ∈ (Finset.range m).attach,
      (b (u m) (gs b u i.1) / b (gs b u i.1) (gs b u i.1)) • gs b u i.1
  decreasing_by exact Finset.mem_range.mp i.2

/-- A Gram–Schmidt-rekurzió kifejtett alakja. -/
theorem gs_def (b : V → V → ℝ) (u : ℕ → V) (m : ℕ) :
    gs b u m = u m - ∑ i ∈ Finset.range m,
      (b (u m) (gs b u i) / b (gs b u i) (gs b u i)) • gs b u i := by
  rw [gs]
  simp [Finset.sum_attach (Finset.range m)
    (fun i => (b (u m) (gs b u i) / b (gs b u i) (gs b u i)) • gs b u i)]

/-- **17.6.** Az ortogonalizáció során kapott `v_m` benne van az `u_0,…,u_m` vektorok
álta generált altérben. -/
theorem gs_mem_span (b : V → V → ℝ) (u : ℕ → V) (m : ℕ) :
    gs b u m ∈ Submodule.span ℝ (u '' Set.Iic m) := by
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    rw [gs_def]
    refine Submodule.sub_mem _ (Submodule.subset_span ⟨m, le_refl m, rfl⟩) ?_
    refine Submodule.sum_mem _ fun i hi => ?_
    have him : i < m := Finset.mem_range.mp hi
    refine Submodule.smul_mem _ _ ?_
    exact Submodule.span_mono (Set.image_mono (Set.Iic_subset_Iic.2 him.le)) (ih i him)

/-- **17.6.** Megfordítva: `u_m` benne van a `v_0,…,v_m` vektorok által generált
altérben. -/
theorem u_mem_span_gs (b : V → V → ℝ) (u : ℕ → V) (m : ℕ) :
    u m ∈ Submodule.span ℝ (gs b u '' Set.Iic m) := by
  have h : u m = gs b u m + ∑ i ∈ Finset.range m,
      (b (u m) (gs b u i) / b (gs b u i) (gs b u i)) • gs b u i := by
    rw [gs_def]; abel
  rw [h]
  refine Submodule.add_mem _ (Submodule.subset_span ⟨m, le_refl m, rfl⟩) ?_
  refine Submodule.sum_mem _ fun i hi => ?_
  exact Submodule.smul_mem _ _
    (Submodule.subset_span ⟨i, (Finset.mem_range.mp hi).le, rfl⟩)

/-- **17.6.** A kezdőszeletek által generált alterek megegyeznek:
`[u_0,…,u_m] = [v_0,…,v_m]`. -/
theorem span_gs_eq_span_u (b : V → V → ℝ) (u : ℕ → V) (m : ℕ) :
    Submodule.span ℝ (gs b u '' Set.Iic m) = Submodule.span ℝ (u '' Set.Iic m) := by
  refine le_antisymm ?_ ?_
  · rw [Submodule.span_le]
    rintro _ ⟨i, hi, rfl⟩
    exact Submodule.span_mono (Set.image_mono (Set.Iic_subset_Iic.2 hi)) (gs_mem_span b u i)
  · rw [Submodule.span_le]
    rintro _ ⟨i, hi, rfl⟩
    exact Submodule.span_mono (Set.image_mono (Set.Iic_subset_Iic.2 hi)) (u_mem_span_gs b u i)

/-- **17.6. Tétel (ortogonalitás).** Ha a `v_0,…,v_{m−1}` vektorok egyike sem nulla,
akkor páronként merőlegesek egymásra.

*Bizonyítás (a könyv szerint).* Teljes indukcióval: a `v_m` vektort
`v_m = u_m + ∑_{i<m} λᵢvᵢ` alakban keresve az ortogonalitási feltételből minden
`j < m`-re `λ_j = −⟨u_m,v_j⟩/⟨v_j,v_j⟩` adódik. -/
theorem gs_ortogonalis {b : V → V → ℝ} (hb : BelsoSzorzat b) (u : ℕ → V) :
    ∀ m : ℕ, (∀ i, i < m → gs b u i ≠ 0) →
      ∀ i j, i < m → j < m → i ≠ j → b (gs b u i) (gs b u j) = 0 := by
  intro m
  induction m with
  | zero => intro _ i j hi; exact absurd hi (Nat.not_lt_zero i)
  | succ m ih =>
    intro hne
    have ihm : ∀ i j, i < m → j < m → i ≠ j → b (gs b u i) (gs b u j) = 0 :=
      ih fun i hi => hne i (Nat.lt_succ_of_lt hi)
    have key : ∀ j, j < m → b (gs b u m) (gs b u j) = 0 := by
      intro j hj
      have hjj : b (gs b u j) (gs b u j) ≠ 0 := fun h =>
        hne j (Nat.lt_succ_of_lt hj) (hb.eq_zero h)
      have hsum : b (∑ i ∈ Finset.range m,
          (b (u m) (gs b u i) / b (gs b u i) (gs b u i)) • gs b u i) (gs b u j)
          = b (u m) (gs b u j) := by
        rw [bilin_sum_left hb.bilin]
        have hterm : ∀ i ∈ Finset.range m,
            b ((b (u m) (gs b u i) / b (gs b u i) (gs b u i)) • gs b u i) (gs b u j)
              = if i = j then b (u m) (gs b u j) else 0 := by
          intro i hi
          rw [hb.bilin.2.2.1]
          by_cases hij : i = j
          · subst hij
            rw [if_pos rfl, div_mul_cancel₀ _ hjj]
          · rw [if_neg hij, ihm i j (Finset.mem_range.mp hi) hj hij, mul_zero]
        rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' (Finset.range m) j
          (fun _ => b (u m) (gs b u j)), if_pos (Finset.mem_range.mpr hj)]
      rw [gs_def, bilin_sub_left hb.bilin, hsum, sub_self]
    intro i j hi hj hij
    rcases Nat.lt_succ_iff_lt_or_eq.mp hi with hi' | rfl
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | rfl
      · exact ihm i j hi' hj' hij
      · rw [hb.symm]
        exact key i hi'
    · rcases Nat.lt_succ_iff_lt_or_eq.mp hj with hj' | rfl
      · exact key j hj'
      · exact absurd rfl hij

/-! ### A 17.6. Tétel a könyv véges vektorrendszerre vonatkozó alakjában -/

/-- Véges vektorrendszer kiterjesztése `ℕ`-nel indexelt vektorrendszerré (a `k`-nál nem
kisebb indexeken a nullvektorral). -/
noncomputable def kiterjesztes {k : ℕ} (u : Fin k → V) : ℕ → V :=
  fun m => if h : m < k then u ⟨m, h⟩ else 0

omit [Module ℝ V] in
theorem kiterjesztes_apply {k : ℕ} (u : Fin k → V) (i : Fin k) :
    kiterjesztes u (i : ℕ) = u i := by
  simp [kiterjesztes, i.2]

omit [Module ℝ V] in
theorem kiterjesztes_image_Iic {k : ℕ} (u : Fin k → V) (i : Fin k) :
    kiterjesztes u '' Set.Iic (i : ℕ) = u '' {j : Fin k | j ≤ i} := by
  ext x
  constructor
  · rintro ⟨m, hm, rfl⟩
    have hmk : m < k := lt_of_le_of_lt hm i.2
    exact ⟨⟨m, hmk⟩, hm, by simp [kiterjesztes, hmk]⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨(j : ℕ), hj, kiterjesztes_apply u j⟩

omit [Module ℝ V] in
theorem kiterjesztes_image_Iio {k : ℕ} (u : Fin k → V) {m : ℕ} (hm : m < k) :
    kiterjesztes u '' Set.Iio m = u '' {j : Fin k | (j : ℕ) < m} := by
  ext x
  constructor
  · rintro ⟨l, hl, rfl⟩
    have hlk : l < k := lt_trans hl hm
    exact ⟨⟨l, hlk⟩, hl, by simp [kiterjesztes, hlk]⟩
  · rintro ⟨j, hj, rfl⟩
    exact ⟨(j : ℕ), hj, kiterjesztes_apply u j⟩

/-- Lineárisan független vektorrendszer egyik tagja sem áll elő a korábbiak lineáris
kombinációjaként. -/
theorem notMem_span_elozok {k : ℕ} {u : Fin k → V} (hu : LinFuggetlen ℝ u) {m : ℕ}
    (hm : m < k) :
    kiterjesztes u m ∉ Submodule.span ℝ (kiterjesztes u '' Set.Iio m) := by
  rw [kiterjesztes_image_Iio u hm]
  have hli : LinearIndependent ℝ u := (linFuggetlen_iff_linearIndependent u).1 hu
  have h := hli.notMem_span_image (s := {j : Fin k | (j : ℕ) < m}) (x := ⟨m, hm⟩)
    (by simp)
  simpa [kiterjesztes, hm] using h

/-- **17.6.** Ha a kiindulási vektorrendszer lineárisan független, akkor az
ortogonalizáció során kapott vektorok egyike sem nulla. -/
theorem gs_ne_zero {b : V → V → ℝ} {u : ℕ → V} {N : ℕ}
    (hu : ∀ m, m < N → u m ∉ Submodule.span ℝ (u '' Set.Iio m)) :
    ∀ m, m < N → gs b u m ≠ 0 := by
  intro m hm hzero
  refine hu m hm ?_
  have hS : (∑ i ∈ Finset.range m,
      (b (u m) (gs b u i) / b (gs b u i) (gs b u i)) • gs b u i)
        ∈ Submodule.span ℝ (u '' Set.Iio m) := by
    refine Submodule.sum_mem _ fun i hi => ?_
    have him : i < m := Finset.mem_range.mp hi
    refine Submodule.smul_mem _ _ ?_
    refine Submodule.span_mono (Set.image_mono ?_) (gs_mem_span b u i)
    exact fun x hx => lt_of_le_of_lt hx him
  have hum : u m = ∑ i ∈ Finset.range m,
      (b (u m) (gs b u i) / b (gs b u i) (gs b u i)) • gs b u i := by
    have := gs_def b u m
    rw [hzero] at this
    linear_combination (norm := abel) -this
  rw [hum]
  exact hS

/-- **17.6. Tétel.** Euklideszi tér tetszőleges `u₁,…,u_k` lineárisan független
vektorrendszeréhez van olyan `v₁,…,v_k` ortogonális vektorrendszer, melyre
`[u₁,…,uᵢ] = [v₁,…,vᵢ]` minden `i = 1,…,k` esetén.

*Bizonyítás (a könyv szerint).* A Gram–Schmidt-féle ortogonalizáció: a `v_i` vektort
`v_i = u_i + ∑_{j<i} λ_j v_j` alakban keresve az ortogonalitási feltétel egyértelműen
meghatározza a `λ_j` együtthatókat; a kapott vektorok nem nullák, mert a két
vektorrendszer ekvivalens. -/
theorem gram_schmidt_ortogonalizacio {b : V → V → ℝ} (hb : BelsoSzorzat b) {k : ℕ}
    {u : Fin k → V} (hu : LinFuggetlen ℝ u) :
    ∃ v : Fin k → V, OrtogonalisRendszer b v ∧ (∀ i, v i ≠ 0) ∧
      ∀ i : Fin k, Generalt ℝ (u '' {j : Fin k | j ≤ i})
        = Generalt ℝ (v '' {j : Fin k | j ≤ i}) := by
  classical
  set U : ℕ → V := kiterjesztes u with hU
  have hne : ∀ m, m < k → gs b U m ≠ 0 :=
    gs_ne_zero (b := b) fun m hm => notMem_span_elozok hu hm
  refine ⟨fun i => gs b U (i : ℕ), ?_, fun i => hne i i.2, ?_⟩
  · intro i j hij
    refine gs_ortogonalis hb U k hne (i : ℕ) (j : ℕ) i.2 j.2 ?_
    exact fun h => hij (Fin.ext h)
  · intro i
    have himg : (fun i : Fin k => gs b U (i : ℕ)) '' {j : Fin k | j ≤ i}
        = gs b U '' Set.Iic (i : ℕ) := by
      ext x
      constructor
      · rintro ⟨j, hj, rfl⟩
        exact ⟨(j : ℕ), hj, rfl⟩
      · rintro ⟨m, hm, rfl⟩
        exact ⟨⟨m, lt_of_le_of_lt hm i.2⟩, hm, rfl⟩
    rw [himg, ← kiterjesztes_image_Iic u i, generalt_eq_span, generalt_eq_span,
      span_gs_eq_span_u]

/-- **17.7. Megjegyzés.** Ha az `u_0,…,u_{l−1}` kezdőszelet már ortogonális (és egyik
tagja sem nulla), akkor az ortogonalizáció ezeket a vektorokat változatlanul hagyja:
`v_i = u_i` minden `i < l` esetén. -/
theorem gs_eq_of_ortogonalis {b : V → V → ℝ} (u : ℕ → V) {l : ℕ}
    (hort : ∀ i j, i < l → j < l → i ≠ j → b (u i) (u j) = 0) :
    ∀ m, m < l → gs b u m = u m := by
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm
    rw [gs_def]
    have hzero : ∀ i ∈ Finset.range m,
        (b (u m) (gs b u i) / b (gs b u i) (gs b u i)) • gs b u i = 0 := by
      intro i hi
      have him : i < m := Finset.mem_range.mp hi
      have hil : i < l := lt_trans him hm
      rw [ih i him hil, hort m i hm hil (fun h => absurd h.symm (Nat.ne_of_lt him)),
        zero_div, zero_smul]
    rw [Finset.sum_congr rfl hzero]
    simp

/-! ## 17.8. Következmény: ortonormált bázis létezése -/

/-- **Egy ortogonalizációs lépés.** Ha `u₁,…,u_k` ortonormált rendszer és `x` nincs benne
az általuk generált altérben, akkor az `x − ∑ᵢ⟨x,uᵢ⟩uᵢ` vektor normáltja olyan `w`
vektor, mely merőleges minden `uᵢ`-re, így `u₁,…,u_k,w` is ortonormált rendszer.
(Ez a Gram–Schmidt-féle ortogonalizáció egyetlen lépése.) -/
theorem letezik_meroleges_normalt {b : V → V → ℝ} (hb : BelsoSzorzat b) {k : ℕ}
    {u : Fin k → V} (hu : OrtonormaltRendszer b u) {x : V}
    (hx : x ∉ Generalt ℝ (Set.range u)) :
    ∃ w : V, hossz b w = 1 ∧ ∀ i, b w (u i) = 0 := by
  classical
  set p : V := x - ∑ i, b x (u i) • u i with hp
  have hpu : ∀ j, b p (u j) = 0 := by
    intro j
    have hsum : b (∑ i, b x (u i) • u i) (u j) = b x (u j) := by
      rw [bilin_sum_left hb.bilin]
      have hterm : ∀ i ∈ (Finset.univ : Finset (Fin k)),
          b (b x (u i) • u i) (u j) = if i = j then b x (u j) else 0 := by
        intro i _
        rw [hb.bilin.2.2.1, ortonormalt_apply hb hu i j]
        by_cases hij : i = j
        · subst hij; simp
        · simp [hij]
      rw [Finset.sum_congr rfl hterm, Finset.sum_ite_eq' Finset.univ j
        (fun _ => b x (u j)), if_pos (Finset.mem_univ j)]
    rw [hp, bilin_sub_left hb.bilin, hsum, sub_self]
  have hpne : p ≠ 0 := by
    intro h0
    refine hx ?_
    have hxeq : x = ∑ i, b x (u i) • u i := by
      have : x - ∑ i, b x (u i) • u i = 0 := by rw [← hp, h0]
      linear_combination (norm := abel) this
    rw [generalt_eq_span, hxeq]
    exact Submodule.sum_mem _ fun i _ =>
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  have hposp : 0 < hossz b p := hossz_pos hb hpne
  refine ⟨(1 / hossz b p) • p, ?_, ?_⟩
  · rw [hossz_smul hb, abs_of_pos (by positivity)]
    field_simp
  · intro i
    rw [hb.bilin.2.2.1, hpu i, mul_zero]

/-- Ortonormált rendszer bővítése egy rá merőleges normált vektorral újra ortonormált
rendszert ad. -/
theorem ortonormalt_snoc {b : V → V → ℝ} (hb : BelsoSzorzat b) {k : ℕ} {u : Fin k → V}
    (hu : OrtonormaltRendszer b u) {w : V} (hw : hossz b w = 1)
    (hwu : ∀ i, b w (u i) = 0) :
    OrtonormaltRendszer b (Fin.snoc u w : Fin (k + 1) → V) := by
  constructor
  · intro i j hij
    revert hij
    refine Fin.lastCases ?_ ?_ i
    · refine Fin.lastCases ?_ ?_ j
      · intro hij
        exact absurd rfl hij
      · intro j' _
        simpa using hwu j'
    · intro i'
      refine Fin.lastCases ?_ ?_ j
      · intro _
        simpa [hb.symm (u i') w] using hwu i'
      · intro j' hij
        have hij' : i' ≠ j' := fun h => hij (by simp [h])
        simpa using hu.1 i' j' hij'
  · intro i
    refine Fin.lastCases ?_ ?_ i
    · simpa using hw
    · intro i'
      simpa using hu.2 i'

/-- Segédtétel a 17.8. Következményhez: ha `V`-nek van `l` elemű generátorrendszere,
akkor minden ortonormált rendszer legfeljebb `d` lépésben ortonormált bázissá
egészíthető ki, ahol `l ≤ k + d`. -/
theorem ortonormalt_egeszitheto_aux {b : V → V → ℝ} (hb : BelsoSzorzat b) {l : ℕ}
    {w0 : Fin l → V} (hw0 : Generalja ℝ w0) :
    ∀ (d k : ℕ) (u : Fin k → V), l ≤ k + d → OrtonormaltRendszer b u →
      ∃ (m : ℕ) (w : Fin m → V), Bazis ℝ w ∧ OrtonormaltRendszer b w ∧ k ≤ m ∧
        ∀ (i : ℕ) (hik : i < k) (him : i < m), w ⟨i, him⟩ = u ⟨i, hik⟩ := by
  intro d
  induction d with
  | zero =>
    intro k u hl hu
    by_cases hgen : Generalja ℝ u
    · exact ⟨k, u, ⟨ortonormalt_linFuggetlen hb hu, hgen⟩, hu, le_refl k,
        fun i hik him => rfl⟩
    · exfalso
      obtain ⟨x, hx⟩ : ∃ x : V, x ∉ Generalt ℝ (Set.range u) := by
        by_contra hcon
        push_neg at hcon
        exact hgen (Set.eq_univ_of_forall hcon)
      obtain ⟨w, hw, hwu⟩ := letezik_meroleges_normalt hb hu hx
      have hind : LinFuggetlen ℝ (Fin.snoc u w : Fin (k + 1) → V) :=
        ortonormalt_linFuggetlen hb (ortonormalt_snoc hb hu hw hwu)
      have := linFuggetlen_le_generator hind hw0
      omega
  | succ e ih =>
    intro k u hl hu
    by_cases hgen : Generalja ℝ u
    · exact ⟨k, u, ⟨ortonormalt_linFuggetlen hb hu, hgen⟩, hu, le_refl k,
        fun i hik him => rfl⟩
    · obtain ⟨x, hx⟩ : ∃ x : V, x ∉ Generalt ℝ (Set.range u) := by
        by_contra hcon
        push_neg at hcon
        exact hgen (Set.eq_univ_of_forall hcon)
      obtain ⟨w, hw, hwu⟩ := letezik_meroleges_normalt hb hu hx
      obtain ⟨m, v, hvb, hvon, hkm, hveq⟩ :=
        ih (k + 1) (Fin.snoc u w) (by omega) (ortonormalt_snoc hb hu hw hwu)
      refine ⟨m, v, hvb, hvon, by omega, fun i hik him => ?_⟩
      rw [hveq i (by omega) him]
      simp [Fin.snoc, hik]

/-- **17.8. Következmény.** Euklideszi tér bármely ortonormált vektorrendszere
kiegészíthető ortonormált bázissá.

*Bizonyítás (a könyv gondolatmenete).* Az ortonormált rendszer lineárisan független;
egészítsük ki bázissá, és alkalmazzuk rá a Gram–Schmidt-féle ortogonalizációt — a
17.7. Megjegyzés szerint az első vektorok változatlanok maradnak —, végül a nem normált
vektorokat osszuk el a hosszúkkal. (Az alábbi bizonyítás ugyanezt az eljárást
lépésenként végzi el: amíg a rendszer nem generátorrendszer, egy rá merőleges normált
vektorral bővíti.) -/
theorem ortonormalt_bazissa_egeszitheto {b : V → V → ℝ} (hb : BelsoSzorzat b)
    (hdim : VegesDimenzios ℝ V) {k : ℕ} {u : Fin k → V} (hu : OrtonormaltRendszer b u) :
    ∃ (m : ℕ) (w : Fin m → V), Bazis ℝ w ∧ OrtonormaltRendszer b w ∧ k ≤ m ∧
      ∀ (i : ℕ) (hik : i < k) (him : i < m), w ⟨i, him⟩ = u ⟨i, hik⟩ := by
  obtain ⟨l, w0, hw0⟩ := hdim
  exact ortonormalt_egeszitheto_aux hb hw0 l k u (by omega) hu

/-- **17.8. Következmény (második rész).** Euklideszi térben van ortonormált bázis.

*Bizonyítás.* Alkalmazzuk az előző állítást az üres vektorrendszerre. -/
theorem letezik_ortonormalt_bazis {b : V → V → ℝ} (hb : BelsoSzorzat b)
    (hdim : VegesDimenzios ℝ V) :
    ∃ (m : ℕ) (w : Fin m → V), Bazis ℝ w ∧ OrtonormaltRendszer b w := by
  obtain ⟨m, w, hwb, hwon, -, -⟩ :=
    ortonormalt_bazissa_egeszitheto hb hdim (u := (Fin.elim0 : Fin 0 → V))
      ⟨fun i => i.elim0, fun i => i.elim0⟩
  exact ⟨m, w, hwb, hwon⟩

/-- **17.8.** Adott dimenziószám esetén az ortonormált bázis elemszáma a dimenzió. -/
theorem letezik_ortonormalt_bazis_dim {b : V → V → ℝ} (hb : BelsoSzorzat b) {n : ℕ}
    (hdim : Dimenzioja ℝ V n) :
    ∃ w : Fin n → V, Bazis ℝ w ∧ OrtonormaltRendszer b w := by
  obtain ⟨e, he⟩ := hdim
  obtain ⟨m, w, hwb, hwon⟩ := letezik_ortonormalt_bazis hb ⟨n, e, he.2⟩
  have hmn : m = n := bazisok_egyenlo_elemszam hwb he
  subst hmn
  exact ⟨w, hwb, hwon⟩

/-! ## 17.9. Definíció, 17.10. Tétel: euklideszi terek izomorfiája -/

/-- **17.9. Definíció.** Az `(U,b₁)` és `(V,b₂)` euklideszi terek *izomorfak*, ha van olyan
`φ : U → V` vektortér-izomorfizmus, mely megtartja a belső szorzatot. -/
def IzomorfEuklideszi {U : Type*} [AddCommGroup U] [Module ℝ U] (b₁ : U → U → ℝ)
    (b₂ : V → V → ℝ) : Prop :=
  ∃ f : U → V, Izomorfizmus ℝ f ∧ ∀ u v, b₂ (f u) (f v) = b₁ u v

/-- **17.10. Tétel.** Bármely `n`-dimenziós euklideszi tér izomorf az `ℝⁿ` euklideszi
térrel (a standard belső szorzattal).

*Bizonyítás (a könyv szerint).* Legyen `e₁,…,e_n` ortonormált bázis `V`-ben, és legyen
`φ : ℝⁿ → V, (x₁,…,x_n) ↦ ∑ xᵢeᵢ`. A 10.10. Tétel bizonyítása szerint `φ` vektortér-
izomorfizmus, és
`⟨φx, φy⟩ = ∑ᵢ∑ⱼ xᵢyⱼ⟨eᵢ,eⱼ⟩ = ∑ᵢ xᵢyᵢ = ⟨x,y⟩`. -/
theorem izomorf_standard {b : V → V → ℝ} (hb : BelsoSzorzat b) {n : ℕ}
    (hdim : Dimenzioja ℝ V n) :
    IzomorfEuklideszi (standardBSZ (n := n)) b := by
  obtain ⟨e, heb, heon⟩ := letezik_ortonormalt_bazis_dim hb hdim
  refine ⟨fun x => ∑ i, x i • e i, ⟨⟨?_, ?_⟩, ?_, ?_⟩, ?_⟩
  · intro x y
    simp [add_smul, Finset.sum_add_distrib]
  · intro c x
    rw [Finset.smul_sum]
    exact Finset.sum_congr rfl fun i _ => by
      simp [smul_smul]
  · intro x y hxy
    exact egyertelmu_eloallitas heb.1 hxy
  · intro v
    obtain ⟨g, hg, -⟩ := koordinatak_egyertelmuek heb v
    exact ⟨g, hg.symm⟩
  · intro x y
    rw [bilin_kombinacio_left hb.bilin]
    have hterm : ∀ i ∈ (Finset.univ : Finset (Fin n)),
        x i * b (e i) (∑ j, y j • e j) = x i * y i := by
      intro i _
      rw [bilin_kombinacio_right hb.bilin]
      have hin : ∀ j ∈ (Finset.univ : Finset (Fin n)),
          y j * b (e i) (e j) = if j = i then y i else 0 := by
        intro j _
        rw [ortonormalt_apply hb heon i j]
        by_cases hij : j = i
        · subst hij; simp
        · simp [hij, Ne.symm hij]
      rw [Finset.sum_congr rfl hin, Finset.sum_ite_eq' Finset.univ i (fun _ => y i),
        if_pos (Finset.mem_univ i)]
    rw [Finset.sum_congr rfl hterm]
    rfl

end Ch17
end SzaboLinAlg
