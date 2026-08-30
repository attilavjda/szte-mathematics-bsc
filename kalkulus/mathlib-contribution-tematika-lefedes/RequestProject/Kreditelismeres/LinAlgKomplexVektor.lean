/-
# Lineáris algebra I — kreditelismerési bizonyítéktár, 1. rész

A `LineárisalgebraI.-7.pdf` (MBLK15E) tematikájának **első három blokkja**:

* komplex számok: kanonikus és trigonometrikus alak, Moivre-képlet, gyökvonás,
  egységgyökök, primitív egységgyökök;
* vektorok és pontok a valós elem-`n`-esek körében: összeadás, skalárral szorzás,
  lineáris kombináció, egyenesek és síkok;
* belső szorzat, vektorok hossza, háromszög-egyenlőtlenség,
  Cauchy–Schwarz-egyenlőtlenség, merőlegesség, merőleges vetítés, alkalmazások
  (a háromszög nevezetes pontjai).
-/
import Mathlib

namespace SZTE.Kredit.LinAlg

open Finset Matrix

/-! ## Komplex számok -/

/-- **Kanonikus alak.** Minden komplex szám egyértelműen írható `a + bi` alakban. -/
theorem complex_canonical (z : ℂ) : z = (z.re : ℂ) + (z.im : ℂ) * Complex.I :=
  (Complex.re_add_im z).symm

/-- **Trigonometrikus alak.** Minden nemnulla komplex szám felírható `r(cos φ + i sin φ)`
alakban, ahol `r = |z| > 0`. -/
theorem complex_trig_form (z : ℂ) (hz : z ≠ 0) :
    ∃ r φ : ℝ, 0 < r ∧ z = (r : ℂ) * (Real.cos φ + Real.sin φ * Complex.I) := by
  refine ⟨‖z‖, Complex.arg z, norm_pos_iff.mpr hz, ?_⟩
  rw [Complex.ofReal_cos, Complex.ofReal_sin]
  exact (Complex.norm_mul_cos_add_sin_mul_I z).symm

/-- **Moivre-képlet.** `(cos φ + i sin φ)^n = cos (nφ) + i sin (nφ)`. -/
theorem moivre (φ : ℝ) (n : ℕ) :
    ((Real.cos φ : ℂ) + (Real.sin φ : ℂ) * Complex.I) ^ n =
      (Real.cos (n * φ) : ℂ) + (Real.sin (n * φ) : ℂ) * Complex.I := by
  have h : ∀ t : ℝ, ((Real.cos t : ℂ) + (Real.sin t : ℂ) * Complex.I)
      = Complex.exp (t * Complex.I) := by
    intro t
    rw [Complex.exp_mul_I, Complex.ofReal_cos, Complex.ofReal_sin]
  rw [h, h, ← Complex.exp_nat_mul]
  push_cast
  ring_nf

/-- Az `exp (2πi/n)` hatványai éppen az `exp (2πik/n)` alakú számok. -/
theorem exp_root_pow (n k : ℕ) :
    (Complex.exp (2 * Real.pi * Complex.I / n)) ^ k
      = Complex.exp (2 * Real.pi * Complex.I * k / n) := by
  rw [← Complex.exp_nat_mul]
  congr 1
  ring

/-- **Gyökvonás.** Egy nemnulla komplex számnak pontosan `n` darab `n`-edik gyöke van. -/
theorem complex_nth_roots_card (z : ℂ) (hz : z ≠ 0) (n : ℕ) (hn : 0 < n) :
    {w : ℂ | w ^ n = z}.ncard = n := by
  classical
  haveI : NeZero n := ⟨hn.ne'⟩
  obtain ⟨w₀, hw₀⟩ := IsAlgClosed.exists_pow_nat_eq z hn
  have hw₀ne : w₀ ≠ 0 := by
    intro h
    rw [h, zero_pow hn.ne'] at hw₀
    exact hz hw₀.symm
  set zeta := Complex.exp (2 * Real.pi * Complex.I / n) with hzeta
  have hprim : IsPrimitiveRoot zeta n := Complex.isPrimitiveRoot_exp n hn.ne'
  have hset : {w : ℂ | w ^ n = z} = ↑((range n).image fun k => zeta ^ k * w₀) := by
    ext w
    simp only [Set.mem_setOf_eq, Finset.coe_image, Set.mem_image, Finset.mem_coe,
      Finset.mem_range]
    constructor
    · intro hw
      have hone : (w / w₀) ^ n = 1 := by rw [div_pow, hw, hw₀, div_self hz]
      obtain ⟨i, hi, hie⟩ := hprim.eq_pow_of_pow_eq_one hone
      exact ⟨i, hi, by rw [hie]; field_simp⟩
    · rintro ⟨k, hk, rfl⟩
      rw [mul_pow, ← pow_mul, mul_comm k n, pow_mul, hprim.pow_eq_one, one_pow, one_mul, hw₀]
  rw [hset, Set.ncard_coe_finset, Finset.card_image_of_injOn (hprim.injOn_pow_mul hw₀ne),
    Finset.card_range]

/-- **Egységgyökök.** `w^n = 1` pontosan akkor, ha `w = exp(2πik/n)` valamely `k < n`-re. -/
theorem nth_roots_of_unity (n : ℕ) (hn : 0 < n) (w : ℂ) :
    w ^ n = 1 ↔ ∃ k : ℕ, k < n ∧ w = Complex.exp (2 * Real.pi * Complex.I * k / n) := by
  haveI : NeZero n := ⟨hn.ne'⟩
  have hprim := Complex.isPrimitiveRoot_exp n hn.ne'
  constructor
  · intro h
    obtain ⟨i, hi, hie⟩ := hprim.eq_pow_of_pow_eq_one h
    exact ⟨i, hi, by rw [← hie, exp_root_pow]⟩
  · rintro ⟨k, _, rfl⟩
    rw [← exp_root_pow, ← pow_mul, mul_comm k n, pow_mul, hprim.pow_eq_one, one_pow]

/-- Az `n`-edik egységgyökök összege `0`, ha `n ≥ 2`. -/
theorem sum_nth_roots_of_unity (n : ℕ) (hn : 2 ≤ n) :
    ∑ k ∈ range n, Complex.exp (2 * Real.pi * Complex.I * k / n) = 0 := by
  have hn0 : n ≠ 0 := by omega
  have hprim := Complex.isPrimitiveRoot_exp n hn0
  have hne : Complex.exp (2 * Real.pi * Complex.I / n) ≠ 1 := hprim.ne_one (by omega)
  calc ∑ k ∈ range n, Complex.exp (2 * Real.pi * Complex.I * k / n)
      = ∑ k ∈ range n, (Complex.exp (2 * Real.pi * Complex.I / n)) ^ k :=
        Finset.sum_congr rfl fun k _ => (exp_root_pow n k).symm
    _ = 0 := by rw [geom_sum_eq hne, hprim.pow_eq_one]; simp

/-- **Primitív egységgyök.** `exp(2πi/n)` primitív `n`-edik egységgyök: pontosan azok a
kitevők adnak `1`-et, amelyek oszthatók `n`-nel. -/
theorem primitive_root_iff (n : ℕ) (hn : 0 < n) (k : ℕ) :
    (Complex.exp (2 * Real.pi * Complex.I / n)) ^ k = 1 ↔ n ∣ k :=
  (Complex.isPrimitiveRoot_exp n hn.ne').pow_eq_one_iff_dvd k

/-! ## Vektorok és pontok a valós elem-`n`-esek körében -/

/-- Az `x` és `y` pontokat összekötő egyenes (affin egyenes) paraméteres alakja. -/
def lineThrough {n : ℕ} (x y : Fin n → ℝ) : Set (Fin n → ℝ) :=
  {p | ∃ t : ℝ, p = fun i => x i + t * (y i - x i)}

/-- **Az egyenes pontjai.** `p` pontosan akkor van az `x`-en és `y`-on átmenő egyenesen,
ha `p` az `x` és `y` affin kombinációja. -/
theorem mem_lineThrough_iff {n : ℕ} (x y p : Fin n → ℝ) :
    p ∈ lineThrough x y ↔ ∃ s t : ℝ, s + t = 1 ∧ p = fun i => s * x i + t * y i := by
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨1 - t, t, by ring, by funext i; ring⟩
  · rintro ⟨s, t, hst, rfl⟩
    refine ⟨t, ?_⟩
    have hs : s = 1 - t := by linarith
    subst hs
    funext i
    ring

/-- Három pont pontosan akkor esik egy egyenesre, ha a különbségvektoraik lineárisan
összefüggők.

(A vázlatban szereplő `x ≠ y` feltétel a bizonyítás során feleslegesnek bizonyult,
ezért az általánosabb, feltétel nélküli alakot állítjuk.) -/
theorem collinear_iff_dependent {n : ℕ} (x y z : Fin n → ℝ) :
    z ∈ lineThrough x y ↔ ∃ t : ℝ, (fun i => z i - x i) = fun i => t * (y i - x i) := by
  constructor
  · rintro ⟨t, rfl⟩
    exact ⟨t, by funext i; ring⟩
  · rintro ⟨t, ht⟩
    refine ⟨t, ?_⟩
    funext i
    have h : z i - x i = t * (y i - x i) := congrFun ht i
    linarith

/-- Az `x`, `y`, `z` pontok által kifeszített sík. -/
def planeThrough {n : ℕ} (x y z : Fin n → ℝ) : Set (Fin n → ℝ) :=
  {p | ∃ s t : ℝ, p = fun i => x i + s * (y i - x i) + t * (z i - x i)}

/-- Az egyenes a sík részhalmaza. -/
theorem lineThrough_subset_planeThrough {n : ℕ} (x y z : Fin n → ℝ) :
    lineThrough x y ⊆ planeThrough x y z := by
  rintro p ⟨t, rfl⟩
  exact ⟨t, 0, by funext i; ring⟩

/-! ## Belső szorzat, hossz, merőlegesség -/

/-- **Belső (skaláris) szorzat** a valós elem-`n`-esek körében. -/
def dotProd {n : ℕ} (x y : Fin n → ℝ) : ℝ := ∑ i, x i * y i

/-- **Vektor hossza.** -/
noncomputable def norm2 {n : ℕ} (x : Fin n → ℝ) : ℝ := Real.sqrt (dotProd x x)

/-- A belső szorzat bilineáris és szimmetrikus. -/
theorem dotProd_symm_bilinear {n : ℕ} (x y z : Fin n → ℝ) (c : ℝ) :
    dotProd x y = dotProd y x ∧
      dotProd (fun i => x i + y i) z = dotProd x z + dotProd y z ∧
      dotProd (fun i => c * x i) y = c * dotProd x y := by
  refine ⟨?_, ?_, ?_⟩
  · exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  · simp only [dotProd, add_mul, Finset.sum_add_distrib]
  · simp only [dotProd, mul_assoc, Finset.mul_sum]

/-- A belső szorzat pozitív definit. -/
theorem dotProd_self_nonneg {n : ℕ} (x : Fin n → ℝ) :
    0 ≤ dotProd x x ∧ (dotProd x x = 0 ↔ x = 0) := by
  refine ⟨Finset.sum_nonneg fun _ _ => mul_self_nonneg _, ?_, ?_⟩
  · intro h
    funext i
    have hi := (Finset.sum_eq_zero_iff_of_nonneg
      (fun i _ => mul_self_nonneg (x i))).mp h i (Finset.mem_univ i)
    simpa [mul_self_eq_zero] using hi
  · intro h
    simp [dotProd, h]

/-- A hossz négyzete a vektor önmagával vett belső szorzata. -/
theorem norm2_sq {n : ℕ} (x : Fin n → ℝ) : norm2 x ^ 2 = dotProd x x :=
  Real.sq_sqrt (dotProd_self_nonneg x).1

/-- A hossz nemnegatív. -/
theorem norm2_nonneg {n : ℕ} (x : Fin n → ℝ) : 0 ≤ norm2 x := Real.sqrt_nonneg _

/-- **Cauchy–Schwarz-egyenlőtlenség.** -/
theorem cauchy_schwarz_dot {n : ℕ} (x y : Fin n → ℝ) :
    |dotProd x y| ≤ norm2 x * norm2 y := by
  have hsq : (dotProd x y) ^ 2 ≤ dotProd x x * dotProd y y := by
    simpa [dotProd, sq] using sum_mul_sq_le_sq_mul_sq Finset.univ x y
  rw [← Real.sqrt_sq_eq_abs, norm2, norm2, ← Real.sqrt_mul (dotProd_self_nonneg x).1]
  exact Real.sqrt_le_sqrt hsq

/-- Az összeg önmagával vett belső szorzatának kifejtése. -/
theorem dotProd_add_add {n : ℕ} (x y : Fin n → ℝ) :
    dotProd (fun i => x i + y i) (fun i => x i + y i)
      = dotProd x x + 2 * dotProd x y + dotProd y y := by
  simp only [dotProd, Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- **Háromszög-egyenlőtlenség.** -/
theorem norm2_triangle {n : ℕ} (x y : Fin n → ℝ) :
    norm2 (fun i => x i + y i) ≤ norm2 x + norm2 y := by
  have hle : dotProd x y ≤ norm2 x * norm2 y := (le_abs_self _).trans (cauchy_schwarz_dot x y)
  have key : dotProd (fun i => x i + y i) (fun i => x i + y i) ≤ (norm2 x + norm2 y) ^ 2 := by
    rw [dotProd_add_add]
    nlinarith [norm2_sq x, norm2_sq y, hle]
  calc norm2 (fun i => x i + y i)
      = Real.sqrt (dotProd (fun i => x i + y i) (fun i => x i + y i)) := rfl
    _ ≤ Real.sqrt ((norm2 x + norm2 y) ^ 2) := Real.sqrt_le_sqrt key
    _ = norm2 x + norm2 y := Real.sqrt_sq (add_nonneg (norm2_nonneg x) (norm2_nonneg y))

/-- **Pitagorasz-tétel.** Merőleges vektorokra `|x+y|² = |x|² + |y|²`. -/
theorem pythagoras {n : ℕ} (x y : Fin n → ℝ) (h : dotProd x y = 0) :
    norm2 (fun i => x i + y i) ^ 2 = norm2 x ^ 2 + norm2 y ^ 2 := by
  rw [norm2_sq, norm2_sq, norm2_sq, dotProd_add_add, h]
  ring

/-- **Merőleges vetítés egy egyenesre.** A vetület `(⟨x,v⟩/⟨v,v⟩)·v`, és a maradék merőleges
`v`-re. -/
theorem orthogonal_projection_line {n : ℕ} (x v : Fin n → ℝ) (hv : dotProd v v ≠ 0) :
    dotProd (fun i => x i - (dotProd x v / dotProd v v) * v i) v = 0 := by
  have h : dotProd (fun i => x i - (dotProd x v / dotProd v v) * v i) v
      = dotProd x v - (dotProd x v / dotProd v v) * dotProd v v := by
    simp only [dotProd, Finset.mul_sum]
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [h, div_mul_cancel₀ _ hv, sub_self]

/-- A `x - t·v` vektor hosszának négyzete `t` másodfokú függvénye. -/
theorem dotProd_sub_smul {n : ℕ} (x v : Fin n → ℝ) (t : ℝ) :
    dotProd (fun i => x i - t * v i) (fun i => x i - t * v i)
      = dotProd x x - 2 * t * dotProd x v + t ^ 2 * dotProd v v := by
  have h : dotProd x x - 2 * t * dotProd x v + t ^ 2 * dotProd v v
      = ∑ i, (x i * x i - 2 * t * (x i * v i) + t ^ 2 * (v i * v i)) := by
    simp only [dotProd, Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [h]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- A merőleges vetület a legközelebbi pont az egyenesen. -/
theorem projection_minimizes {n : ℕ} (x v : Fin n → ℝ) (hv : dotProd v v ≠ 0) (t : ℝ) :
    norm2 (fun i => x i - (dotProd x v / dotProd v v) * v i) ≤ norm2 (fun i => x i - t * v i) := by
  have hpos : 0 < dotProd v v := lt_of_le_of_ne (dotProd_self_nonneg v).1 (Ne.symm hv)
  have hc : (dotProd x v / dotProd v v) * dotProd v v = dotProd x v := div_mul_cancel₀ _ hv
  have gen : ∀ dxx P D s c : ℝ, 0 < D → c * D = P →
      dxx - 2 * c * P + c ^ 2 * D ≤ dxx - 2 * s * P + s ^ 2 * D := by
    intro dxx P D s c hD hcD
    subst hcD
    nlinarith [sq_nonneg (s - c), hD]
  refine Real.sqrt_le_sqrt ?_
  rw [dotProd_sub_smul, dotProd_sub_smul]
  exact gen (dotProd x x) (dotProd x v) (dotProd v v) t _ hpos hc

/-! ## Alkalmazás: a háromszög nevezetes pontjai -/

/-- **Súlypont.** A háromszög súlypontja mindhárom súlyvonalon rajta van. -/
theorem centroid_mem_median {n : ℕ} (A B C : Fin n → ℝ) :
    (fun i => (A i + B i + C i) / 3) ∈
      lineThrough A (fun i => (B i + C i) / 2) :=
  ⟨2 / 3, by funext i; ring⟩

/-- A súlypont a súlyvonalat `2 : 1` arányban osztja. -/
theorem centroid_ratio {n : ℕ} (A B C : Fin n → ℝ) :
    (fun i => (A i + B i + C i) / 3) =
      fun i => A i + (2 / 3) * ((B i + C i) / 2 - A i) := by
  funext i
  ring

end SZTE.Kredit.LinAlg
