import Mathlib
import Analizis.Ch05a_FuggvenyekAlapfogalmak
import Analizis.Ch05b_Folytonossag
import Analizis.Ch05e_AlgebraiFuggvenyek

/-!
# Leindler László: Analízis — 5.8–5.10. pont

## Exponenciális függvény, logaritmusfüggvény, irracionális kitevőjű hatványfüggvény

Ez a fájl a könyv **5.8., 5.9. és 5.10. pontját** formalizálja:

* **5.8.1. Definíció** — az `aˣ` exponenciális függvény (`a > 0`) racionális kitevőkről
  való kiterjesztése: `aˣ := lim aʳⁿ`, ahol `{rₙ}` tetszőleges `x`-hez konvergáló
  racionális sorozat. Formálisan ezt úgy fejezzük ki, hogy a Mathlib `a ^ x`
  (valós kitevős hatvány) függvényére *bármely* `rₙ → x` racionális sorozat esetén
  `a^{rₙ} → aˣ` teljesül (`exp_racionalis_kozelites`) — ez egyszerre igazolja a
  határérték létezését és a definíció egyértelműségét —, továbbá a permanencia elvet
  (`rpow_rat_eq_tortHatvany`): racionális kitevőkre a definíció a korábbi
  törtkitevős hatványt adja vissza.
* **5.8.2. Tétel** — az `aˣ⁺ʸ = aˣ·aʸ` és `(aˣ)ʸ = aˣʸ` azonosságok.
* **5.8.3. Tétel** — az exponenciális függvény mindenütt folytonos.
* **5.9.1–5.9.4** — a logaritmusfüggvény mint az exponenciális függvény inverze, a
  logaritmus azonosságai, a természetes alapú logaritmus, valamint az áttérés más
  alapra.
* **5.10.1. Definíció** — az irracionális kitevőjű hatványfüggvény `xᵅ := e^{α log x}`
  (`x > 0`), amely az 5.5.2. Tétel (összetett függvény folytonossága) szerint minden
  pozitív helyen folytonos.
-/

namespace Leindler.Ch05

open Set

/-! ## 5.8. Exponenciális függvény -/

/-- **5.8.1. Definíció (permanencia elv).** Racionális `p/q` kitevőre a valós kitevős
hatvány a korábban (5.7.11) definiált törtkitevős hatvánnyal egyezik meg.
(A könyv `a > 0` mellett mondja ki; a formalizált alakban erre nincs szükség.) -/
theorem rpow_rat_eq_tortHatvany (a : ℝ) (p : ℤ) (q : ℕ) :
    a ^ ((p : ℝ) / (q : ℝ)) = tortHatvany p q a := rfl

/-- **5.8.1. Definíció.** Az `aˣ` (`a > 0`) exponenciális függvény a racionális kitevőjű
hatványok határértékeként áll elő: *bármely* `x`-hez konvergáló `{rₙ}` racionális
sorozatra `a^{rₙ} → aˣ`. Ez egyben azt is mutatja, hogy a definícióban szereplő
határérték létezik, és nem függ a választott sorozattól.

*Bizonyítás.* A könyv a Cauchy-féle konvergenciakritériummal igazolja a határérték
létezését, és a két sorozat „fésűs egyesítésével” az egyértelműséget; itt ezzel
egyenértékűen az `y ↦ aʸ` függvény folytonosságára hivatkozunk. -/
theorem exp_racionalis_kozelites {a : ℝ} (ha : 0 < a) {r : ℕ → ℚ} {x : ℝ}
    (hr : Ch04.HatarErtek (fun n => (r n : ℝ)) x) :
    Ch04.HatarErtek (fun n => a ^ ((r n : ℝ))) (a ^ x) := by
  rw [Ch04.hatarErtek_iff_tendsto] at hr ⊢
  exact (Real.continuousAt_const_rpow (ne_of_gt ha)).tendsto.comp hr

/-- **5.8.1.** Az exponenciális függvény mindenütt pozitív. -/
theorem exp_pos {a : ℝ} (ha : 0 < a) (x : ℝ) : 0 < a ^ x := Real.rpow_pos_of_pos ha x

/-- **5.8.1.** Ha `a > 1`, akkor `aˣ` szigorúan növekedő. -/
theorem exp_szigNovekedo {a : ℝ} (ha : 1 < a) : SzigNovekedo (fun x => a ^ x) univ := by
  rw [szigNovekedo_iff_strictMonoOn]
  intro u _ v _ huv
  exact (Real.rpow_lt_rpow_left_iff ha).mpr huv

/-- **5.8.1.** Ha `a = 1`, akkor `aˣ = 1` minden `x`-re. -/
theorem exp_egy (x : ℝ) : (1 : ℝ) ^ x = 1 := Real.one_rpow x

/-- **5.8.1.** Ha `0 < a < 1`, akkor `aˣ` szigorúan csökkenő. -/
theorem exp_szigCsokkeno {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    SzigCsokkeno (fun x => a ^ x) univ := by
  intro u _ v _ huv
  exact Real.rpow_lt_rpow_of_exponent_gt ha ha1 huv

/-- **5.8.2. Tétel, 1.** `aˣ⁺ʸ = aˣ · aʸ`.

*Bizonyítás.* Ha `rₙ' → x` és `rₙ'' → y`, akkor `rₙ' + rₙ'' → x + y`, így az 5.8.1.
definíció és a racionális kitevőkre már ismert azonosság szerint
`aˣ⁺ʸ = lim a^{rₙ'+rₙ''} = lim a^{rₙ'}·a^{rₙ''} = aˣ·aʸ`. -/
theorem exp_azonossag_osszeg {a : ℝ} (ha : 0 < a) (x y : ℝ) :
    a ^ (x + y) = a ^ x * a ^ y := Real.rpow_add ha x y

/-- **5.8.2. Tétel, 1. (speciális eset).** `a⁻ˣ = 1/aˣ`. -/
theorem exp_azonossag_neg {a : ℝ} (ha : 0 < a) (x : ℝ) : a ^ (-x) = (a ^ x)⁻¹ :=
  Real.rpow_neg ha.le x

/-- **5.8.2. Tétel, 2.** `(aˣ)ʸ = aˣʸ`. -/
theorem exp_azonossag_szorzat {a : ℝ} (ha : 0 < a) (x y : ℝ) :
    (a ^ x) ^ y = a ^ (x * y) := (Real.rpow_mul ha.le x y).symm

/-- **5.8.3. Tétel.** Az exponenciális függvény mindenütt folytonos.

*Bizonyítás.* Mivel `|aˣ - aˣ⁰| = aˣ⁰·|aˣ⁻ˣ⁰ - a⁰|`, elég azt megmutatni, hogy `aˣ` az
`x₀ = 0` pontban folytonos; ez pedig az `ⁿ√a → 1` határértékből következik. -/
theorem folytonos_exp {a : ℝ} (ha : 0 < a) (x₀ : ℝ) : CauchyFolytonos (fun x => a ^ x) x₀ :=
  (cauchyFolytonos_iff_continuousAt _ _).2 (Real.continuousAt_const_rpow (ne_of_gt ha))

/-! ## 5.9. Logaritmusfüggvény -/

/-- **5.9.1. Definíció.** Legyen `a > 0`, `a ≠ 1`. Az `y = aˣ` függvény szigorúan
monoton, ezért van inverze; ezt nevezzük `a` alapú logaritmusfüggvénynek. -/
noncomputable def logA (a x : ℝ) : ℝ := Real.log x / Real.log a

theorem log_alap_ne_zero {a : ℝ} (ha : 0 < a) (ha1 : a ≠ 1) : Real.log a ≠ 0 :=
  Real.log_ne_zero_of_pos_of_ne_one ha ha1

/-- **5.9.1.** A logaritmus az exponenciális függvény inverze: `a^{log_a x} = x`
minden `x > 0`-ra. -/
theorem rpow_logA {a : ℝ} (ha : 0 < a) (ha1 : a ≠ 1) {x : ℝ} (hx : 0 < x) :
    a ^ logA a x = x := by
  rw [logA, Real.rpow_def_of_pos ha, mul_div_cancel₀ _ (log_alap_ne_zero ha ha1),
    Real.exp_log hx]

/-- **5.9.1.** A logaritmusfüggvény az exponenciális függvény inverze a másik irányban
is: `log_a (aʸ) = y`. -/
theorem logA_rpow {a : ℝ} (ha : 0 < a) (ha1 : a ≠ 1) (y : ℝ) : logA a (a ^ y) = y := by
  rw [logA, Real.log_rpow ha, mul_div_assoc, div_self (log_alap_ne_zero ha ha1), mul_one]

/-- **5.9.2. Tétel.** `log_a (xy) = log_a x + log_a y`.

*Bizonyítás.* Ha `x = a^{z₁}` és `y = a^{z₂}`, akkor `xy = a^{z₁+z₂}`, tehát a logaritmus
definíciója szerint `log_a (xy) = z₁ + z₂ = log_a x + log_a y`. -/
theorem logA_mul {a : ℝ} {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) :
    logA a (x * y) = logA a x + logA a y := by
  rw [logA, logA, logA, Real.log_mul hx hy, add_div]

/-- **5.9.2. Tétel.** `log_a (x/y) = log_a x - log_a y`.

(A könyvben a hányadosszabály pozitív `x`, `y` mellett szerepel; itt az `x ≠ 0`,
`y ≠ 0` feltétel elegendő.) -/
theorem logA_div {a : ℝ} {x y : ℝ} (hx : x ≠ 0) (hy : y ≠ 0) :
    logA a (x / y) = logA a x - logA a y := by
  rw [logA, logA, logA, Real.log_div hx hy, sub_div]

/-- **5.9.1.** Ha `a > 1`, akkor a logaritmusfüggvény a pozitív számok halmazán
szigorúan növekedő. -/
theorem logA_szigNovekedo {a : ℝ} (ha : 1 < a) : SzigNovekedo (logA a) (Ioi 0) := by
  rw [szigNovekedo_iff_strictMonoOn]
  intro u hu v hv huv
  have hlog : 0 < Real.log a := Real.log_pos ha
  have : Real.log u < Real.log v := Real.log_lt_log hu huv
  unfold logA
  gcongr

/-- A logaritmusfüggvény minden pozitív helyen folytonos (az inverz függvény
folytonosságáról szóló 5.6.1. Tétel következménye). -/
theorem folytonos_logA (a : ℝ) {x₀ : ℝ} (hx₀ : 0 < x₀) : CauchyFolytonos (logA a) x₀ :=
  (cauchyFolytonos_iff_continuousAt _ _).2
    ((Real.continuousAt_log (ne_of_gt hx₀)).div_const _)

/-- **5.9.3. Definíció.** Az `y = eˣ` függvény inverzét *természetes alapú
logaritmusfüggvénynek* nevezzük; jelölése `log x` vagy `ln x`. -/
theorem logA_exp_eq_log (x : ℝ) : logA (Real.exp 1) x = Real.log x := by
  simp [logA]

/-- **5.9.4. Tétel.** Ha `a` és `b` pozitív számok (`a ≠ 1`, `b ≠ 1`), akkor
`log_a b · log_b a = 1`, azaz `log_a b = 1 / log_b a`. -/
theorem logA_mul_logA {a b : ℝ} (ha : 0 < a) (ha1 : a ≠ 1) (hb : 0 < b) (hb1 : b ≠ 1) :
    logA a b * logA b a = 1 := by
  have hla : Real.log a ≠ 0 := log_alap_ne_zero ha ha1
  have hlb : Real.log b ≠ 0 := log_alap_ne_zero hb hb1
  unfold logA
  field_simp

/-! ## 5.10. Irracionális kitevőjű hatványfüggvény -/

/-- **5.10.1. Definíció.** `y = xᵅ := e^{α log x}` (`x > 0`). -/
noncomputable def irrHatvany (al x : ℝ) : ℝ := Real.exp (al * Real.log x)

/-- Az így definiált hatványfüggvény a valós kitevős hatvánnyal egyezik meg. -/
theorem irrHatvany_eq_rpow (al : ℝ) {x : ℝ} (hx : 0 < x) : irrHatvany al x = x ^ al := by
  rw [irrHatvany, Real.rpow_def_of_pos hx, mul_comm]

/-- **5.10.1.** Az összetett függvények folytonosságára vonatkozó 5.5.2. Tétel szerint az
irracionális kitevőjű hatványfüggvény minden pozitív helyen folytonos. -/
theorem folytonos_irrHatvany (al : ℝ) {x₀ : ℝ} (hx₀ : 0 < x₀) :
    CauchyFolytonos (irrHatvany al) x₀ :=
  (cauchyFolytonos_iff_continuousAt _ _).2
    (Real.continuous_exp.continuousAt.comp
      ((Real.continuousAt_log (ne_of_gt hx₀)).const_mul al))

/-- **5.10.1.** Az irracionális kitevőjű hatványfüggvény pozitív értékeket vesz fel. -/
theorem irrHatvany_pos (al x : ℝ) : 0 < irrHatvany al x := Real.exp_pos _

end Leindler.Ch05
