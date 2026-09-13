import Mathlib
import Analizis.Ch05e_AlgebraiFuggvenyek
import Analizis.Ch05h_VegtelenbenVettHatarertek
import Analizis.Ch06b_ElemiDerivaltak

/-!
# Leindler László: Analízis — 6.8.3–6.8.4. és 6.11.3.

Ez a fájl a 6. fejezet két hiányzó pontját formalizálja:

* **6.8.3. Megjegyzés.** Az `f(x) = x^(p/q)` függvény páratlan `q` esetén a negatív
  `x`-ekre is értelmezve van (a páratlan kitevőjű gyökfüggvény segítségével).
* **6.8.4. Tétel.** Páratlan `q` esetén az `x^(p/q)` függvény differenciálható, és
  bármely `x ≠ 0`-ra `(x^(p/q))' = (p/q)·x^(p/q - 1)`.
* **6.11.3. Tétel.** A l'Hospital-szabály akkor is érvényes, ha a hányadosok
  határértékét nem egy véges helyen, hanem a `+∞`-ben (illetve `-∞`-ben) vizsgáljuk.

A `(p/q)·x^(p/q-1)` deriváltat a `(p/q)·x^(p/q)/x` alakban írjuk fel: `x ≠ 0` esetén a
kettő ugyanaz, viszont így a negatív `x`-ekre is értelmes marad a formula (a
`paratlanTortHatvany` függvény értékével kifejezve).
-/

namespace Leindler.Ch06

open Set Filter Topology Leindler.Ch05

/-! ## 6.8.3. Megjegyzés: törtkitevős hatvány páratlan nevezővel -/

/-- **6.8.3. Megjegyzés.** Páratlan `q` esetén az `x^(p/q) := (ᵍ√x)ᵖ` függvény a negatív
`x`-ekre is értelmezve van, hiszen a páratlan kitevőjű gyökfüggvény mindenütt
értelmezve van. -/
noncomputable def paratlanTortHatvany (p : ℤ) (q : ℕ) (x : ℝ) : ℝ :=
  (paratlanGyok q x) ^ p

/-- Segédlemma: pozitív `y` esetén `(y^(1/q))^p = y^(p/q)`. -/
theorem rpow_inv_zpow {y : ℝ} (hy : 0 < y) (q : ℕ) (p : ℤ) :
    (y ^ ((q : ℝ)⁻¹)) ^ p = y ^ ((p : ℝ) / (q : ℝ)) := by
  rw [← Real.rpow_intCast (y ^ ((q : ℝ)⁻¹)) p, ← Real.rpow_mul hy.le]
  congr 1
  field_simp

/-- Pozitív `x`-re a törtkitevős hatvány a szokásos `x^(p/q)` valós hatvány. -/
theorem paratlanTortHatvany_of_pos (p : ℤ) (q : ℕ) {x : ℝ} (hx : 0 < x) :
    paratlanTortHatvany p q x = x ^ ((p : ℝ) / (q : ℝ)) := by
  simp only [paratlanTortHatvany, paratlanGyok, if_pos hx.le, gyok]
  exact rpow_inv_zpow hx q p

/-- **6.8.3. Megjegyzés.** Negatív `x`-re (páratlan `q` mellett) a törtkitevős hatvány
értéke `(-1)^p·(-x)^(p/q)`. -/
theorem paratlanTortHatvany_of_neg (p : ℤ) (q : ℕ) {x : ℝ} (hx : x < 0) :
    paratlanTortHatvany p q x = (-1 : ℝ) ^ p * (-x) ^ ((p : ℝ) / (q : ℝ)) := by
  have hx' : (0 : ℝ) < -x := by linarith
  simp only [paratlanTortHatvany, paratlanGyok, if_neg (not_le.mpr hx), gyok]
  rw [show -((-x) ^ ((q : ℝ)⁻¹)) = (-1 : ℝ) * (-x) ^ ((q : ℝ)⁻¹) by ring, mul_zpow,
    rpow_inv_zpow hx' q p]

/-- **6.8.4. Tétel.** Ha `q` páratlan természetes szám, akkor az `x^(p/q)` függvény
bármely `x ≠ 0` helyen differenciálható, és

`(x^(p/q))' = (p/q)·x^(p/q - 1) = (p/q)·x^(p/q)/x`.

*Bizonyítás (a könyv gondolatmenete).* Az összetett függvény és az inverz függvény
differenciálási szabályainak együttes alkalmazásával: pozitív `x`-ekre az
`x^(p/q) = (x^(1/q))^p` alak, negatív `x`-ekre pedig az
`x^(p/q) = (-1)^p·(-x)^(p/q)` alak deriválható a hatványfüggvényre vonatkozó
6.8.2. Tétel és a láncszabály szerint. -/
theorem derivalt_paratlanTortHatvany (p : ℤ) (q : ℕ) {x : ℝ} (hx : x ≠ 0) :
    Derivalt (paratlanTortHatvany p q)
      x ((p : ℝ) / (q : ℝ) * paratlanTortHatvany p q x / x) := by
  set c : ℝ := (p : ℝ) / (q : ℝ) with hc
  refine (derivalt_iff_hasDerivAt _ _ _).2 ?_
  rcases lt_or_gt_of_ne hx with hneg | hpos
  · -- negatív `x`
    have hx' : (0 : ℝ) < -x := by linarith
    have hbase : HasDerivAt (fun t : ℝ => -t) (-1 : ℝ) x := by
      simpa using (hasDerivAt_id x).neg
    have hrp : HasDerivAt (fun t : ℝ => (-t) ^ c) (-1 * c * (-x) ^ (c - 1)) x :=
      hbase.rpow_const (Or.inl (ne_of_gt hx'))
    have hH : HasDerivAt (fun t : ℝ => (-1 : ℝ) ^ p * (-t) ^ c)
        ((-1 : ℝ) ^ p * (-1 * c * (-x) ^ (c - 1))) x := hrp.const_mul _
    have heq : (fun t : ℝ => (-1 : ℝ) ^ p * (-t) ^ c)
        =ᶠ[𝓝 x] paratlanTortHatvany p q := by
      filter_upwards [eventually_lt_nhds hneg] with t ht
      exact (paratlanTortHatvany_of_neg p q ht).symm
    have hval : c * paratlanTortHatvany p q x / x
        = (-1 : ℝ) ^ p * (-1 * c * (-x) ^ (c - 1)) := by
      rw [paratlanTortHatvany_of_neg p q hneg,
        Real.rpow_sub hx' c 1, Real.rpow_one]
      field_simp
      ring
    rw [hval]
    exact hH.congr_of_eventuallyEq heq.symm
  · -- pozitív `x`
    have hrp : HasDerivAt (fun t : ℝ => t ^ c) (c * x ^ (c - 1)) x :=
      Real.hasDerivAt_rpow_const (Or.inl (ne_of_gt hpos))
    have heq : (fun t : ℝ => t ^ c) =ᶠ[𝓝 x] paratlanTortHatvany p q := by
      filter_upwards [eventually_gt_nhds hpos] with t ht
      exact (paratlanTortHatvany_of_pos p q ht).symm
    have hval : c * paratlanTortHatvany p q x / x = c * x ^ (c - 1) := by
      rw [paratlanTortHatvany_of_pos p q hpos, Real.rpow_sub hpos c 1, Real.rpow_one]
      ring
    rw [hval]
    exact hrp.congr_of_eventuallyEq heq.symm

/-! ## 6.11.3. Tétel: l'Hospital-szabály a végtelenben -/

/-- A könyv „`+∞`-ben vett határérték” fogalma megegyezik a Mathlib
`Tendsto f atTop (𝓝 c)` fogalmával. -/
theorem hatarErtekVegtelenben_iff_tendsto (f : ℝ → ℝ) (c : ℝ) :
    HatarErtekVegtelenben f c ↔ Tendsto f atTop (𝓝 c) := by
  rw [Metric.tendsto_nhds]
  constructor
  · intro h ε hε
    obtain ⟨K, hK⟩ := h ε hε
    filter_upwards [eventually_gt_atTop K] with x hx
    simpa [Real.dist_eq] using hK x hx
  · intro h ε hε
    obtain ⟨K, hK⟩ := eventually_atTop.mp (h ε hε)
    exact ⟨K, fun x hx => by simpa [Real.dist_eq] using hK x hx.le⟩

/-- A könyv „`-∞`-ben vett határérték” fogalma megegyezik a
`Tendsto f atBot (𝓝 c)` fogalmával. -/
theorem hatarErtekMinuszVegtelenben_iff_tendsto (f : ℝ → ℝ) (c : ℝ) :
    HatarErtekMinuszVegtelenben f c ↔ Tendsto f atBot (𝓝 c) := by
  rw [Metric.tendsto_nhds]
  constructor
  · intro h ε hε
    obtain ⟨D, hD⟩ := h ε hε
    filter_upwards [eventually_lt_atBot D] with x hx
    simpa [Real.dist_eq] using hD x hx
  · intro h ε hε
    obtain ⟨D, hD⟩ := eventually_atBot.mp (h ε hε)
    exact ⟨D, fun x hx => by simpa [Real.dist_eq] using hD x hx.le⟩

/-- **6.11.3. Tétel (l'Hospital-szabály a `+∞`-ben, `0/0` eset).** Ha `f` és `g`
differenciálhatók az `(a, ∞)` intervallumon, `g'` ott nem tűnik el, továbbá
`lim_{x→∞} f(x) = lim_{x→∞} g(x) = 0`, akkor `lim_{x→∞} f'(x)/g'(x)` léte biztosítja,
hogy `lim_{x→∞} f(x)/g(x)` is létezik, és a két határérték egyenlő.

*Bizonyítás (a könyv gondolatmenete).* Az `x = 1/t` helyettesítéssel a `+∞`-beli
határérték a `t → 0+` féloldali határértékbe megy át, ahol a 6.11.1. Tétel
alkalmazható; a láncszabály szerinti `-1/t²` tényezők a hányadosban kiesnek. -/
theorem lhospital_vegtelenben {f g f' g' : ℝ → ℝ} {a L : ℝ}
    (hf : ∀ x ∈ Ioi a, HasDerivAt f (f' x) x) (hg : ∀ x ∈ Ioi a, HasDerivAt g (g' x) x)
    (hg0 : ∀ x ∈ Ioi a, g' x ≠ 0)
    (hftop : Tendsto f atTop (𝓝 0)) (hgtop : Tendsto g atTop (𝓝 0))
    (hlim : Tendsto (fun x => f' x / g' x) atTop (𝓝 L)) :
    Tendsto (fun x => f x / g x) atTop (𝓝 L) :=
  HasDerivAt.lhopital_zero_atTop_on_Ioi hf hg hg0 hftop hgtop hlim

/-- **6.11.3. Tétel** a könyv határérték-fogalmával kimondva. -/
theorem lhospital_vegtelenben_hatarertek {f g f' g' : ℝ → ℝ} {a L : ℝ}
    (hf : ∀ x ∈ Ioi a, HasDerivAt f (f' x) x) (hg : ∀ x ∈ Ioi a, HasDerivAt g (g' x) x)
    (hg0 : ∀ x ∈ Ioi a, g' x ≠ 0)
    (hf0 : HatarErtekVegtelenben f 0) (hg0' : HatarErtekVegtelenben g 0)
    (hlim : HatarErtekVegtelenben (fun x => f' x / g' x) L) :
    HatarErtekVegtelenben (fun x => f x / g x) L := by
  rw [hatarErtekVegtelenben_iff_tendsto] at hf0 hg0' hlim ⊢
  exact lhospital_vegtelenben hf hg hg0 hf0 hg0' hlim

/-- **6.11.3. Tétel (l'Hospital-szabály a `-∞`-ben, `0/0` eset).** -/
theorem lhospital_minusz_vegtelenben {f g f' g' : ℝ → ℝ} {a L : ℝ}
    (hf : ∀ x ∈ Iio a, HasDerivAt f (f' x) x) (hg : ∀ x ∈ Iio a, HasDerivAt g (g' x) x)
    (hg0 : ∀ x ∈ Iio a, g' x ≠ 0)
    (hfbot : Tendsto f atBot (𝓝 0)) (hgbot : Tendsto g atBot (𝓝 0))
    (hlim : Tendsto (fun x => f' x / g' x) atBot (𝓝 L)) :
    Tendsto (fun x => f x / g x) atBot (𝓝 L) :=
  HasDerivAt.lhopital_zero_atBot_on_Iio hf hg hg0 hfbot hgbot hlim

/-- **6.11.3. Tétel** (`-∞`) a könyv határérték-fogalmával kimondva. -/
theorem lhospital_minusz_vegtelenben_hatarertek {f g f' g' : ℝ → ℝ} {a L : ℝ}
    (hf : ∀ x ∈ Iio a, HasDerivAt f (f' x) x) (hg : ∀ x ∈ Iio a, HasDerivAt g (g' x) x)
    (hg0 : ∀ x ∈ Iio a, g' x ≠ 0)
    (hf0 : HatarErtekMinuszVegtelenben f 0) (hg0' : HatarErtekMinuszVegtelenben g 0)
    (hlim : HatarErtekMinuszVegtelenben (fun x => f' x / g' x) L) :
    HatarErtekMinuszVegtelenben (fun x => f x / g x) L := by
  rw [hatarErtekMinuszVegtelenben_iff_tendsto] at hf0 hg0' hlim ⊢
  exact lhospital_minusz_vegtelenben hf hg hg0 hf0 hg0' hlim

end Leindler.Ch06
