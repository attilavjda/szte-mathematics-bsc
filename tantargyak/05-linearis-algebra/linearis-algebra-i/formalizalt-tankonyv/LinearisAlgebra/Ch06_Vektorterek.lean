import LinearisAlgebra.Ch05_Egyenletrendszerek

/-!
# Szabó László: Bevezetés a lineáris algebrába — 6. fejezet: Vektortér, altér, generálás

A jegyzet 6. fejezetének (32–37. oldal) formalizálása:

* **6.1. Definíció** — a vektortér-axiómák (6.1.1)–(6.1.8),
* **6.2. Példák** — mátrixok, elem-`n`-esek, sorozatok, függvények vektortere,
* **6.3. Tétel** — a nullvektor és az additív inverz egyértelműsége, `λ0 = 0v = 0`,
  `λv = 0 ⟹ λ = 0 ∨ v = 0`, `(-λ)v = λ(-v) = -(λv)`,
* **6.4. Definíció, 6.5. Tétel** — a vektorok különbsége és a rá vonatkozó szabályok,
* **6.6. Definíció, 6.7. Tétel** — altér; az altérkritérium; alterek metszete,
* **6.9. Definíció, 6.10. Tétel** — lineáris kombináció, generált altér `[X]`,
* **6.11. Definíció, 6.12. Tétel** — alterek összege, `U₁ + U₂ = [U₁ ∪ U₂]`.

A 6.1. Definíciót a `Vektorter` struktúra adja vissza *szó szerint* (a könyv nyolc
axiómájával); a 6.3. és 6.5. Tétel bizonyítása a könyv számolásait követi.  A további
pontokban — a jegyzet többi fejezetéhez hasonlóan — a Mathlib `Module T V` fogalmával
dolgozunk, hiszen a `modulVektorter` híd szerint minden modulus vektortér a könyv
értelmében is.
-/

namespace SzaboLinAlg
namespace Ch06

open scoped BigOperators

/-! ## 6.1. Definíció: a vektortér-axiómák -/

/-- **6.1. Definíció.** A `T` számtest feletti *vektortér*: egy `V` halmaz egy
összeadással és a `T` elemeivel való szorzással, melyekre teljesülnek a
(6.1.1)–(6.1.8) vektortér-axiómák. -/
structure Vektorter (T : Type*) [Field T] (V : Type*) where
  /-- A vektorok összeadása. -/
  osszeg : V → V → V
  /-- Skalárral való szorzás. -/
  skalarszoros : T → V → V
  /-- (6.1.1) az összeadás kommutatív. -/
  osszeg_kommutativ : ∀ u v, osszeg u v = osszeg v u
  /-- (6.1.2) az összeadás asszociatív. -/
  osszeg_asszociativ : ∀ u v w, osszeg (osszeg u v) w = osszeg u (osszeg v w)
  /-- (6.1.3) létezik egységelem az összeadásra nézve (a nullvektor). -/
  nullvektor : V
  /-- (6.1.3) `u + 0 = u`. -/
  osszeg_nullvektor : ∀ u, osszeg u nullvektor = u
  /-- (6.1.4) minden vektornak van additív inverze. -/
  additiv_inverz : ∀ v, ∃ v', osszeg v v' = nullvektor
  /-- (6.1.5) `λ(u + v) = λu + λv`. -/
  skalar_osszeg : ∀ (l : T) (u v : V),
    skalarszoros l (osszeg u v) = osszeg (skalarszoros l u) (skalarszoros l v)
  /-- (6.1.6) `(λ + μ)u = λu + μu`. -/
  osszeg_skalar : ∀ (l m : T) (u : V),
    skalarszoros (l + m) u = osszeg (skalarszoros l u) (skalarszoros m u)
  /-- (6.1.7) `(λμ)u = λ(μu)`. -/
  skalar_asszociativ : ∀ (l m : T) (u : V),
    skalarszoros (l * m) u = skalarszoros l (skalarszoros m u)
  /-- (6.1.8) `1u = u`. -/
  egy_skalar : ∀ u, skalarszoros 1 u = u

namespace Vektorter

variable {T : Type*} [Field T] {V : Type*} (W : Vektorter T V)

/-- A nullvektor bal oldalról is egységelem: `0 + u = u`. -/
theorem nullvektor_osszeg (u : V) : W.osszeg W.nullvektor u = u := by
  rw [W.osszeg_kommutativ, W.osszeg_nullvektor]

/-! ### 6.3. Tétel -/

/-- **(6.3.1)** A `V`-n értelmezett összeadásra vonatkozóan egyetlen egységelem van.

*Bizonyítás.* Ha `o₁` és `o₂` is egységelem, akkor `o₁ = o₁ + o₂ = o₂`. -/
theorem egysegelem_egyertelmu {o₁ o₂ : V} (h₁ : ∀ u, W.osszeg u o₁ = u)
    (h₂ : ∀ u, W.osszeg u o₂ = u) : o₁ = o₂ := by
  have h : W.osszeg o₁ o₂ = o₁ := h₂ o₁
  have h' : W.osszeg o₂ o₁ = o₂ := h₁ o₂
  rw [W.osszeg_kommutativ] at h'
  rw [← h, h']

/-- **(6.3.2)** Minden vektornak egyetlen additív inverze van.

*Bizonyítás.* `u₁ = u₁ + 0 = u₁ + (v + u₂) = (u₁ + v) + u₂ = 0 + u₂ = u₂`. -/
theorem additiv_inverz_egyertelmu {v u₁ u₂ : V} (h₁ : W.osszeg v u₁ = W.nullvektor)
    (h₂ : W.osszeg v u₂ = W.nullvektor) : u₁ = u₂ := by
  calc u₁ = W.osszeg u₁ W.nullvektor := (W.osszeg_nullvektor u₁).symm
    _ = W.osszeg u₁ (W.osszeg v u₂) := by rw [h₂]
    _ = W.osszeg (W.osszeg u₁ v) u₂ := (W.osszeg_asszociativ _ _ _).symm
    _ = W.osszeg (W.osszeg v u₁) u₂ := by rw [W.osszeg_kommutativ u₁ v]
    _ = W.osszeg W.nullvektor u₂ := by rw [h₁]
    _ = u₂ := W.nullvektor_osszeg u₂

/-- Egyszerűsítési szabály: `w + u = w + v` esetén `u = v`. -/
theorem osszeg_bal_egyszerusites {w u v : V} (h : W.osszeg w u = W.osszeg w v) : u = v := by
  obtain ⟨w', hw'⟩ := W.additiv_inverz w
  have h1 : W.osszeg w' (W.osszeg w u) = W.osszeg w' (W.osszeg w v) := by rw [h]
  rw [← W.osszeg_asszociativ, ← W.osszeg_asszociativ, W.osszeg_kommutativ w' w, hw',
    W.nullvektor_osszeg, W.nullvektor_osszeg] at h1
  exact h1

/-- **(6.3.3)** `λ0 = 0`.

*Bizonyítás (a könyv szerint).*
`λ0 = λ0 + 0 = λ0 + (λ0 + (-λ0)) = (λ0 + λ0) + (-λ0) = λ(0 + 0) + (-λ0) = λ0 + (-λ0) = 0`. -/
theorem skalar_nullvektor (l : T) :
    W.skalarszoros l W.nullvektor = W.nullvektor := by
  obtain ⟨z, hz⟩ := W.additiv_inverz (W.skalarszoros l W.nullvektor)
  calc W.skalarszoros l W.nullvektor
      = W.osszeg (W.skalarszoros l W.nullvektor) W.nullvektor :=
        (W.osszeg_nullvektor _).symm
    _ = W.osszeg (W.skalarszoros l W.nullvektor)
          (W.osszeg (W.skalarszoros l W.nullvektor) z) := by rw [hz]
    _ = W.osszeg (W.osszeg (W.skalarszoros l W.nullvektor)
          (W.skalarszoros l W.nullvektor)) z := (W.osszeg_asszociativ _ _ _).symm
    _ = W.osszeg (W.skalarszoros l (W.osszeg W.nullvektor W.nullvektor)) z := by
        rw [W.skalar_osszeg]
    _ = W.osszeg (W.skalarszoros l W.nullvektor) z := by rw [W.osszeg_nullvektor]
    _ = W.nullvektor := hz

/-- **(6.3.3)** `0v = 0`.

*Bizonyítás (a könyv szerint).*
`0v = 0v + 0 = 0v + (0v + (-0v)) = (0v + 0v) + (-0v) = (0 + 0)v + (-0v) = 0v + (-0v) = 0`. -/
theorem nulla_skalar (v : V) : W.skalarszoros 0 v = W.nullvektor := by
  obtain ⟨z, hz⟩ := W.additiv_inverz (W.skalarszoros 0 v)
  calc W.skalarszoros 0 v
      = W.osszeg (W.skalarszoros 0 v) W.nullvektor := (W.osszeg_nullvektor _).symm
    _ = W.osszeg (W.skalarszoros 0 v) (W.osszeg (W.skalarszoros 0 v) z) := by rw [hz]
    _ = W.osszeg (W.osszeg (W.skalarszoros 0 v) (W.skalarszoros 0 v)) z :=
        (W.osszeg_asszociativ _ _ _).symm
    _ = W.osszeg (W.skalarszoros (0 + 0) v) z := by rw [W.osszeg_skalar]
    _ = W.osszeg (W.skalarszoros 0 v) z := by norm_num
    _ = W.nullvektor := hz

/-- **(6.3.4)** Ha `λv = 0`, akkor `λ = 0` vagy `v = 0`.

*Bizonyítás.* Ha `λ ≠ 0`, akkor `v = 1v = (λ⁻¹λ)v = λ⁻¹(λv) = λ⁻¹0 = 0`. -/
theorem skalar_eq_nulla {l : T} {v : V} (h : W.skalarszoros l v = W.nullvektor) :
    l = 0 ∨ v = W.nullvektor := by
  rcases eq_or_ne l 0 with hl | hl
  · exact Or.inl hl
  · refine Or.inr ?_
    calc v = W.skalarszoros 1 v := (W.egy_skalar v).symm
      _ = W.skalarszoros (l⁻¹ * l) v := by rw [inv_mul_cancel₀ hl]
      _ = W.skalarszoros l⁻¹ (W.skalarszoros l v) := W.skalar_asszociativ _ _ _
      _ = W.skalarszoros l⁻¹ W.nullvektor := by rw [h]
      _ = W.nullvektor := W.skalar_nullvektor l⁻¹

/-- **(6.3.5)** `(-λ)v` a `λv` additív inverze.

*Bizonyítás.* `λv + (-λ)v = (λ + (-λ))v = 0v = 0`. -/
theorem ellentett_skalar (l : T) (v : V) :
    W.osszeg (W.skalarszoros l v) (W.skalarszoros (-l) v) = W.nullvektor := by
  rw [← W.osszeg_skalar, add_neg_cancel, W.nulla_skalar]

/-- **(6.3.5)** `λ(-v)` szintén a `λv` additív inverze.

*Bizonyítás.* `λv + λ(-v) = λ(v + (-v)) = λ0 = 0`. -/
theorem skalar_ellentett (l : T) {v v' : V} (h : W.osszeg v v' = W.nullvektor) :
    W.osszeg (W.skalarszoros l v) (W.skalarszoros l v') = W.nullvektor := by
  rw [← W.skalar_osszeg, h, W.skalar_nullvektor]

/-- **(6.3.5)** `(-λ)v = λ(-v)`: a két vektor megegyezik, hiszen mindkettő `λv`
additív inverze, az pedig (6.3.2) szerint egyértelmű. -/
theorem ellentett_skalar_eq (l : T) {v v' : V} (h : W.osszeg v v' = W.nullvektor) :
    W.skalarszoros (-l) v = W.skalarszoros l v' :=
  W.additiv_inverz_egyertelmu (W.ellentett_skalar l v) (W.skalar_ellentett l h)

/-! ### 6.4. Definíció, 6.5. Tétel -/

/-- **6.5. Tétel (első fele).** `λ(u - v) = λu - λv`, azaz ha `v'` a `v` additív
inverze, akkor `λ(u + v') = λu + (λv')`, és `λv'` a `λv` additív inverze. -/
theorem skalar_kulonbseg (l : T) (u : V) {v v' : V} (h : W.osszeg v v' = W.nullvektor) :
    W.skalarszoros l (W.osszeg u v')
        = W.osszeg (W.skalarszoros l u) (W.skalarszoros l v')
      ∧ W.osszeg (W.skalarszoros l v) (W.skalarszoros l v') = W.nullvektor :=
  ⟨W.skalar_osszeg l u v', W.skalar_ellentett l h⟩

/-- **6.5. Tétel (második fele).** `(λ - μ)u = λu - μu`, azaz `(λ - μ)u = λu + (-μ)u`,
és `(-μ)u` a `μu` additív inverze. -/
theorem kulonbseg_skalar (l m : T) (u : V) :
    W.skalarszoros (l - m) u = W.osszeg (W.skalarszoros l u) (W.skalarszoros (-m) u)
      ∧ W.osszeg (W.skalarszoros m u) (W.skalarszoros (-m) u) = W.nullvektor := by
  refine ⟨?_, W.ellentett_skalar m u⟩
  rw [← W.osszeg_skalar, sub_eq_add_neg]

end Vektorter

/-! ## 6.2. Példák -/

/-- Minden Mathlib-értelemben vett modulus vektortér a könyv 6.1. Definíciója szerint is.
Ez a híd teszi lehetővé, hogy a további pontokban a `Module T V` fogalommal dolgozzunk. -/
def modulVektorter (T : Type*) [Field T] (V : Type*) [AddCommGroup V] [Module T V] :
    Vektorter T V where
  osszeg u v := u + v
  skalarszoros l u := l • u
  osszeg_kommutativ := add_comm
  osszeg_asszociativ := add_assoc
  nullvektor := 0
  osszeg_nullvektor := add_zero
  additiv_inverz v := ⟨-v, add_neg_cancel v⟩
  skalar_osszeg := smul_add
  osszeg_skalar := add_smul
  skalar_asszociativ := mul_smul
  egy_skalar := one_smul T

/-- **(6.2.2)** A `T` feletti `m × n`-es mátrixok vektorteret alkotnak (2.3. Tétel). -/
def matrixVektorter (T : Type*) [Field T] (m n : ℕ) :
    Vektorter T (Ch02.Matrix' T m n) :=
  modulVektorter T _

/-- **(6.2.5)** A `T`-beli elemekből képezett elem-`n`-esek `Tⁿ` halmaza vektortér. -/
def tupleVektorter (T : Type*) [Field T] (n : ℕ) : Vektorter T (Fin n → T) :=
  modulVektorter T _

/-- **(6.2.3)** A valós számsorozatok vektorteret alkotnak `ℝ` felett. -/
noncomputable def sorozatVektorter : Vektorter ℝ (ℕ → ℝ) := modulVektorter ℝ _

/-- **(6.2.4)** A valós függvények `ℝ^ℝ` halmaza vektortér `ℝ` felett. -/
noncomputable def fuggvenyVektorter : Vektorter ℝ (ℝ → ℝ) := modulVektorter ℝ _

/-! ## 6.6. Definíció, 6.7. Tétel: alterek -/

variable {T : Type*} [Field T] {V : Type*} [AddCommGroup V] [Module T V]

/-- **6.6. Definíció + 6.7.2. altérkritérium.** A `V` vektortér nemüres `U`
részhalmaza *altér*, ha zárt az összeadásra és a skalárral való szorzásra. -/
def Alter (T : Type*) [Field T] {V : Type*} [AddCommGroup V] [Module T V]
    (U : Set V) : Prop :=
  U.Nonempty ∧ (∀ u ∈ U, ∀ v ∈ U, u + v ∈ U) ∧ (∀ l : T, ∀ u ∈ U, l • u ∈ U)

namespace Alter

variable {U : Set V}

/-- **(6.7.1)** Az altér tartalmazza a `V` nullvektorát: `0 = 0v ∈ U`. -/
theorem zero_mem (hU : Alter T U) : (0 : V) ∈ U := by
  obtain ⟨v, hv⟩ := hU.1
  have := hU.2.2 (0 : T) v hv
  rwa [zero_smul] at this

/-- **(6.7.1)** Az altér minden elemének `V`-beli additív inverzét is tartalmazza:
`-v = (-1)v ∈ U`. -/
theorem neg_mem (hU : Alter T U) {v : V} (hv : v ∈ U) : -v ∈ U := by
  have := hU.2.2 (-1 : T) v hv
  rwa [neg_one_smul] at this

theorem add_mem (hU : Alter T U) {u v : V} (hu : u ∈ U) (hv : v ∈ U) : u + v ∈ U :=
  hU.2.1 u hu v hv

theorem smul_mem (hU : Alter T U) (l : T) {v : V} (hv : v ∈ U) : l • v ∈ U :=
  hU.2.2 l v hv

end Alter

/-- **6.7.2.** Az alterek pontosan a Mathlib-értelemben vett részmodulusok. -/
theorem alter_iff_submodule (U : Set V) :
    Alter T U ↔ ∃ W : Submodule T V, (W : Set V) = U := by
  constructor
  · intro hU
    refine ⟨⟨⟨⟨U, fun {u v} hu hv => hU.2.1 u hu v hv⟩, hU.zero_mem⟩,
      fun {l v} hv => hU.2.2 l v hv⟩, rfl⟩
  · rintro ⟨W, rfl⟩
    exact ⟨⟨0, W.zero_mem⟩, fun _ hu _ hv => W.add_mem hu hv, fun _ _ hu => W.smul_mem _ hu⟩

/-- **(6.7.3)** Alterek metszete is altér. -/
theorem alter_inter {U₁ U₂ : Set V} (h₁ : Alter T U₁) (h₂ : Alter T U₂) :
    Alter T (U₁ ∩ U₂) := by
  refine ⟨⟨0, h₁.zero_mem, h₂.zero_mem⟩, ?_, ?_⟩
  · rintro u ⟨hu1, hu2⟩ v ⟨hv1, hv2⟩
    exact ⟨h₁.add_mem hu1 hv1, h₂.add_mem hu2 hv2⟩
  · rintro l u ⟨hu1, hu2⟩
    exact ⟨h₁.smul_mem l hu1, h₂.smul_mem l hu2⟩

/-- **(6.8.1)** Minden vektortérben `{0}` és `V` altér (*triviális alterek*). -/
theorem alter_zero : Alter T ({0} : Set V) :=
  ⟨⟨0, rfl⟩, by rintro u rfl v rfl; simp, by rintro l u rfl; simp⟩

theorem alter_univ : Alter T (Set.univ : Set V) :=
  ⟨⟨0, trivial⟩, fun _ _ _ _ => trivial, fun _ _ _ => trivial⟩

/-! ## 6.9. Definíció, 6.10. Tétel: lineáris kombináció és generált altér -/

/-- **6.9. Definíció.** Az `X ⊆ V` halmaz által *generált* altér: az `X`-beli vektorok
összes lineáris kombinációjának halmaza,
`[X] = {∑_{i=1}^{n} λᵢvᵢ : n ≥ 0, v₁,…,vₙ ∈ X, λ₁,…,λₙ ∈ T}`.
(A nulla tagú lineáris kombináció megállapodás szerint a nullvektor.) -/
def Generalt (T : Type*) [Field T] {V : Type*} [AddCommGroup V] [Module T V]
    (X : Set V) : Set V :=
  {v | ∃ (n : ℕ) (w : Fin n → V) (l : Fin n → T), (∀ i, w i ∈ X) ∧ v = ∑ i, l i • w i}

/-- Ha `U` altér, akkor `U` zárt az `U`-beli vektorok lineáris kombinációjára. -/
theorem alter_sum_mem {U : Set V} (hU : Alter T U) :
    ∀ (n : ℕ) (l : Fin n → T) (w : Fin n → V), (∀ i, w i ∈ U) → ∑ i, l i • w i ∈ U := by
  intro n
  induction n with
  | zero => intro l w _; simpa using hU.zero_mem
  | succ k ih =>
      intro l w hw
      rw [Fin.sum_univ_castSucc]
      exact hU.add_mem (ih (fun i => l i.castSucc) (fun i => w i.castSucc)
        (fun i => hw _)) (hU.smul_mem _ (hw _))

/-- **6.10. Tétel (első rész).** `[X]` altér `V`-ben. -/
theorem generalt_alter (X : Set V) : Alter T (Generalt T X) := by
  refine ⟨⟨0, ⟨0, Fin.elim0, Fin.elim0, (by intro i; exact i.elim0), by simp⟩⟩, ?_, ?_⟩
  · rintro u ⟨n, w, l, hw, rfl⟩ v ⟨m, w', l', hw', rfl⟩
    refine ⟨n + m, Fin.append w w', Fin.append l l', ?_, ?_⟩
    · refine Fin.addCases (fun j => ?_) (fun j => ?_)
      · simpa [Fin.append_left] using hw j
      · simpa [Fin.append_right] using hw' j
    · rw [Fin.sum_univ_add]
      simp [Fin.append_left, Fin.append_right]
  · rintro c u ⟨n, w, l, hw, rfl⟩
    refine ⟨n, w, fun i => c * l i, hw, ?_⟩
    rw [Finset.smul_sum]
    simp [mul_smul]

/-- **6.10. Tétel (második rész).** `X ⊆ [X]`, hiszen `v = 1v` egy tagú lineáris
kombináció. -/
theorem subset_generalt (X : Set V) : X ⊆ Generalt T X := by
  intro v hv
  exact ⟨1, fun _ => v, fun _ => 1, fun _ => hv, by simp⟩

/-- **6.10. Tétel (harmadik rész).** `[X]` a legszűkebb `X`-et tartalmazó altér: minden
`X`-et tartalmazó altér tartalmazza `[X]`-et. -/
theorem generalt_minimal {X U : Set V} (hU : Alter T U) (hXU : X ⊆ U) :
    Generalt T X ⊆ U := by
  rintro v ⟨n, w, l, hw, rfl⟩
  exact alter_sum_mem hU n l w (fun i => hXU (hw i))

/-- **6.10. Tétel.** Ha `X ⊆ Y`, akkor `[X] ⊆ [Y]`. -/
theorem generalt_mono {X Y : Set V} (h : X ⊆ Y) : Generalt T X ⊆ Generalt T Y :=
  generalt_minimal (generalt_alter Y) (h.trans (subset_generalt Y))

/-- **6.10. Tétel.** `[[X]] = [X]`. -/
theorem generalt_idem (X : Set V) : Generalt T (Generalt T X) = Generalt T X :=
  Set.Subset.antisymm
    (generalt_minimal (generalt_alter X) (subset_refl _))
    (subset_generalt _)

/-- A generált altér megegyezik a Mathlib `Submodule.span` fogalmával. -/
theorem generalt_eq_span (X : Set V) : Generalt T X = (Submodule.span T X : Set V) := by
  refine Set.Subset.antisymm (generalt_minimal ?_ Submodule.subset_span) ?_
  · exact (alter_iff_submodule (T := T) _).2 ⟨Submodule.span T X, rfl⟩
  · intro v hv
    obtain ⟨W, hW⟩ := (alter_iff_submodule (T := T) (Generalt T X)).1 (generalt_alter X)
    have hle : Submodule.span T X ≤ W := by
      rw [Submodule.span_le, hW]
      exact subset_generalt X
    show v ∈ Generalt T X
    rw [← hW]
    exact hle hv

/-- Ha `[X] = V`, akkor `X` *generátorrendszer* a `V` vektortérben. -/
def Generatorrendszer (T : Type*) [Field T] {V : Type*} [AddCommGroup V] [Module T V]
    (X : Set V) : Prop := Generalt T X = Set.univ

/-! ## 6.11. Definíció, 6.12. Tétel: alterek összege -/

/-- **6.11. Definíció.** Az `U₁` és `U₂` alterek *összege*:
`U₁ + U₂ = {u₁ + u₂ : u₁ ∈ U₁, u₂ ∈ U₂}`. -/
def AlterOsszeg (U₁ U₂ : Set V) : Set V :=
  {v | ∃ u₁ ∈ U₁, ∃ u₂ ∈ U₂, v = u₁ + u₂}

/-- **6.12. Tétel (első rész).** Alterek összege is altér.

*Bizonyítás.* `(u₁ + u₂) + (v₁ + v₂) = (u₁ + v₁) + (u₂ + v₂)` és
`λ(u₁ + u₂) = λu₁ + λu₂`. -/
theorem alterOsszeg_alter {U₁ U₂ : Set V} (h₁ : Alter T U₁) (h₂ : Alter T U₂) :
    Alter T (AlterOsszeg U₁ U₂) := by
  refine ⟨⟨0, 0, h₁.zero_mem, 0, h₂.zero_mem, by simp⟩, ?_, ?_⟩
  · rintro u ⟨u₁, hu₁, u₂, hu₂, rfl⟩ v ⟨v₁, hv₁, v₂, hv₂, rfl⟩
    exact ⟨u₁ + v₁, h₁.add_mem hu₁ hv₁, u₂ + v₂, h₂.add_mem hu₂ hv₂, by abel⟩
  · rintro l u ⟨u₁, hu₁, u₂, hu₂, rfl⟩
    exact ⟨l • u₁, h₁.smul_mem l hu₁, l • u₂, h₂.smul_mem l hu₂, by rw [smul_add]⟩

/-- **6.12. Tétel (második rész).** `U₁ + U₂ = [U₁ ∪ U₂]`.

*Bizonyítás.* `U₁ ∪ U₂ ⊆ U₁ + U₂` (mert `0` mindkét altérben benne van), és `U₁ + U₂`
altér, ezért `[U₁ ∪ U₂] ⊆ U₁ + U₂`; fordítva `u₁ + u₂ ∈ [U₁ ∪ U₂]`, mert a generált
altér zárt az összeadásra. -/
theorem alterOsszeg_eq_generalt {U₁ U₂ : Set V} (h₁ : Alter T U₁) (h₂ : Alter T U₂) :
    AlterOsszeg U₁ U₂ = Generalt T (U₁ ∪ U₂) := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro v ⟨u₁, hu₁, u₂, hu₂, rfl⟩
    exact (generalt_alter (U₁ ∪ U₂)).add_mem
      (subset_generalt _ (Or.inl hu₁)) (subset_generalt _ (Or.inr hu₂))
  · refine generalt_minimal (alterOsszeg_alter h₁ h₂) ?_
    rintro v (hv | hv)
    · exact ⟨v, hv, 0, h₂.zero_mem, by simp⟩
    · exact ⟨0, h₁.zero_mem, v, hv, by simp⟩

end Ch06
end SzaboLinAlg
