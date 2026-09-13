/-
# Kategóriaelméleti olvasat

Ebben a fájlban a gyakorlatok mögötti *szerkezeti* (kategóriaelméleti) tartalmat
formalizáljuk: melyik kalkulus-feladat melyik általános kategóriaelméleti elv
konkrét esete.

A megfeleltetés:

| gyakorlat | kategóriaelméleti tartalom |
|---|---|
| 2.18 (injektívek kompozíciója) | monomorfizmusok kompozíciója `Type`-ban |
| 2.6 c, 2.7 (bijekció, inverz)  | izomorfizmus `Type`-ban, `Equiv` |
| 2.10-2.15 (kompozíció)         | a kategória asszociativitási + egység-axiómái |
| 1.5 (a szuprémum egyértelmű)   | univerzális objektum egyértelműsége (kolimit) |
| 1.4 (sup/inf)                  | `sSup ⊣ Iic` adjunkció a részbenrendezett kategóriában |
| 1.10 (Dirichlet-közelítés)     | `⌊·⌋ ⊣ ℤ ↪ ℝ` Galois-kapcsolat |
| 3.x (határérték)               | a szűrők kategóriája; `Tendsto` = morfizmus |
| 3.x (folytonosság)             | `Top` kategória: identitás és kompozíció |
| 4.2 (láncszabály)              | a derivált funktorialitása: `T(g∘f) = Tg ∘ Tf` |
-/
import Mathlib

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace Kalkulus1.Kategoria

open CategoryTheory Filter Topology

/-! ## 1. Monomorfizmus = injektív függvény (2.2, 2.6, 2.18) -/

/-- A `Type` kategóriában a monomorfizmusok pontosan az injektív függvények. -/
theorem mono_iff_inj {X Y : Type} (f : X ⟶ Y) : Mono f ↔ Function.Injective f :=
  CategoryTheory.mono_iff_injective f

/-- 2.18 kategóriaelméleti magja: monomorfizmusok kompozíciója monomorfizmus.
Ez tetszőleges kategóriában igaz — az injektivitásról szóló feladat ennek
`Type`-beli esete. -/
theorem mono_comp_mono {C : Type _} [Category C] {X Y Z : C} (f : X ⟶ Y) (g : Y ⟶ Z)
    [Mono f] [Mono g] : Mono (f ≫ g) := inferInstance

/-- Következmény: az injektivitás öröklődése a kompozícióra a monomorfizmus-elv
konkrét esete. -/
theorem inj_comp_of_mono {X Y Z : Type} (f : X → Y) (g : Y → Z)
    (hf : Function.Injective f) (hg : Function.Injective g) :
    Function.Injective (g ∘ f) := by
  have hfm : Mono (show X ⟶ Y from f) := (mono_iff_inj (show X ⟶ Y from f)).mpr hf
  have hgm : Mono (show Y ⟶ Z from g) := (mono_iff_inj (show Y ⟶ Z from g)).mpr hg
  have hm : Mono ((show X ⟶ Y from f) ≫ (show Y ⟶ Z from g)) :=
    mono_comp_mono (show X ⟶ Y from f) (show Y ⟶ Z from g)
  have h := (mono_iff_inj _).mp hm
  simpa [CategoryTheory.types_comp] using h

/-! ## 2. Izomorfizmus = bijekció (2.6 c, 2.7, 2.9) -/

/-- A `Type` kategóriában az izomorfizmusok pontosan a bijekciók. -/
theorem isIso_iff_bij {X Y : Type} (f : X ⟶ Y) : IsIso f ↔ Function.Bijective f :=
  CategoryTheory.isIso_iff_bijective f

/-- 2.7 A `f(x) = (x+1)/(x-1)` függvény involúció az `ℝ \ {1}` halmazon, tehát
önmaga inverze: olyan izomorfizmus, amely saját inverze (`f ≫ f = 𝟙`). -/
noncomputable def gyak_2_7_equiv : {x : ℝ // x ≠ 1} ≃ {x : ℝ // x ≠ 1} where
  toFun x := ⟨(x.1 + 1) / (x.1 - 1), by
    have h1 : x.1 - 1 ≠ 0 := sub_ne_zero.mpr x.2
    intro h
    rw [div_eq_one_iff_eq h1] at h
    linarith⟩
  invFun x := ⟨(x.1 + 1) / (x.1 - 1), by
    have h1 : x.1 - 1 ≠ 0 := sub_ne_zero.mpr x.2
    intro h
    rw [div_eq_one_iff_eq h1] at h
    linarith⟩
  left_inv := by
    rintro ⟨x, hx⟩
    have h1 : x - 1 ≠ 0 := sub_ne_zero.mpr hx
    apply Subtype.ext
    simp only
    field_simp
    ring
  right_inv := by
    rintro ⟨x, hx⟩
    have h1 : x - 1 ≠ 0 := sub_ne_zero.mpr hx
    apply Subtype.ext
    simp only
    field_simp
    ring

/-- Az involúció-tulajdonság: `f ∘ f = id`. -/
theorem gyak_2_7_involutiv :
    gyak_2_7_equiv.trans gyak_2_7_equiv = Equiv.refl _ := by
  ext x
  exact congrArg Subtype.val (gyak_2_7_equiv.left_inv x)

/-! ## 3. A kompozíció kategória-axiómái (2.10-2.15) -/

/-- A függvénykompozíció asszociatív — a kategória-axióma, amelyre minden
„számoljuk ki `f ∘ g ∘ h`-t” feladat épül. -/
theorem comp_assoc {A B C D : Type} (f : A → B) (g : B → C) (h : C → D) :
    (h ∘ g) ∘ f = h ∘ (g ∘ f) := rfl

/-- Az identitás a kompozíció egységeleme. -/
theorem id_comp {A B : Type} (f : A → B) : id ∘ f = f ∧ f ∘ id = f := ⟨rfl, rfl⟩

/-! ## 4. Univerzális tulajdonság: a szuprémum egyértelmű (1.5) -/

/-- Az univerzális objektum egyértelműségének elve részbenrendezett halmazban:
két legkisebb felső korlát szükségképpen egyenlő. Ez a „kolimit egyértelmű
izomorfizmus erejéig” állítás; részbenrendezésben az izomorfizmus egyenlőség. -/
theorem lub_unique {α : Type _} [PartialOrder α] {S : Set α} {a b : α}
    (ha : IsLUB S a) (hb : IsLUB S b) : a = b := ha.unique hb

/-- Ugyanez a legnagyobb alsó korlátra (limit / terminális objektum). -/
theorem glb_unique {α : Type _} [PartialOrder α] {S : Set α} {a b : α}
    (ha : IsGLB S a) (hb : IsGLB S b) : a = b := ha.unique hb

/-! ## 5. Adjunkció: `sSup ⊣ Iic` (1.4) -/

/-- A szuprémum-képzés balra adjungáltja a „főideál” hozzárendelésnek:
`sSup S ≤ a ↔ S ⊆ Iic a`. Pontosan ez a felső határ univerzális tulajdonsága. -/
theorem sSup_galois {α : Type _} [CompleteLattice α] (S : Set α) (a : α) :
    sSup S ≤ a ↔ S ⊆ Set.Iic a := by
  constructor
  · intro h x hx
    exact le_trans (le_sSup hx) h
  · intro h
    exact sSup_le fun x hx => h hx

/-- 1.10 háttere: az egészrész-függvény jobbra adjungáltja a `ℤ ↪ ℝ` beágyazásnak
(Galois-kapcsolat), és ez adja a racionális közelítés alapbecslését. -/
theorem floor_galois (z : ℤ) (x : ℝ) : (z : ℝ) ≤ x ↔ z ≤ ⌊x⌋ := (Int.le_floor).symm

/-- A Galois-kapcsolat közvetlen következménye: `x - 1 < ⌊x⌋ ≤ x`. -/
theorem floor_approx (x : ℝ) : x - 1 < ⌊x⌋ ∧ (⌊x⌋ : ℝ) ≤ x :=
  ⟨Int.sub_one_lt_floor x, Int.floor_le x⟩

/-! ## 6. Monoton függvény = funktor (1.4, 4.8) -/

/-- Egy részbenrendezett halmaz kategória, és egy monoton függvény funktor
a megfelelő kategóriák között. -/
noncomputable def monotoneFunctor {X Y : Type} [Preorder X] [Preorder Y] {f : X → Y}
    (hf : Monotone f) : CategoryTheory.Functor X Y := hf.functor

/-- Funktorok kompozíciója: monoton függvények kompozíciója monoton. -/
theorem monotone_comp {X Y Z : Type} [Preorder X] [Preorder Y] [Preorder Z]
    {f : X → Y} {g : Y → Z} (hf : Monotone f) (hg : Monotone g) : Monotone (g ∘ f) :=
  hg.comp hf

/-! ## 7. A szűrők kategóriája: a határérték mint morfizmus (3. feladatsor) -/

/-- Identitás-morfizmus a szűrők kategóriájában. -/
theorem tendsto_id' {α : Type _} (F : Filter α) : Tendsto id F F := tendsto_id

/-- Morfizmusok kompozíciója: a határértékek „behelyettesítési szabálya”
(pl. `lim sin(3x)/x` kiszámítása `u = 3x` helyettesítéssel) semmi más, mint
kompozíció a szűrők kategóriájában. -/
theorem tendsto_comp' {α β γ : Type _} {F : Filter α} {G : Filter β} {H : Filter γ}
    {f : α → β} {g : β → γ} (hf : Tendsto f F G) (hg : Tendsto g G H) :
    Tendsto (g ∘ f) F H := hg.comp hf

/-- A folytonosság pontosan az, hogy a függvény minden pontban „morfizmus”
a környezetszűrők között. -/
theorem continuous_iff_tendsto_nhds {f : ℝ → ℝ} :
    Continuous f ↔ ∀ x, Tendsto f (𝓝 x) (𝓝 (f x)) := continuous_iff_continuousAt

/-! ## 8. A `Top` kategória (folytonosság) -/

/-- Az identitás folytonos, és folytonos függvények kompozíciója folytonos:
ez a `Top` kategória két axiómája. -/
theorem top_category_axioms {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] {f : X → Y} {g : Y → Z} (hf : Continuous f) (hg : Continuous g) :
    Continuous (id : X → X) ∧ Continuous (g ∘ f) := ⟨continuous_id, hg.comp hf⟩

/-! ## 9. A derivált funktorialitása: a láncszabály (4.2) -/

/-- A láncszabály *funktor*-alakja: a differenciál (az érintőleképezés) megőrzi
a kompozíciót, `T(g ∘ f)ₓ = T g_{f(x)} ∘ T fₓ`. -/
theorem fderiv_functorial {f g : ℝ → ℝ} {x : ℝ}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g (f x)) :
    fderiv ℝ (g ∘ f) x = (fderiv ℝ g (f x)).comp (fderiv ℝ f x) :=
  fderiv_comp x hg hf

/-- A funktor másik axiómája: az identitás differenciálja az identitás. -/
theorem fderiv_id' (x : ℝ) : fderiv ℝ (id : ℝ → ℝ) x = ContinuousLinearMap.id ℝ ℝ :=
  fderiv_id

/-- Egydimenziós, „iskolás” alak: a láncszabály a deriváltak szorzata. -/
theorem lancszabaly {f g : ℝ → ℝ} {x u v : ℝ} (hf : HasDerivAt f u x)
    (hg : HasDerivAt g v (f x)) : HasDerivAt (g ∘ f) (v * u) x := hg.comp x hf

end Kalkulus1.Kategoria
