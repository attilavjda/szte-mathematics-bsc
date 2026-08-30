import Mathlib

/-!
# Leindler László: Analízis — 5. fejezet: Egyváltozós függvények

## 5.1. Alapfogalmak

Ebben a fájlban a tankönyv 5.1. pontjának fogalmait és tételét formalizáljuk:
korlátosság, felső/alsó határ, szélső értékek, monotonitás, pontnál való
növekedés, konvexség/konkávság, inflexiós pont, páros és páratlan függvények.

A tankönyv az egyváltozós valós függvényt egy `𝒟 ⊆ ℝ` értelmezési tartományon
értelmezett hozzárendelésként vezeti be (5.1.1. Definíció). Lean-ben a
függvényt `f : ℝ → ℝ` alakban adjuk meg, az értelmezési tartományt pedig külön
`D : Set ℝ` halmazként kezeljük; minden fogalom `D`-re relativizált.
-/

namespace Leindler.Ch05

open Set

/-! ## 5.1.1. Definíció: függvény, értelmezési tartomány, értékkészlet -/

/-- **5.1.1. Definíció.** Az `f` függvény *értékkészlete* az értelmezési tartomány
pontjaihoz hozzárendelt számok összessége. -/
def Ertekkeszlet (f : ℝ → ℝ) (D : Set ℝ) : Set ℝ := f '' D

open scoped Classical in
/-- Példa a tankönyv 4. megadási módjára („utasítással”): a Dirichlet-függvény,
amely a racionális helyeken `1`, az irracionálisokon `0`. -/
noncomputable def dirichlet (x : ℝ) : ℝ := if (∃ q : ℚ, (q : ℝ) = x) then 1 else 0

/-! ## 5.1.2. Definíció: korlátosság -/

/-- **5.1.2. Definíció.** Az `f` függvény *felülről korlátos* a `D` halmazon, ha van
olyan `K` szám, hogy minden `x ∈ D`-re `f x ≤ K`. -/
def FelulrolKorlatos (f : ℝ → ℝ) (D : Set ℝ) : Prop := ∃ K : ℝ, ∀ x ∈ D, f x ≤ K

/-- **5.1.2. Definíció.** Az `f` függvény *alulról korlátos* a `D` halmazon, ha van
olyan `k` szám, hogy minden `x ∈ D` pontban `k ≤ f x`. -/
def AlulrolKorlatos (f : ℝ → ℝ) (D : Set ℝ) : Prop := ∃ k : ℝ, ∀ x ∈ D, k ≤ f x

/-- **5.1.2. Definíció.** Az `f` függvény *korlátos*, ha alulról és felülről is
korlátos. -/
def KorlatosFv (f : ℝ → ℝ) (D : Set ℝ) : Prop :=
  AlulrolKorlatos f D ∧ FelulrolKorlatos f D

/-- **5.1.2. Definíció (folytatás).** Ha `k ≤ f x ≤ K` minden `x ∈ D` pontban, akkor
`|f x| ≤ max (|k|) (|K|)`, azaz a korlátosság az abszolút érték korlátosságát jelenti.

*Bizonyítás (a könyv gondolatmenete).* Ha `f x ≥ 0`, akkor `|f x| = f x ≤ K ≤ |K|`;
ha `f x < 0`, akkor `|f x| = -f x ≤ -k ≤ |k|`. -/
theorem abs_le_max_of_bounds {f : ℝ → ℝ} {D : Set ℝ} {k K : ℝ}
    (hk : ∀ x ∈ D, k ≤ f x) (hK : ∀ x ∈ D, f x ≤ K) :
    ∀ x ∈ D, |f x| ≤ max |k| |K| := by
  intro x hx
  rcases le_total 0 (f x) with h | h
  · rw [abs_of_nonneg h]
    exact le_trans (le_trans (hK x hx) (le_abs_self K)) (le_max_right _ _)
  · rw [abs_of_nonpos h]
    have : -f x ≤ -k := neg_le_neg (hk x hx)
    exact le_trans (le_trans this (neg_le_abs k)) (le_max_left _ _)

/-- A korlátosság ekvivalens azzal, hogy `|f|` felülről korlátos. -/
theorem korlatosFv_iff_abs {f : ℝ → ℝ} {D : Set ℝ} :
    KorlatosFv f D ↔ ∃ M : ℝ, ∀ x ∈ D, |f x| ≤ M := by
  constructor
  · rintro ⟨⟨k, hk⟩, ⟨K, hK⟩⟩
    exact ⟨max |k| |K|, abs_le_max_of_bounds hk hK⟩
  · rintro ⟨M, hM⟩
    refine ⟨⟨-M, fun x hx => ?_⟩, ⟨M, fun x hx => ?_⟩⟩
    · exact neg_le_of_abs_le (hM x hx)
    · exact le_of_abs_le (hM x hx)

/-! ## 5.1.3. Definíció: a függvényértékek felső és alsó határa -/

/-- **5.1.3. Definíció.** A függvényértékek *felső határa* (szuprémuma) a
legkisebb felső korlát, azaz az értékkészlet szuprémuma. -/
noncomputable def FvFelsoHatar (f : ℝ → ℝ) (D : Set ℝ) : ℝ := sSup (Ertekkeszlet f D)

/-- **5.1.3. Definíció.** A függvényértékek *alsó határa* (infimuma) a legnagyobb
alsó korlát, azaz az értékkészlet infimuma. -/
noncomputable def FvAlsoHatar (f : ℝ → ℝ) (D : Set ℝ) : ℝ := sInf (Ertekkeszlet f D)

/-- A felső határ valóban felső korlát (a nemüres, felülről korlátos esetben). -/
theorem fvFelsoHatar_felso_korlat {f : ℝ → ℝ} {D : Set ℝ} (hK : FelulrolKorlatos f D) :
    ∀ x ∈ D, f x ≤ FvFelsoHatar f D := by
  obtain ⟨K, hKle⟩ := hK
  intro x hx
  refine le_csSup ⟨K, ?_⟩ ⟨x, hx, rfl⟩
  rintro y ⟨z, hz, rfl⟩
  exact hKle z hz

/-- A felső határ a legkisebb felső korlát. -/
theorem fvFelsoHatar_legkisebb {f : ℝ → ℝ} {D : Set ℝ} (hD : D.Nonempty)
    {K : ℝ} (hK : ∀ x ∈ D, f x ≤ K) : FvFelsoHatar f D ≤ K := by
  obtain ⟨x₀, hx₀⟩ := hD
  refine csSup_le ⟨f x₀, x₀, hx₀, rfl⟩ ?_
  rintro y ⟨z, hz, rfl⟩
  exact hK z hz

/-- Példa (a könyvből): az `y = -x²` függvény felülről korlátos, felső határa `0`. -/
theorem pelda_neg_sq_felso_hatar : FvFelsoHatar (fun x : ℝ => -x ^ 2) univ = 0 := by
  have h : Ertekkeszlet (fun x : ℝ => -x ^ 2) univ = Iic 0 := by
    ext y
    constructor
    · rintro ⟨z, -, rfl⟩
      simpa using neg_nonpos.2 (sq_nonneg z)
    · intro hy
      exact ⟨Real.sqrt (-y), mem_univ _, by
        have : Real.sqrt (-y) ^ 2 = -y := Real.sq_sqrt (by simpa using hy)
        simp [this]⟩
  rw [FvFelsoHatar, h, csSup_Iic]

/-! ## 5.1.4. Definíció: szélső értékek -/

/-- **5.1.4. Definíció.** Az `f` függvény *felveszi a maximumát*, ha van olyan
`x₁ ∈ D` hely, ahol értéke a felső határával egyenlő. -/
def FelveszMaximumat (f : ℝ → ℝ) (D : Set ℝ) : Prop :=
  ∃ x₁ ∈ D, f x₁ = FvFelsoHatar f D

/-- **5.1.4. Definíció.** Az `f` függvény *felveszi a minimumát*, ha van olyan
`x₂ ∈ D` hely, ahol értéke az alsó határával egyenlő. -/
def FelveszMinimumat (f : ℝ → ℝ) (D : Set ℝ) : Prop :=
  ∃ x₂ ∈ D, f x₂ = FvAlsoHatar f D

/-- **5.1.4. Definíció.** Az `f` függvénynek `x₀`-ban *helyi (lokális) maximuma* van,
ha `x₀`-nak van olyan környezete, amelybe eső, az értelmezési tartományhoz tartozó
`x` pontokra `f x ≤ f x₀`. -/
def HelyiMaximum (f : ℝ → ℝ) (D : Set ℝ) (x₀ : ℝ) : Prop :=
  ∃ δ > 0, ∀ x ∈ D, |x - x₀| < δ → f x ≤ f x₀

/-- **5.1.4. Definíció.** Az `f` függvénynek `x₀`-ban *helyi (lokális) minimuma* van. -/
def HelyiMinimum (f : ℝ → ℝ) (D : Set ℝ) (x₀ : ℝ) : Prop :=
  ∃ δ > 0, ∀ x ∈ D, |x - x₀| < δ → f x₀ ≤ f x

/-- **5.1.4. Definíció.** *Szigorú* helyi maximum: a függvény csak az `x₀` pontban
veszi fel a szélső értékét a környezetben. -/
def SzigoruHelyiMaximum (f : ℝ → ℝ) (D : Set ℝ) (x₀ : ℝ) : Prop :=
  ∃ δ > 0, ∀ x ∈ D, x ≠ x₀ → |x - x₀| < δ → f x < f x₀

/-- Szigorú helyi maximumból következik a (tágabb értelemben vett) helyi maximum. -/
theorem szigoruHelyiMaximum_helyiMaximum {f : ℝ → ℝ} {D : Set ℝ} {x₀ : ℝ}
    (h : SzigoruHelyiMaximum f D x₀) : HelyiMaximum f D x₀ := by
  obtain ⟨δ, hδ, h⟩ := h
  refine ⟨δ, hδ, fun x hx hxd => ?_⟩
  rcases eq_or_ne x x₀ with rfl | hne
  · exact le_rfl
  · exact (h x hx hne hxd).le

/-! ## 5.1.5. Definíció: monotonitás -/

/-- **5.1.5. Definíció.** Az `f` függvény *tágabb értelemben növekedő* a `D`
halmazon, ha `x₁ < x₂` esetén `f x₁ ≤ f x₂`. -/
def Novekedo (f : ℝ → ℝ) (D : Set ℝ) : Prop :=
  ∀ x₁ ∈ D, ∀ x₂ ∈ D, x₁ < x₂ → f x₁ ≤ f x₂

/-- **5.1.5. Definíció.** Az `f` függvény *tágabb értelemben csökkenő*. -/
def Csokkeno (f : ℝ → ℝ) (D : Set ℝ) : Prop :=
  ∀ x₁ ∈ D, ∀ x₂ ∈ D, x₁ < x₂ → f x₂ ≤ f x₁

/-- **5.1.5. Definíció.** Az `f` függvény *szigorúan növekedő*. -/
def SzigNovekedo (f : ℝ → ℝ) (D : Set ℝ) : Prop :=
  ∀ x₁ ∈ D, ∀ x₂ ∈ D, x₁ < x₂ → f x₁ < f x₂

/-- **5.1.5. Definíció.** Az `f` függvény *szigorúan csökkenő*. -/
def SzigCsokkeno (f : ℝ → ℝ) (D : Set ℝ) : Prop :=
  ∀ x₁ ∈ D, ∀ x₂ ∈ D, x₁ < x₂ → f x₂ < f x₁

/-- **5.1.5. Definíció.** *Monoton* függvény: növekedő vagy csökkenő. -/
def Monoton (f : ℝ → ℝ) (D : Set ℝ) : Prop := Novekedo f D ∨ Csokkeno f D

/-- A szigorúan növekedő függvény tágabb értelemben is növekedő. -/
theorem szigNovekedo_novekedo {f : ℝ → ℝ} {D : Set ℝ} (h : SzigNovekedo f D) :
    Novekedo f D := fun x₁ h₁ x₂ h₂ hlt => (h x₁ h₁ x₂ h₂ hlt).le

/-- A `D`-n értelmezett növekedés a Mathlib `MonotoneOn` fogalmával azonos. -/
theorem novekedo_iff_monotoneOn {f : ℝ → ℝ} {D : Set ℝ} :
    Novekedo f D ↔ MonotoneOn f D := by
  constructor
  · intro h x hx y hy hxy
    rcases eq_or_lt_of_le hxy with rfl | hlt
    · exact le_rfl
    · exact h x hx y hy hlt
  · intro h x hx y hy hxy
    exact h hx hy hxy.le

/-- A szigorú növekedés a Mathlib `StrictMonoOn` fogalmával azonos. -/
theorem szigNovekedo_iff_strictMonoOn {f : ℝ → ℝ} {D : Set ℝ} :
    SzigNovekedo f D ↔ StrictMonoOn f D :=
  ⟨fun h x hx y hy hxy => h x hx y hy hxy, fun h _ hx _ hy hxy => h hx hy hxy⟩

/-! ## 5.1.6. Definíció: pontnál való növekedés -/

/-- **5.1.6. Definíció.** Az `f` függvényt az `x₀` pontnál *növekedőnek* nevezzük,
ha van olyan környezete `x₀`-nak, hogy az ebbe eső összes `x₁ < x₀ < x₂`
pontokban `f x₁ < f x₀ < f x₂`. -/
def PontnalNovekedo (f : ℝ → ℝ) (x₀ : ℝ) : Prop :=
  ∃ δ > 0, ∀ x₁ x₂, |x₁ - x₀| < δ → |x₂ - x₀| < δ → x₁ < x₀ → x₀ < x₂ →
    f x₁ < f x₀ ∧ f x₀ < f x₂

/-- **5.1.6. Definíció.** Az `f` függvényt az `x₀` pontnál *csökkenőnek* nevezzük. -/
def PontnalCsokkeno (f : ℝ → ℝ) (x₀ : ℝ) : Prop :=
  ∃ δ > 0, ∀ x₁ x₂, |x₁ - x₀| < δ → |x₂ - x₀| < δ → x₁ < x₀ → x₀ < x₂ →
    f x₀ < f x₁ ∧ f x₂ < f x₀

/-- Egy mindenütt szigorúan növekedő függvény minden pontnál növekedő. -/
theorem szigNovekedo_pontnalNovekedo {f : ℝ → ℝ} (h : SzigNovekedo f univ) (x₀ : ℝ) :
    PontnalNovekedo f x₀ :=
  ⟨1, one_pos, fun x₁ x₂ _ _ h₁ h₂ =>
    ⟨h x₁ (mem_univ _) x₀ (mem_univ _) h₁, h x₀ (mem_univ _) x₂ (mem_univ _) h₂⟩⟩

/-! ## 5.1.7. Definíció: konvexség és konkávság -/

/-- A `(c, f c)` és `(d, f d)` pontokon átmenő húr (szelő) egyenletének jobb oldala:
`h(x) = f c + (f d - f c)/(d - c) · (x - c)`. -/
noncomputable def hur (f : ℝ → ℝ) (c d x : ℝ) : ℝ := f c + (f d - f c) / (d - c) * (x - c)

/-- A húr a másik végpontból felírva ugyanaz az egyenes:
`f d + (f d - f c)/(d - c) · (x - d) = hur f c d x`. -/
theorem hur_masik_alak {f : ℝ → ℝ} {c d : ℝ} (hcd : c < d) (x : ℝ) :
    f d + (f d - f c) / (d - c) * (x - d) = hur f c d x := by
  have h : d - c ≠ 0 := sub_ne_zero.2 (ne_of_gt hcd)
  rw [hur]; field_simp; ring

/-- A húr és a függvényérték különbsége a bal oldali szelőmeredekséggel kifejezve. -/
theorem hur_sub {f : ℝ → ℝ} {c d : ℝ} (hcd : c < d) (x : ℝ) :
    hur f c d x - f x = ((f d - f c) * (x - c) - (f x - f c) * (d - c)) / (d - c) := by
  have h : d - c ≠ 0 := sub_ne_zero.2 (ne_of_gt hcd)
  rw [hur]; field_simp; ring

/-- A húr és a függvényérték különbsége a jobb oldali szelőmeredekséggel kifejezve. -/
theorem hur_sub' {f : ℝ → ℝ} {c d : ℝ} (hcd : c < d) (x : ℝ) :
    hur f c d x - f x = ((f d - f x) * (d - c) - (f d - f c) * (d - x)) / (d - c) := by
  have h : d - c ≠ 0 := sub_ne_zero.2 (ne_of_gt hcd)
  rw [hur]; field_simp; ring

/-- **5.1.7. Definíció.** Az `f` függvény (görbéje) *konvex* az `I` halmazon, ha bármely
ívének minden pontja az ív végpontjait összekötő húr alatt vagy magán a húron van. -/
def KonvexGorbe (f : ℝ → ℝ) (I : Set ℝ) : Prop :=
  ∀ c ∈ I, ∀ d ∈ I, c < d → ∀ x ∈ Ioo c d, f x ≤ hur f c d x

/-- **5.1.7. Definíció.** Az `f` függvény (görbéje) *szigorúan konvex* az `I` halmazon,
ha bármely ívének minden pontja — a végpontok kivételével — a húr *alatt* van. -/
def SzigKonvexGorbe (f : ℝ → ℝ) (I : Set ℝ) : Prop :=
  ∀ c ∈ I, ∀ d ∈ I, c < d → ∀ x ∈ Ioo c d, f x < hur f c d x

/-- **5.1.7. Definíció.** Az `f` függvény (görbéje) *konkáv* az `I` halmazon. -/
def KonkavGorbe (f : ℝ → ℝ) (I : Set ℝ) : Prop :=
  ∀ c ∈ I, ∀ d ∈ I, c < d → ∀ x ∈ Ioo c d, hur f c d x ≤ f x

/-- **5.1.7. Definíció.** Az `f` függvény (görbéje) *szigorúan konkáv* az `I` halmazon. -/
def SzigKonkavGorbe (f : ℝ → ℝ) (I : Set ℝ) : Prop :=
  ∀ c ∈ I, ∀ d ∈ I, c < d → ∀ x ∈ Ioo c d, hur f c d x < f x

/-- Segédlemma: a húr alatt levés ekvivalens a bal oldali szelőmeredekségre vonatkozó
egyenlőtlenséggel. -/
theorem lt_hur_iff_slope {f : ℝ → ℝ} {c d x : ℝ} (hcx : c < x) (hxd : x < d) :
    f x < hur f c d x ↔ (f x - f c) / (x - c) < (f d - f c) / (d - c) := by
  have hxc : (0 : ℝ) < x - c := sub_pos.2 hcx
  have hdc : (0 : ℝ) < d - c := sub_pos.2 (hcx.trans hxd)
  rw [← sub_pos, hur_sub (hcx.trans hxd), div_pos_iff_of_pos_right hdc,
    div_lt_div_iff₀ hxc hdc]
  exact sub_pos

/-- Segédlemma: a húr alatt levés ekvivalens a jobb oldali szelőmeredekségre vonatkozó
egyenlőtlenséggel. -/
theorem lt_hur_iff_slope_right {f : ℝ → ℝ} {c d x : ℝ} (hcx : c < x) (hxd : x < d) :
    f x < hur f c d x ↔ (f d - f c) / (d - c) < (f d - f x) / (d - x) := by
  have hdx : (0 : ℝ) < d - x := sub_pos.2 hxd
  have hdc : (0 : ℝ) < d - c := sub_pos.2 (hcx.trans hxd)
  rw [← sub_pos, hur_sub' (hcx.trans hxd), div_pos_iff_of_pos_right hdc,
    div_lt_div_iff₀ hdc hdx]
  exact sub_pos

/-! ## 5.1.8. Tétel: a konvexség szelős jellemzése -/

/-- **5.1.8. Tétel.** Az `y = f(x)` `(a ≤ x ≤ b)` függvény akkor és csak akkor
szigorúan konvex, ha

`(f(x') - f(c))/(x' - c) < (f(d) - f(x''))/(d - x'')`   (1)

bármely `a ≤ c < x', x'' < d ≤ b` egyenlőtlenségeket teljesítő `c, d, x', x''`
pontokra teljesül.

*Bizonyítás (a könyv gondolatmenete).* A szükségességhez felírjuk a `(c, f(c))` és
`(d, f(d))` pontokon átmenő egyenes egyenletét kétféle alakban, `h₁` és `h₂`
formában. A szigorú konvexitás miatt `f(x') < h₁(x')`, innen
`(f(x') - f(c))/(x' - c) < (f(d) - f(c))/(d - c)`, hasonlóan `f(x'') < h₂(x'')`
miatt (mivel `x'' - d < 0`) `(f(d) - f(c))/(d - c) < (f(d) - f(x''))/(d - x'')`.
A tranzitivitás adja (1)-et. Az elegendőséghez `x' = x'' = x ∈ (c, d)` választással
`(f(x) - f(c))(d - x) < (f(d) - f(x))(x - c)` adódik, amit átrendezve
`f(x) < f(c) + (f(d) - f(c))/(d - c) · (x - c) = h₁(x)`, azaz a görbe minden pontja
a húr alatt van. -/
theorem szigKonvex_iff_szelo (f : ℝ → ℝ) (a b : ℝ) :
    SzigKonvexGorbe f (Icc a b) ↔
      ∀ c d x' x'' : ℝ, a ≤ c → c < x' → x' < d → c < x'' → x'' < d → d ≤ b →
        (f x' - f c) / (x' - c) < (f d - f x'') / (d - x'') := by
  constructor
  · -- szükségesség
    intro hconv c d x' x'' hac hcx' hx'd hcx'' hx''d hdb
    have hcd : c < d := hcx'.trans hx'd
    have hcI : c ∈ Icc a b := ⟨hac, le_trans hcd.le hdb⟩
    have hdI : d ∈ Icc a b := ⟨le_trans hac hcd.le, hdb⟩
    have h1 : (f x' - f c) / (x' - c) < (f d - f c) / (d - c) :=
      (lt_hur_iff_slope hcx' hx'd).1 (hconv c hcI d hdI hcd x' ⟨hcx', hx'd⟩)
    have h2 : (f d - f c) / (d - c) < (f d - f x'') / (d - x'') :=
      (lt_hur_iff_slope_right hcx'' hx''d).1 (hconv c hcI d hdI hcd x'' ⟨hcx'', hx''d⟩)
    exact h1.trans h2
  · -- elegendőség
    intro h c hc d hd hcd x hx
    obtain ⟨hcx, hxd⟩ := hx
    have key := h c d x x hc.1 hcx hxd hcx hxd hd.2
    have hxc : (0 : ℝ) < x - c := sub_pos.2 hcx
    have hdx : (0 : ℝ) < d - x := sub_pos.2 hxd
    have hdc : (0 : ℝ) < d - c := sub_pos.2 hcd
    rw [div_lt_div_iff₀ hxc hdx] at key
    refine (lt_hur_iff_slope hcx hxd).2 ?_
    rw [div_lt_div_iff₀ hxc hdc]
    -- a `d - c = (d - x) + (x - c)` felbontással az állítás lineárissá válik
    have e1 : (f x - f c) * (d - c) = (f x - f c) * (d - x) + (f x - f c) * (x - c) := by ring
    have e2 : (f d - f x) * (x - c) + (f x - f c) * (x - c) = (f d - f c) * (x - c) := by ring
    linarith

/-- A könyv szigorú konvexség-fogalma megegyezik a Mathlib `StrictConvexOn`
fogalmával egy `[a, b]` intervallumon. -/
theorem szigKonvexGorbe_iff_strictConvexOn (f : ℝ → ℝ) (a b : ℝ) :
    SzigKonvexGorbe f (Icc a b) ↔ StrictConvexOn ℝ (Icc a b) f := by
  rw [strictConvexOn_iff_slope_strict_mono_adjacent]
  constructor
  · intro hconv
    refine ⟨convex_Icc a b, fun x y z hx hz hxy hyz => ?_⟩
    have h := hconv x hx z hz (hxy.trans hyz) y ⟨hxy, hyz⟩
    have h1 : (f y - f x) / (y - x) < (f z - f x) / (z - x) :=
      (lt_hur_iff_slope hxy hyz).1 h
    have h2 : (f z - f x) / (z - x) < (f z - f y) / (z - y) :=
      (lt_hur_iff_slope_right hxy hyz).1 h
    exact h1.trans h2
  · rintro ⟨-, hslope⟩
    intro c hc d hd hcd x hx
    have h := hslope hc hd hx.1 hx.2
    -- a szelőmeredekségek adjacens monotonitásából adódik a húr alatt levés
    have hxc : (0 : ℝ) < x - c := sub_pos.2 hx.1
    have hdx : (0 : ℝ) < d - x := sub_pos.2 hx.2
    have hdc : (0 : ℝ) < d - c := sub_pos.2 hcd
    rw [div_lt_div_iff₀ hxc hdx] at h
    refine (lt_hur_iff_slope hx.1 hx.2).2 ?_
    rw [div_lt_div_iff₀ hxc hdc]
    have e1 : (f x - f c) * (d - c) = (f x - f c) * (d - x) + (f x - f c) * (x - c) := by ring
    have e2 : (f d - f x) * (x - c) + (f x - f c) * (x - c) = (f d - f c) * (x - c) := by ring
    linarith

/-! ## 5.1.9–5.1.10. Definíció: inflexiós pont -/

/-- **5.1.10. Definíció.** Egy `f` függvénynek `x₀`-ban *inflexiós pontja* van, ha
`x₀`-nak vannak olyan jobb és bal oldali környezetei, hogy az egyikben a függvény
konvex, a másikban konkáv. -/
def InflexiosPont (f : ℝ → ℝ) (x₀ : ℝ) : Prop :=
  ∃ δ > 0,
    (KonvexGorbe f (Ioo (x₀ - δ) x₀) ∧ KonkavGorbe f (Ioo x₀ (x₀ + δ))) ∨
    (KonkavGorbe f (Ioo (x₀ - δ) x₀) ∧ KonvexGorbe f (Ioo x₀ (x₀ + δ)))

/-! ## 5.1.11. Definíció: páros és páratlan függvények -/

/-- **5.1.11. Definíció.** Az `f` függvény *páros*, ha bármely `x` helyre
`f x = f (-x)`. -/
def ParosFv (f : ℝ → ℝ) : Prop := ∀ x : ℝ, f x = f (-x)

/-- **5.1.11. Definíció.** Az `f` függvény *páratlan*, ha `f (-x) = -f x`. -/
def ParatlanFv (f : ℝ → ℝ) : Prop := ∀ x : ℝ, f (-x) = -f x

/-- Példa: `x ↦ x²` páros függvény. -/
theorem paros_sq : ParosFv (fun x : ℝ => x ^ 2) := by intro x; simp

/-- Példa: `x ↦ x³` páratlan függvény. -/
theorem paratlan_cube : ParatlanFv (fun x : ℝ => x ^ 3) := by intro x; ring

/-- Páratlan függvény a `0` helyen (ha ott értelmezve van) `0` értéket vesz fel. -/
theorem paratlan_zero {f : ℝ → ℝ} (h : ParatlanFv f) : f 0 = 0 := by
  have := h 0
  simp at this
  linarith

end Leindler.Ch05
