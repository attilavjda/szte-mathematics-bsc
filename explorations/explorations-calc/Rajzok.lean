/-
# Rajzos érvek — a képek Lean-beli megfelelői

Ez a fájl a `kalkulus_rajzos_gondolkodas.pdf` ábráihoz tartozó, gépileg ellenőrzött
állításokat gyűjti össze. Minden tétel neve mellett zárójelben az ábra témája áll.
A cél: minden rajz mögött legyen egy pontos, `sorry` nélkül bizonyított állítás,
hogy látszódjék, *mit* bizonyít a kép és mit nem.
-/
import Mathlib
import RequestProject.Szakasz1

set_option maxHeartbeats 1000000

namespace Kalkulus1.Rajzok

open Finset Filter Set

/-! ## 1. Logikai rajzok -/

/-- **Átlós tábla (1.2, Russell-paradoxon).** Rajzoljunk négyzetrácsot, sorai és oszlopai
a birkatulajdonosok; a `(b, a)` mezőbe tegyünk pipát, ha `b` vigyáz `a` birkáira.
A „jó falusi juhász” sora épp az átló *tagadása* volna — ilyen sor pedig nincs,
mert az átlón önmagával kerülne ellentmondásba. -/
theorem atlos_tabla {α : Type*} (R : α → α → Prop) : ¬ ∃ b, ∀ a, R b a ↔ ¬ R a a := by
  rintro ⟨b, hb⟩
  have := hb b
  tauto

/-- **Venn-diagram (1.3, 1.12).** A De Morgan-azonosság: a két kör metszetének komplementere
a két komplementer uniója. A rajz és a bizonyítás ugyanaz: egy pont hova esik. -/
theorem venn_de_morgan {α : Type*} (A B : Set α) : (A ∩ B)ᶜ = Aᶜ ∪ Bᶜ :=
  Set.compl_inter A B

/-- **Venn-diagram, tartalmazás (1.7 a).** „A néggyel oszthatók párosak” = a kisebb kör
a nagyobb belsejében van. -/
theorem venn_tartalmazas : {n : ℤ | (4 : ℤ) ∣ n} ⊆ {n : ℤ | (2 : ℤ) ∣ n} := by
  intro n hn
  exact dvd_trans ⟨2, rfl⟩ hn

/-- **Tabló-fa (3.1).** A határérték-állítás tagadása mechanikusan előáll: minden
kvantor megfordul, a záró egyenlőtlenség pedig az ellenkezőjére vált. Ez a szemantikus
tabló egyetlen ága: „van rossz `ε`, minden `δ`-hoz van tanú `x`”. -/
theorem tablo_nem_hatarertek (f : ℝ → ℝ) (a L : ℝ) :
    ¬ (∀ ε > 0, ∃ δ > 0, ∀ x, 0 < |x - a| → |x - a| < δ → |f x - L| < ε)
      ↔ ∃ ε > 0, ∀ δ > 0, ∃ x, 0 < |x - a| ∧ |x - a| < δ ∧ ε ≤ |f x - L| := by
  push_neg
  rfl

/-- **Játékfa / Skolem-függvény (3.1).** Az `∀ε ∃δ` állítás pontosan azt jelenti, hogy
van *nyerő stratégiánk*: egy `D` függvény, amely minden ellenfél-`ε`-ra megadja a
válasz-`δ`-t. A rajz: kétszintű fa, felül az ellenfél `ε`-ágai, alul a mi `δ`-válaszunk. -/
theorem jatek_strategia (f : ℝ → ℝ) (a L : ℝ) :
    (∀ ε > 0, ∃ δ > 0, ∀ x, |x - a| < δ → |f x - L| < ε)
      ↔ ∃ D : ℝ → ℝ, ∀ ε > 0, 0 < D ε ∧ ∀ x, |x - a| < D ε → |f x - L| < ε := by
  constructor
  · intro h
    choose! D hD hD' using h
    exact ⟨D, fun ε hε => ⟨hD ε hε, hD' ε hε⟩⟩
  · rintro ⟨D, hD⟩ ε hε
    exact ⟨D ε, (hD ε hε).1, (hD ε hε).2⟩

/-- **Skatulyaelv (1.10 a).** A `[0,1)` intervallumot `n+1` egyenlő rekeszre osztjuk, és a
`0·x, 1·x, …, n·x` törtrészeit rakjuk beléjük: két szám azonos rekeszbe esik, a különbségük
adja a jó közelítést. Rajz: számegyenes-szakasz rekeszekkel és pontokkal. -/
theorem skatulyaelv_kozelites (x : ℝ) {n : ℕ} (hn : 0 < n) :
    ∃ (r : ℤ) (s : ℕ), 0 < s ∧ s ≤ n ∧ |x - (r : ℝ) / (s : ℝ)| < 1 / ((n : ℝ) * (s : ℝ)) := by
  obtain ⟨j, k, hk0, hkn, hjk⟩ := Real.exists_int_int_abs_mul_sub_le x hn
  refine ⟨j, k.toNat, by omega, by omega, ?_⟩
  have hk : ((k.toNat : ℕ) : ℝ) = (k : ℝ) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) (Int.toNat_of_nonneg hk0.le)
  rw [hk]
  have hkpos : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk0
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
  have hdiff : x - (j : ℝ) / (k : ℝ) = ((k : ℝ) * x - (j : ℝ)) / (k : ℝ) := by
    field_simp
  rw [hdiff, abs_div, abs_of_pos hkpos, div_lt_div_iff₀ hkpos (by positivity)]
  have h1 : |(k : ℝ) * x - (j : ℝ)| ≤ 1 / ((n : ℝ) + 1) := hjk
  have h2 : 1 / ((n : ℝ) + 1) * ((n : ℝ) * (k : ℝ)) < 1 * (k : ℝ) := by
    rw [div_mul_eq_mul_div, one_mul, div_lt_iff₀ (by positivity)]
    nlinarith
  nlinarith [mul_le_mul_of_nonneg_right h1 (by positivity : (0:ℝ) ≤ (n : ℝ) * (k : ℝ))]

/-! ## 2. Számegyenes-rajzok -/

/-- **Előjelvonal (1.12 g).** Két gyöktényező szorzata pontosan a gyökök között negatív:
a számegyenesen a `+ − +` mintázat. -/
theorem elojel_vonal {a b : ℝ} (hab : a < b) (x : ℝ) :
    (x - a) * (x - b) < 0 ↔ a < x ∧ x < b := by
  constructor
  · intro h
    constructor <;> nlinarith [sq_nonneg (x - a), sq_nonneg (x - b)]
  · rintro ⟨h1, h2⟩
    nlinarith

/-- **Abszolút érték mint távolság (1.12 i).** `|x - 5| ≤ ε` = „`x` az `5` körüli
`ε` sugarú gátak között van”. -/
theorem tavolsag_savban (a ε x : ℝ) : |x - a| ≤ ε ↔ a - ε ≤ x ∧ x ≤ a + ε := by
  rw [abs_le]
  constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]

/-- **Fal-rajz (1.5).** Két „legkisebb felső gát” egymást is korlátozza, tehát egybeesnek:
a szuprémum egyértelműségének képe két, egymásnak feszülő fal. -/
theorem ket_fal_egybeesik {S : Set ℝ} {a b : ℝ} (ha : IsLUB S a) (hb : IsLUB S b) : a = b :=
  le_antisymm (ha.2 hb.1) (hb.2 ha.1)

/-! ## 3. Indukciós rajzok -/

/-- **Három piramis egy téglatestben (1.16).** A kirakós pontosan ezt az azonosságot
mondja ki: az első `n` négyzetszám háromszorosa a `(2n+1)`-szerese az első `n` szám
összegének. Ebből a Gauss-összeggel azonnal jön a zárt alak — indukció nélkül. -/
theorem negyzetszamok_kepe (n : ℕ) :
    3 * (∑ i ∈ Finset.range (n + 1), (i : ℝ) ^ 2)
      = (2 * (n : ℝ) + 1) * ∑ i ∈ Finset.range (n + 1), (i : ℝ) := by
  rw [Kalkulus1.Szakasz1.gyak_1_16, Kalkulus1.Szakasz1.gyak_1_14_a]
  ring

/-- **Gauss párosítása (1.14 a).** Két egymás mellé rajzolt lépcső egy `n × (n+1)`-es
téglalapot ad ki: az összeg kétszerese `n(n+1)`. -/
theorem gauss_teglalap (n : ℕ) :
    2 * (∑ i ∈ Finset.range (n + 1), (i : ℝ)) = (n : ℝ) * ((n : ℝ) + 1) := by
  rw [Kalkulus1.Szakasz1.gyak_1_14_a]
  ring

/-! ## 4. Függvénygrafikon-rajzok -/

/-- Egy valós függvény grafikonja a síkon. -/
def grafikon (f : ℝ → ℝ) : Set (ℝ × ℝ) := {p : ℝ × ℝ | p.2 = f p.1}

/-- **Vízszintes vonal teszt (2.2).** Injektív = minden vízszintes egyenes legfeljebb
egyszer metszi a grafikont. -/
theorem vizszintes_vonal_teszt (f : ℝ → ℝ) :
    Function.Injective f ↔ ∀ y : ℝ, ∀ p ∈ grafikon f, ∀ q ∈ grafikon f,
      p.2 = y → q.2 = y → p.1 = q.1 := by
  constructor
  · intro hf y p hp q hq hpy hqy
    exact hf (by rw [← hp, ← hq, hpy, hqy] : f p.1 = f q.1)
  · intro h x₁ x₂ hx
    exact h (f x₁) (x₁, f x₁) rfl (x₂, f x₂) rfl rfl hx.symm

/-- **Szürjektivitás vonalteszttel (2.2).** Szürjektív = *minden* vízszintes egyenes
metszi a grafikont. -/
theorem szurjektiv_vonal_teszt (f : ℝ → ℝ) :
    Function.Surjective f ↔ ∀ y : ℝ, ∃ p ∈ grafikon f, p.2 = y := by
  constructor
  · intro hf y
    obtain ⟨x, hx⟩ := hf y
    exact ⟨(x, f x), rfl, hx⟩
  · intro h y
    obtain ⟨p, hp, hpy⟩ := h y
    exact ⟨p.1, by rw [← hp, hpy]⟩

/-- **Tükrözés az `y = x` egyenesre (2.3).** Az inverz grafikonja az eredeti grafikon
tükörképe: a `Prod.swap` pontosan a papíron végzett átlós tükrözés. -/
theorem grafikon_tukrozes (e : ℝ ≃ ℝ) :
    Prod.swap '' grafikon (e : ℝ → ℝ) = grafikon (e.symm : ℝ → ℝ) := by
  ext p
  constructor
  · rintro ⟨q, hq, rfl⟩
    simp only [grafikon, Set.mem_setOf_eq] at hq ⊢
    simp [Prod.swap, hq]
  · intro hp
    refine ⟨(p.2, p.1), ?_, rfl⟩
    simp only [grafikon, Set.mem_setOf_eq] at hp ⊢
    simp [hp]

/-- **Involúció = tengelyesen szimmetrikus grafikon (2.7).** Az `f(x) = (x+1)/(x−1)`
grafikonja önmaga tükörképe az `y = x` egyenesre; ezért `f⁻¹ = f`. -/
theorem involucio_grafikon_szimmetrikus :
    Prod.swap '' {p : ℝ × ℝ | p.1 ≠ 1 ∧ p.2 = (p.1 + 1) / (p.1 - 1)}
      = {p : ℝ × ℝ | p.1 ≠ 1 ∧ p.2 = (p.1 + 1) / (p.1 - 1)} := by
  have kulcs : ∀ x : ℝ, x ≠ 1 → ((x + 1) / (x - 1) ≠ 1 ∧
      ((x + 1) / (x - 1) + 1) / ((x + 1) / (x - 1) - 1) = x) := by
    intro x hx
    have hx1 : x - 1 ≠ 0 := sub_ne_zero.mpr hx
    constructor
    · intro h
      rw [div_eq_one_iff_eq hx1] at h
      linarith
    · have h2 : (x + 1) / (x - 1) - 1 = 2 / (x - 1) := by field_simp; ring
      rw [h2]
      field_simp
      ring
  ext p
  constructor
  · rintro ⟨q, ⟨hq1, hq2⟩, rfl⟩
    obtain ⟨h1, h2⟩ := kulcs q.1 hq1
    refine ⟨?_, ?_⟩
    · simp only [Prod.fst_swap]
      rw [hq2]; exact h1
    · simp only [Prod.fst_swap, Prod.snd_swap]
      rw [hq2]; exact h2.symm
  · rintro ⟨hp1, hp2⟩
    obtain ⟨h1, h2⟩ := kulcs p.1 hp1
    refine ⟨(p.2, p.1), ⟨?_, ?_⟩, rfl⟩
    · rw [hp2]; exact h1
    · simp only
      rw [hp2, h2]

/-! ## 5. Pókháló-diagram (rekurzió) -/

/-- **Pókháló-diagram (1.18).** Ha egy `s` halmazon `f` a `c` fixpont felé `q`-szoros
arányban zsugorít, akkor az iteráció hibája mértani sorozatként megy nullába.
A rajz: az `y = f(x)` görbe és az `y = x` egyenes között lépcsőző pókháló. -/
theorem pokhalo_zsugorodas {f : ℝ → ℝ} {s : Set ℝ} {c q : ℝ} (hq : 0 ≤ q)
    (hmap : ∀ x ∈ s, f x ∈ s) (hcon : ∀ x ∈ s, |f x - c| ≤ q * |x - c|)
    {x₀ : ℝ} (hx₀ : x₀ ∈ s) (n : ℕ) :
    f^[n] x₀ ∈ s ∧ |f^[n] x₀ - c| ≤ q ^ n * |x₀ - c| := by
  induction n with
  | zero => simpa using hx₀
  | succ n ih =>
    obtain ⟨hmem, hbound⟩ := ih
    rw [Function.iterate_succ_apply']
    refine ⟨hmap _ hmem, ?_⟩
    calc |f (f^[n] x₀) - c| ≤ q * |f^[n] x₀ - c| := hcon _ hmem
      _ ≤ q * (q ^ n * |x₀ - c|) := by
          exact mul_le_mul_of_nonneg_left hbound hq
      _ = q ^ (n + 1) * |x₀ - c| := by ring

/-- 1.18. gyakorlat. Ha `1 < x₁ < 2` és `xₙ = −xₙ₋₁²/2 + xₙ₋₁ + 1`, akkor `n ≥ 3` esetén
`|xₙ − √2| < 1/2ⁿ`. A pókháló-diagram mutatja: a sorozat a `[11/8, 3/2]` csapdába esik,
és ott minden lépés felezi a `√2`-tól mért távolságot. -/
theorem gyak_1_18 (x : ℕ → ℝ) (h1 : 1 < x 1) (h2 : x 1 < 2)
    (hrec : ∀ n, 1 ≤ n → x (n + 1) = -(x n) ^ 2 / 2 + x n + 1)
    (n : ℕ) (hn : 3 ≤ n) : |x n - Real.sqrt 2| < 1 / 2 ^ n := by
  set c := Real.sqrt 2 with hc
  have hsq : c ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hcnn : 0 ≤ c := Real.sqrt_nonneg 2
  have hclow : 11 / 8 < c := by nlinarith
  have hchigh : c < 3 / 2 := by nlinarith
  -- első lépés: a `(1,2)` intervallumból a `(1, 3/2)` intervallumba jutunk
  have hx2 : 1 < x 2 ∧ x 2 < 3 / 2 := by
    have hr := hrec 1 le_rfl
    constructor <;> nlinarith [hr, mul_pos (sub_pos.mpr h1) (sub_pos.mpr h1)]
  -- második lépés: innen a `(11/8, 3/2)` csapdába
  have hx3 : 11 / 8 < x 3 ∧ x 3 < 3 / 2 := by
    have hr := hrec 2 (by norm_num)
    obtain ⟨ha, hb⟩ := hx2
    constructor <;> nlinarith [hr]
  -- a csapdában minden lépés felezi a `√2`-tól mért távolságot
  have key : ∀ y : ℝ, 11 / 8 < y → y < 3 / 2 →
      |(-y ^ 2 / 2 + y + 1) - c| ≤ (1 / 2) * |y - c| := by
    intro y hy1 hy2
    have hfac : (-y ^ 2 / 2 + y + 1) - c = (y - c) * (1 - (y + c) / 2) := by
      linear_combination (-1 / 2 : ℝ) * hsq
    rw [hfac, abs_mul]
    have hb : |1 - (y + c) / 2| ≤ 1 / 2 := by
      rw [abs_le]; constructor <;> linarith
    calc |y - c| * |1 - (y + c) / 2| ≤ |y - c| * (1 / 2) :=
          mul_le_mul_of_nonneg_left hb (abs_nonneg _)
      _ = (1 / 2) * |y - c| := by ring
  -- és a csapda zárt
  have inv : ∀ y : ℝ, 11 / 8 < y → y < 3 / 2 →
      11 / 8 < (-y ^ 2 / 2 + y + 1) ∧ (-y ^ 2 / 2 + y + 1) < 3 / 2 := by
    intro y ha hb
    constructor <;> nlinarith
  have main : ∀ m, 3 ≤ m → (11 / 8 < x m ∧ x m < 3 / 2 ∧ |x m - c| < 1 / 2 ^ m) := by
    intro m hm
    induction m, hm using Nat.le_induction with
    | base =>
      refine ⟨hx3.1, hx3.2, ?_⟩
      rw [abs_lt]
      norm_num
      constructor <;> linarith [hx3.1, hx3.2]
    | succ m hm ih =>
      obtain ⟨ha, hb, hcc⟩ := ih
      have hr := hrec m (by omega)
      obtain ⟨i1, i2⟩ := inv (x m) ha hb
      refine ⟨by rw [hr]; exact i1, by rw [hr]; exact i2, ?_⟩
      have hk := key (x m) ha hb
      rw [hr]
      calc |(-x m ^ 2 / 2 + x m + 1) - c| ≤ (1 / 2) * |x m - c| := hk
        _ < (1 / 2) * (1 / 2 ^ m) := by linarith
        _ = 1 / 2 ^ (m + 1) := by ring
  exact (main n hn).2.2

/-! ## 6. Egységkör-rajz -/

/-- **Terület-szendvics az egységkörön (3.7).** `0 < x < π/2` esetén
`sin x < x < tan x`: a háromszög, a körcikk és a nagyobb háromszög területe.
Innen a rendőrelvvel jön a `sin x / x → 1` határérték. -/
theorem egysegkor_szendvics {x : ℝ} (hx : 0 < x) (hx2 : x < Real.pi / 2) :
    Real.sin x < x ∧ x < Real.tan x :=
  ⟨Real.sin_lt hx, Real.lt_tan hx hx2⟩

/-- **Rendőrelv-rajz (3.7).** A szendvicsből: `cos x < sin x / x < 1` a `(0, π/2)`
intervallumon — két „rendőr” fogja közre a hányadost. -/
theorem rendorelv_sav {x : ℝ} (hx : 0 < x) (hx2 : x < Real.pi / 2) :
    Real.cos x < Real.sin x / x ∧ Real.sin x / x < 1 := by
  have hcos : 0 < Real.cos x := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hx2⟩
  obtain ⟨hs, ht⟩ := egysegkor_szendvics hx hx2
  constructor
  · rw [lt_div_iff₀ hx]
    rw [Real.tan_eq_sin_div_cos, lt_div_iff₀ hcos] at ht
    linarith
  · rw [div_lt_one hx]
    exact hs

/-! ## 7. Deriválás-rajzok -/

/-- **Szelő → érintő (4.1).** A derivált a különbségi hányados határértéke: a rajzon a
szelő meredeksége fordul át az érintő meredekségébe. -/
theorem szelo_hatarerteke (f : ℝ → ℝ) (a d : ℝ) (h : HasDerivAt f d a) :
    Tendsto (fun x => (f x - f a) / (x - a)) (nhdsWithin a {a}ᶜ) (nhds d) := by
  have hs := hasDerivAt_iff_tendsto_slope.mp h
  refine hs.congr (fun x => ?_)
  rw [slope_def_field]

end Kalkulus1.Rajzok
