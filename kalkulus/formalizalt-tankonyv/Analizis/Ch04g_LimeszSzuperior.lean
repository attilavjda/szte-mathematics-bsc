import Analizis.Ch04f_NevezetesHatarertekek

/-!
# Leindler László: Analízis — 4.14.10–4.15.3: limesz szuperior és limesz inferior

Ez a modul a 4.14. szakasz hátralévő részét formalizálja (35–38. oldal):

* **4.14.10. Tétel** ‑ korlátos sorozatnak van legnagyobb és legkisebb torlódási pontja,
* **4.14.12. Definíció** ‑ limesz szuperior és limesz inferior,
* **4.14.13. Tétel** ‑ korlátos sorozat akkor és csak akkor konvergál, ha
  `lim sup aₙ = lim inf aₙ`,
* a `lim sup (aₙ + bₙ) ≤ lim sup aₙ + lim sup bₙ` és
  `lim inf aₙ + lim inf bₙ ≤ lim inf (aₙ + bₙ)` egyenlőtlenségek (a könyv (1) és (2)
  képlete, amelyeket a szerző gyakorlásra szán), a `(-1)ⁿ`, `(-1)ⁿ⁺¹` ellenpélda, valamint
  az az állítás, hogy ha az egyik sorozat konvergens, akkor egyenlőség áll.

A **4.15.1.** és a **4.15.2. Tétel** (a korlátosság szükséges, a monotonitás és
korlátosság elegendő feltétel) a `Ch04c_Konvergenciakriteriumok` modulban szerepel
(`konvergencia_szukseges_korlatossag`, `monoton_korlatos_konvergens`); a **4.15.3. Tétel**
a 4.14.13. Tétel átfogalmazása, a **4.15.4. Tétel** (Cauchy-kritérium) szintén a `Ch04c`
modulban van (`cauchy_kriterium`).
-/

namespace Leindler
namespace Ch04

open scoped BigOperators

/-! ## Segédfogalom: a `Lₙ = sup_{k ≥ n} aₖ` és `ℓₙ = inf_{k ≥ n} aₖ` sorozatok -/

/-- A sorozat `n`-edik tagjától kezdődő tagjainak halmaza. -/
def Vegtagok (a : Sorozat) (n : ℕ) : Set ℝ := {x | ∃ k, n ≤ k ∧ a k = x}

theorem vegtagok_nonempty (a : Sorozat) (n : ℕ) : (Vegtagok a n).Nonempty :=
  ⟨a n, ⟨n, le_refl n, rfl⟩⟩

theorem vegtagok_bddAbove {a : Sorozat} (h : FelulrolKorlatos a) (n : ℕ) :
    BddAbove (Vegtagok a n) := by
  obtain ⟨K, hK⟩ := h
  exact ⟨K, fun x hx => by obtain ⟨k, -, rfl⟩ := hx; exact hK k⟩

theorem vegtagok_bddBelow {a : Sorozat} (h : AlulrolKorlatos a) (n : ℕ) :
    BddBelow (Vegtagok a n) := by
  obtain ⟨k₀, hk₀⟩ := h
  exact ⟨k₀, fun x hx => by obtain ⟨k, -, rfl⟩ := hx; exact hk₀ k⟩

/-- A könyv `Lₙ = sup_{k ≥ n} aₖ` sorozata. -/
noncomputable def SupTagok (a : Sorozat) (n : ℕ) : ℝ := sSup (Vegtagok a n)

/-- A könyv `ℓₙ = inf_{k ≥ n} aₖ` sorozata. -/
noncomputable def InfTagok (a : Sorozat) (n : ℕ) : ℝ := sInf (Vegtagok a n)

theorem le_supTagok {a : Sorozat} (h : FelulrolKorlatos a) {n k : ℕ} (hk : n ≤ k) :
    a k ≤ SupTagok a n :=
  le_csSup (vegtagok_bddAbove h n) ⟨k, hk, rfl⟩

theorem supTagok_le {a : Sorozat} {n : ℕ} {c : ℝ} (hc : ∀ k, n ≤ k → a k ≤ c) :
    SupTagok a n ≤ c :=
  csSup_le (vegtagok_nonempty a n) (by rintro x ⟨k, hk, rfl⟩; exact hc k hk)

/-- `Lₙ` csökkenő: minél nagyobb `n`, annál kevesebb tagra veszünk szuprémumot. -/
theorem supTagok_csokkeno {a : Sorozat} (h : FelulrolKorlatos a) : Csokkeno (SupTagok a) := by
  intro n
  exact supTagok_le fun k hk => le_supTagok h (le_trans (Nat.le_succ n) hk)

theorem supTagok_alulrol_korlatos {a : Sorozat} (hf : FelulrolKorlatos a)
    (ha : AlulrolKorlatos a) : AlulrolKorlatos (SupTagok a) := by
  obtain ⟨k₀, hk₀⟩ := ha
  exact ⟨k₀, fun n => le_trans (hk₀ n) (le_supTagok hf (le_refl n))⟩

/-- A szuprémum jellemző tulajdonsága: `Lₙ - ε` már nem felső korlát. -/
theorem exists_lt_supTagok (a : Sorozat) {n : ℕ} {ε : ℝ} (hε : 0 < ε) :
    ∃ k, n ≤ k ∧ SupTagok a n - ε < a k := by
  have hlt : SupTagok a n - ε < SupTagok a n := by linarith
  obtain ⟨x, hx, hxlt⟩ := exists_lt_of_lt_csSup (vegtagok_nonempty a n) hlt
  obtain ⟨k, hk, rfl⟩ := hx
  exact ⟨k, hk, hxlt⟩

/-! ## 4.14.12. Definíció — limesz szuperior és limesz inferior -/

/-- **4.14.12. Definíció.** Korlátos sorozat legnagyobb torlódási pontját a sorozat
*limesz szuperiorjának* nevezzük. -/
def LimeszSzuperior (a : Sorozat) (L : ℝ) : Prop :=
  TorlodasiPont a L ∧ ∀ B, TorlodasiPont a B → B ≤ L

/-- **4.14.12. Definíció.** Korlátos sorozat legkisebb torlódási pontját a sorozat
*limesz inferiorjának* nevezzük. -/
def LimeszInferior (a : Sorozat) (l : ℝ) : Prop :=
  TorlodasiPont a l ∧ ∀ B, TorlodasiPont a B → l ≤ B

/-- A limesz szuperior egyértelmű. -/
theorem limeszSzuperior_unicitas {a : Sorozat} {L L' : ℝ} (h : LimeszSzuperior a L)
    (h' : LimeszSzuperior a L') : L = L' :=
  le_antisymm (h'.2 L h.1) (h.2 L' h'.1)

/-- A limesz inferior egyértelmű. -/
theorem limeszInferior_unicitas {a : Sorozat} {l l' : ℝ} (h : LimeszInferior a l)
    (h' : LimeszInferior a l') : l = l' :=
  le_antisymm (h.2 l' h'.1) (h'.2 l h.1)

/-! ## 4.14.10. Tétel — a legnagyobb és a legkisebb torlódási pont létezése -/

/-- **4.14.10. Tétel (első fele).** Korlátos sorozatnak van legnagyobb torlódási pontja.

*Bizonyítás (a könyv bizonyítása).* Legyen `Lₙ = sup_{k ≥ n} aₖ`.  Nyilvánvaló, hogy
`Lₙ₊₁ ≤ Lₙ`, és mivel a sorozat korlátos, `{Lₙ}` is az, tehát a 4.14.5. Tétel szerint
`Lₙ → L` valamely `L`-hez.  Először azt mutatjuk meg, hogy `L` torlódási pont: adott
`ε > 0` mellett van olyan `ν₁`, hogy `n > ν₁` esetén `L ≤ Lₙ < L + ε`, továbbá `Lₙ`
definíciója szerint van olyan `kₙ ≥ n`, hogy `Lₙ - ε < a_{kₙ} ≤ Lₙ`, tehát
`L - ε < a_{kₙ} < L + ε`, azaz `(L-ε, L+ε)`-ba végtelen sok tag esik.  Ha volna `L`-nél
nagyobb `L*` torlódási pont, akkor `L < K < L*` mellett `Lₙ < K` már elég nagy `n`-re,
azaz `K`-nál nagyobb tagja a sorozatnak csak véges sok van, s így `L*` nem lehet
torlódási pont. -/
theorem letezik_limesz_szuperior {a : Sorozat} (h : Korlatos a) :
    ∃ L, LimeszSzuperior a L := by
  obtain ⟨hal, hfel⟩ := h
  obtain ⟨L, hL⟩ := van_also_hatar (supTagok_alulrol_korlatos hfel hal)
  have hLlim : HatarErtek (SupTagok a) L :=
    monoton_korlatos_konvergens_csokkeno (supTagok_csokkeno hfel) hL
  refine ⟨L, ?_, ?_⟩
  · -- `L` torlódási pont
    intro r hr N
    obtain ⟨N₁, hN₁⟩ := hLlim (r / 2) (by linarith)
    set n := max N₁ N + 1 with hn
    have hnN₁ : n > N₁ := by omega
    have habs := abs_lt.mp (hN₁ n hnN₁)
    obtain ⟨k, hk, hklt⟩ := exists_lt_supTagok a (n := n) (ε := r / 2) (by linarith)
    have hkle : a k ≤ SupTagok a n := le_supTagok hfel hk
    have hkN : k > N := lt_of_lt_of_le (by omega) hk
    refine ⟨k, hkN, ?_⟩
    rw [abs_lt]
    constructor <;> linarith [habs.1, habs.2]
  · -- `L` a legnagyobb torlódási pont
    intro B hB
    by_contra hBL
    push_neg at hBL
    set K := (L + B) / 2 with hK
    have hLK : L < K := by rw [hK]; linarith
    have hKB : K < B := by rw [hK]; linarith
    obtain ⟨N₂, hN₂⟩ := hLlim (K - L) (by linarith)
    have hlt : SupTagok a (N₂ + 1) < K := by
      have := abs_lt.mp (hN₂ (N₂ + 1) (by omega))
      linarith [this.2]
    obtain ⟨n, hnN, hnB⟩ := hB (B - K) (by linarith) (N₂ + 1)
    have hle : a n ≤ SupTagok a (N₂ + 1) := le_supTagok hfel (le_of_lt hnN)
    have := abs_lt.mp hnB
    linarith [this.1]

/-- A torlódási pont fogalma és a sorozat negáltja. -/
theorem torlodasiPont_neg {a : Sorozat} {A : ℝ} (h : TorlodasiPont a A) :
    TorlodasiPont (fun n => -a n) (-A) := by
  intro r hr N
  obtain ⟨n, hn, hlt⟩ := h r hr N
  refine ⟨n, hn, ?_⟩
  have : -a n - -A = -(a n - A) := by ring
  rw [this, abs_neg]
  exact hlt

/-- **4.14.10. Tétel (második fele).** Korlátos sorozatnak van legkisebb torlódási pontja.

*Bizonyítás.* A könyv megjegyzése szerint elég a `{-aₙ}` sorozatra alkalmazni az előző
állítást: `{-aₙ}` legnagyobb torlódási pontjának ellentettje `{aₙ}` legkisebb torlódási
pontja. -/
theorem letezik_limesz_inferior {a : Sorozat} (h : Korlatos a) :
    ∃ l, LimeszInferior a l := by
  have hneg : Korlatos (fun n => -a n) := by
    obtain ⟨⟨k, hk⟩, ⟨K, hK⟩⟩ := h
    exact ⟨⟨-K, fun n => by simpa using neg_le_neg (hK n)⟩,
      ⟨-k, fun n => by simpa using neg_le_neg (hk n)⟩⟩
  obtain ⟨L, hL, hLmax⟩ := letezik_limesz_szuperior hneg
  refine ⟨-L, ?_, ?_⟩
  · have := torlodasiPont_neg hL
    simpa using this
  · intro B hB
    have hBneg : TorlodasiPont (fun n => -a n) (-B) := torlodasiPont_neg hB
    linarith [hLmax (-B) hBneg]

/-! ## 4.14.13. Tétel -/

/-- Konvergens sorozat torlódási pontja csak a határértéke lehet. -/
theorem torlodasiPont_eq_hatarErtek {a : Sorozat} {A B : ℝ} (hA : HatarErtek a A)
    (hB : TorlodasiPont a B) : B = A := by
  obtain ⟨φ, hφ, hlim⟩ := (torlodasiPont_iff a B).mp hB
  have := reszsorozat_hatarerteke (a := a) (b := fun k => a (φ k)) ⟨φ, hφ, rfl⟩ hA
  exact hatarErtek_unicitas hlim this

/-- **4.14.13. Tétel (= 4.15.3. Tétel).** Egy korlátos sorozat akkor és csak akkor
konvergál, ha `lim sup aₙ = lim inf aₙ`.

*Bizonyítás.* Ha a sorozat konvergens, akkor minden torlódási pontja a határértékével
egyenlő, tehát a legnagyobb és a legkisebb torlódási pont is az.  Megfordítva, ha
`L = ℓ`, akkor minden `B` torlódási pontra `ℓ ≤ B ≤ L = ℓ`, azaz a sorozatnak csak egy
torlódási pontja van, s így a 4.14.9. Tétel szerint konvergens. -/
theorem konvergens_iff_limsup_eq_liminf {a : Sorozat} {L l : ℝ} (hkorl : Korlatos a)
    (hL : LimeszSzuperior a L) (hl : LimeszInferior a l) :
    Konvergens a ↔ L = l := by
  constructor
  · rintro ⟨A, hA⟩
    rw [torlodasiPont_eq_hatarErtek hA hL.1, torlodasiPont_eq_hatarErtek hA hl.1]
  · intro hLl
    refine ⟨L, egy_torlodasi_pont_konvergens hkorl fun B hB => ?_⟩
    have h₁ : B ≤ L := hL.2 B hB
    have h₂ : l ≤ B := hl.2 B hB
    linarith

/-! ## Példa: a `(-1)ⁿ` sorozat -/

theorem valto_elojel_torlodasi_pontok {B : ℝ} (h : TorlodasiPont (fun n : ℕ => (-1 : ℝ) ^ n) B) :
    B = 1 ∨ B = -1 := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨h1, h2⟩ := hcon
  set r := min |B - 1| |B + 1| with hr
  have hr1 : 0 < |B - 1| := abs_pos.mpr (sub_ne_zero.mpr h1)
  have hr2 : 0 < |B + 1| := abs_pos.mpr (by intro hz; exact h2 (by linarith [eq_neg_of_add_eq_zero_left hz]))
  have hrpos : 0 < r := lt_min hr1 hr2
  obtain ⟨n, -, hlt0⟩ := h r hrpos 0
  have hlt : |(-1 : ℝ) ^ n - B| < r := hlt0
  rcases Nat.even_or_odd n with he | ho
  · rw [he.neg_one_pow] at hlt
    have hrw : |(1 : ℝ) - B| = |B - 1| := abs_sub_comm 1 B
    rw [hrw] at hlt
    linarith [min_le_left |B - 1| |B + 1|]
  · rw [ho.neg_one_pow] at hlt
    have hrw : |(-1 : ℝ) - B| = |B + 1| := by
      rw [abs_sub_comm]
      congr 1
      ring
    rw [hrw] at hlt
    linarith [min_le_right |B - 1| |B + 1|]

/-- A `{(-1)ⁿ}` sorozat limesz szuperiorja `1`. -/
theorem limeszSzuperior_valto_elojel : LimeszSzuperior (fun n : ℕ => (-1 : ℝ) ^ n) 1 := by
  constructor
  · intro r hr N
    refine ⟨2 * N + 2, by omega, ?_⟩
    have : ((-1 : ℝ)) ^ (2 * N + 2) = 1 := by
      rw [pow_succ, pow_succ, pow_mul]
      norm_num
    simp only [this, sub_self, abs_zero]
    exact hr
  · intro B hB
    rcases valto_elojel_torlodasi_pontok hB with rfl | rfl
    · exact le_refl 1
    · norm_num

/-- A `{(-1)ⁿ}` sorozat limesz inferiorja `-1`. -/
theorem limeszInferior_valto_elojel : LimeszInferior (fun n : ℕ => (-1 : ℝ) ^ n) (-1) := by
  constructor
  · intro r hr N
    refine ⟨2 * N + 1, by omega, ?_⟩
    have : ((-1 : ℝ)) ^ (2 * N + 1) = -1 := by
      rw [pow_succ, pow_mul]
      norm_num
    simp only [this, sub_self, abs_zero]
    exact hr
  · intro B hB
    rcases valto_elojel_torlodasi_pontok hB with rfl | rfl
    · norm_num
    · exact le_refl (-1)

/-! ## A limesz szuperior és a limesz inferior szubadditivitása -/

/-- A könyv (1) képlete: `lim sup (aₙ + bₙ) ≤ lim sup aₙ + lim sup bₙ`.

*Bizonyítás.* Legyen `C` az `{aₙ + bₙ}` sorozat legnagyobb torlódási pontja; ekkor van
olyan részsorozat, amely `C`-hez tart.  Ebből a Bolzano–Weierstrass-tétel szerint
kiválasztható olyan további részsorozat, amely mentén `aₙ` konvergens, mondjuk `α`-hoz;
ekkor `α` az `{aₙ}` torlódási pontja, tehát `α ≤ A`.  Ugyanezen részsorozat mentén
`bₙ = (aₙ + bₙ) - aₙ → C - α`, tehát `C - α` a `{bₙ}` torlódási pontja, azaz `C - α ≤ B`.
Így `C ≤ α + B ≤ A + B`. -/
theorem limeszSzuperior_add_le {a b : Sorozat} {A B C : ℝ} (hka : Korlatos a)
    (hA : LimeszSzuperior a A) (hB : LimeszSzuperior b B)
    (hC : LimeszSzuperior (fun n => a n + b n) C) : C ≤ A + B := by
  obtain ⟨φ, hφ, hlim⟩ := (torlodasiPont_iff _ C).mp hC.1
  obtain ⟨⟨k, hk⟩, ⟨K, hK⟩⟩ := hka
  obtain ⟨α, -, ψ, hψ, htend⟩ :=
    (isCompact_Icc (a := k) (b := K)).tendsto_subseq (x := fun m => a (φ m))
      fun m => ⟨hk _, hK _⟩
  have halim : HatarErtek (fun j => a (φ (ψ j))) α := (hatarErtek_iff_tendsto _ _).mpr htend
  have hαtorl : TorlodasiPont a α :=
    (torlodasiPont_iff a α).mpr ⟨φ ∘ ψ, hφ.comp hψ, halim⟩
  have hαA : α ≤ A := hA.2 α hαtorl
  have hclim : HatarErtek (fun j => a (φ (ψ j)) + b (φ (ψ j))) C := by
    have hsub : HatarErtek (fun j => (fun m => a (φ m) + b (φ m)) (ψ j)) C :=
      reszsorozat_hatarerteke ⟨ψ, hψ, rfl⟩ hlim
    exact hsub
  have hblim : HatarErtek (fun j => b (φ (ψ j))) (C - α) := by
    have := hatarErtek_sub hclim halim
    simpa using this
  have hβtorl : TorlodasiPont b (C - α) :=
    (torlodasiPont_iff b (C - α)).mpr ⟨φ ∘ ψ, hφ.comp hψ, hblim⟩
  have hβB : C - α ≤ B := hB.2 _ hβtorl
  linarith

/-- A könyv (2) képlete: `lim inf aₙ + lim inf bₙ ≤ lim inf (aₙ + bₙ)`. -/
theorem le_limeszInferior_add {a b : Sorozat} {A B C : ℝ} (hka : Korlatos a)
    (hA : LimeszInferior a A) (hB : LimeszInferior b B)
    (hC : LimeszInferior (fun n => a n + b n) C) : A + B ≤ C := by
  obtain ⟨φ, hφ, hlim⟩ := (torlodasiPont_iff _ C).mp hC.1
  obtain ⟨⟨k, hk⟩, ⟨K, hK⟩⟩ := hka
  obtain ⟨α, -, ψ, hψ, htend⟩ :=
    (isCompact_Icc (a := k) (b := K)).tendsto_subseq (x := fun m => a (φ m))
      fun m => ⟨hk _, hK _⟩
  have halim : HatarErtek (fun j => a (φ (ψ j))) α := (hatarErtek_iff_tendsto _ _).mpr htend
  have hαtorl : TorlodasiPont a α :=
    (torlodasiPont_iff a α).mpr ⟨φ ∘ ψ, hφ.comp hψ, halim⟩
  have hAα : A ≤ α := hA.2 α hαtorl
  have hclim : HatarErtek (fun j => a (φ (ψ j)) + b (φ (ψ j))) C :=
    reszsorozat_hatarerteke ⟨ψ, hψ, rfl⟩ hlim
  have hblim : HatarErtek (fun j => b (φ (ψ j))) (C - α) := by
    have := hatarErtek_sub hclim halim
    simpa using this
  have hβtorl : TorlodasiPont b (C - α) :=
    (torlodasiPont_iff b (C - α)).mpr ⟨φ ∘ ψ, hφ.comp hψ, hblim⟩
  have hBβ : B ≤ C - α := hB.2 _ hβtorl
  linarith

/-- **Ellenpélda** (a könyv példája): `aₙ = (-1)ⁿ`, `bₙ = (-1)ⁿ⁺¹` esetén `aₙ + bₙ = 0`,
tehát `lim sup (aₙ + bₙ) = 0 < 2 = lim sup aₙ + lim sup bₙ`, azaz (1)-ben szigorú
egyenlőtlenség is állhat. -/
theorem limeszSzuperior_add_strict :
    LimeszSzuperior (fun n : ℕ => (-1 : ℝ) ^ n + (-1 : ℝ) ^ (n + 1)) 0 := by
  have hzero : (fun n : ℕ => (-1 : ℝ) ^ n + (-1 : ℝ) ^ (n + 1)) = fun _ : ℕ => (0 : ℝ) := by
    funext n
    rw [pow_succ]
    ring
  rw [hzero]
  constructor
  · exact hatarErtek_torlodasiPont (allando_hatarerteke 0)
  · intro B hB
    have := torlodasiPont_eq_hatarErtek (allando_hatarerteke (0 : ℝ)) hB
    exact le_of_eq this

/-- Ha az egyik sorozat konvergens, akkor (1)-ben egyenlőség áll:
`lim sup (aₙ + bₙ) = lim aₙ + lim sup bₙ`.

*Bizonyítás.* A `≤` irány az előző tétel (konvergens sorozat limesz szuperiorja a
határértéke).  A `≥` irányhoz: ha `b`-nek a `B` torlódási pontja, akkor a hozzá tartozó
részsorozat mentén `aₙ + bₙ → A + B`, tehát `A + B` az összegsorozat torlódási pontja,
így `A + B ≤ C`. -/
theorem limeszSzuperior_add_konvergens {a b : Sorozat} {A B C : ℝ} (hka : Korlatos a)
    (hA : HatarErtek a A) (hB : LimeszSzuperior b B)
    (hC : LimeszSzuperior (fun n => a n + b n) C) : C = A + B := by
  have hAsup : LimeszSzuperior a A :=
    ⟨hatarErtek_torlodasiPont hA, fun B' hB' => le_of_eq (torlodasiPont_eq_hatarErtek hA hB')⟩
  have hle : C ≤ A + B := limeszSzuperior_add_le hka hAsup hB hC
  obtain ⟨φ, hφ, hblim⟩ := (torlodasiPont_iff b B).mp hB.1
  have halim : HatarErtek (fun k => a (φ k)) A := reszsorozat_hatarerteke ⟨φ, hφ, rfl⟩ hA
  have hsum : HatarErtek (fun k => a (φ k) + b (φ k)) (A + B) := hatarErtek_add halim hblim
  have htorl : TorlodasiPont (fun n => a n + b n) (A + B) :=
    (torlodasiPont_iff _ (A + B)).mpr ⟨φ, hφ, hsum⟩
  have hge : A + B ≤ C := hC.2 _ htorl
  linarith

end Ch04
end Leindler
