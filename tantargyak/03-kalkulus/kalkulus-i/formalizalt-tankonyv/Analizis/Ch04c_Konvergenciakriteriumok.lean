import Analizis.Ch04b_SorozatokMuveletek

/-!
# Leindler László: Analízis — 4. fejezet: Számsorozatok (4.14–4.17. szakasz)

A torlódási pont fogalma, a monoton korlátos sorozatok konvergenciája, az egymásba
skatulyázott intervallumok tétele, a Bolzano–Weierstrass-tétel, a Cauchy-féle
konvergenciakritérium, az `(1 + 1/n)ⁿ` sorozat határértéke, valamint a valós számsorok
alapfogalmai (32–44. oldal).
-/

namespace Leindler
namespace Ch04

open scoped BigOperators
open Filter Topology

/-! ## 4.14. A torlódási pont fogalma -/

/-- **4.14.1. Definíció.** Az `{aₙ}` sorozatnak az `A` szám *torlódási pontja*, ha `A`
bármely környezetébe beleesik a sorozatnak végtelen sok tagja.  (A "végtelen sok tag"
azt jelenti, hogy bármely `N` indexnél van későbbi olyan tag, amely a környezetbe esik.) -/
def TorlodasiPont (a : Sorozat) (A : ℝ) : Prop := ∀ r > 0, ∀ N : ℕ, ∃ n > N, |a n - A| < r

/-- **4.14.2. Definíció.** Az `{aₙ}` sorozatnak az `A` szám torlódási pontja, ha
kiválasztható az `{aₙ}` sorozatból egy `A`-hoz konvergáló részsorozat. -/
def TorlodasiPontReszsorozattal (a : Sorozat) (A : ℝ) : Prop :=
  ∃ φ : ℕ → ℕ, StrictMono φ ∧ HatarErtek (fun k => a (φ k)) A

/-- **4.14.3. Megjegyzés.** A limeszpont (határérték) mindig torlódási pont. -/
theorem hatarErtek_torlodasiPont {a : Sorozat} {A : ℝ} (h : HatarErtek a A) :
    TorlodasiPont a A := by
  intro r hr N
  obtain ⟨M, hM⟩ := h r hr
  exact ⟨max M N + 1, by omega, hM _ (by omega)⟩

/-- **4.14.4. Tétel.** A torlódási pont két definíciója ekvivalens.

*Bizonyítás.* `4.14.2. ⇒ 4.14.1.`: ha `a_{nₖ} → A`, akkor `A` bármely környezetébe
végtelen sok tagja beleesik a részsorozatnak, s ezek az eredeti sorozat tagjai is.
`4.14.1. ⇒ 4.14.2.`: `A`-nak vesszük az `1/(k+1)` sugarú környezeteit, mindegyikből
kiválasztunk egy olyan tagot, amelynek indexe nagyobb a korábban kiválasztottakénál;
az így kapott részsorozat `A`-hoz konvergál. -/
theorem torlodasiPont_iff (a : Sorozat) (A : ℝ) :
    TorlodasiPont a A ↔ TorlodasiPontReszsorozattal a A := by
  constructor
  · intro h
    have hcl : MapClusterPt A Filter.atTop a := by
      rw [mapClusterPt_iff_frequently]
      intro s hs
      obtain ⟨r, hr, hsub⟩ := Metric.mem_nhds_iff.mp hs
      rw [Filter.frequently_atTop]
      intro N
      obtain ⟨n, hn, hlt⟩ := h r hr N
      exact ⟨n, le_of_lt hn, hsub (by simpa [Real.dist_eq] using hlt)⟩
    obtain ⟨φ, hφ, htend⟩ := subseq_tendsto_of_neBot hcl
    exact ⟨φ, hφ, (hatarErtek_iff_tendsto _ _).mpr htend⟩
  · rintro ⟨φ, hφ, hlim⟩ r hr N
    obtain ⟨K, hK⟩ := hlim r hr
    refine ⟨φ (max K N + 1), ?_, hK _ (by omega)⟩
    exact lt_of_lt_of_le (by omega) (strictMono_id_le hφ _)

/-- **4.14.5. Tétel.** Bármely monoton és korlátos sorozat konvergens.  Ha a sorozat
növekedő, akkor a felső határához, ha csökkenő, az alsó határához konvergál.

*Bizonyítás (növekedő eset).* Legyen `A` a sorozat felső határa.  Ekkor `aₙ ≤ A` minden
`n`-re, és bármely `ε > 0` esetén `A - ε` már nem felső korlát, tehát van olyan `n₀`,
hogy `A - ε < a_{n₀}`.  A növekedés miatt `n > n₀`-ra `a_{n₀} ≤ aₙ`, így
`A - ε < aₙ ≤ A + ε`, azaz `|aₙ - A| < ε`. -/
theorem monoton_korlatos_konvergens_novekedo {a : Sorozat} {A : ℝ} (hmon : Novekedo a)
    (hsup : FelsoHatar a A) : HatarErtek a A := by
  intro ε hε
  have : ¬ (∀ n, a n ≤ A - ε) := by
    intro hcon
    have := hsup.2 (A - ε) hcon
    linarith
  push_neg at this
  obtain ⟨n₀, hn₀⟩ := this
  refine ⟨n₀, fun n hn => ?_⟩
  have h₁ : a n₀ ≤ a n := novekedo_le hmon (le_of_lt hn)
  have h₂ : a n ≤ A := hsup.1 n
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

/-- **4.14.5. Tétel (csökkenő eset).** -/
theorem monoton_korlatos_konvergens_csokkeno {a : Sorozat} {A : ℝ} (hmon : Csokkeno a)
    (hinf : AlsoHatar a A) : HatarErtek a A := by
  intro ε hε
  have : ¬ (∀ n, A + ε ≤ a n) := by
    intro hcon
    have := hinf.2 (A + ε) hcon
    linarith
  push_neg at this
  obtain ⟨n₀, hn₀⟩ := this
  refine ⟨n₀, fun n hn => ?_⟩
  have h₁ : a n ≤ a n₀ := csokkeno_le hmon (le_of_lt hn)
  have h₂ : A ≤ a n := hinf.1 n
  exact abs_lt.mpr ⟨by linarith, by linarith⟩

/-- **4.15.2. Tétel.** Ahhoz, hogy egy sorozat konvergens legyen, elegendő, hogy a
sorozat monoton és korlátos legyen. -/
theorem monoton_korlatos_konvergens {a : Sorozat} (hmon : Monoton a) (hkorl : Korlatos a) :
    Konvergens a := by
  rcases hmon with hnov | hcsokk
  · obtain ⟨A, hA⟩ := van_felso_hatar hkorl.2
    exact ⟨A, monoton_korlatos_konvergens_novekedo hnov hA⟩
  · obtain ⟨A, hA⟩ := van_also_hatar hkorl.1
    exact ⟨A, monoton_korlatos_konvergens_csokkeno hcsokk hA⟩

/-- **4.14.6. Tétel (egymásba skatulyázott zárt intervallumok).** Egymásba skatulyázott
zárt intervallumok sorozatának mindig van közös pontja.

*Bizonyítás.* A balvégpontok monoton növekedő, korlátos sorozatot alkotnak, így a
4.14.5. Tétel szerint konvergálnak a felső határukhoz, jelöljük ezt `α`-val.  Mivel
`αₖ ≤ βₗ` minden `k`, `ℓ`-re, `α` minden `Iₖ`-nak pontja. -/
theorem skatulyazott_intervallumok {α β : Sorozat} (hα : Novekedo α) (hβ : Csokkeno β)
    (hle : ∀ k, α k ≤ β k) : ∃ x : ℝ, ∀ k, α k ≤ x ∧ x ≤ β k := by
  have hαβ : ∀ k l : ℕ, α k ≤ β l := by
    intro k l
    have h₁ : α k ≤ α (max k l) := novekedo_le hα (le_max_left _ _)
    have h₂ : β (max k l) ≤ β l := csokkeno_le hβ (le_max_right _ _)
    exact le_trans h₁ (le_trans (hle _) h₂)
  obtain ⟨A, hA⟩ := van_felso_hatar (a := α) ⟨β 0, fun k => hαβ k 0⟩
  exact ⟨A, fun k => ⟨hA.1 k, hA.2 (β k) fun j => hαβ j k⟩⟩

/-- **4.14.6. Tétel (folytatás).** Ha az intervallumok hossza nullához tart, akkor csak
egy közös pontjuk van. -/
theorem skatulyazott_intervallumok_egyertelmu {α β : Sorozat} (hα : Novekedo α)
    (hβ : Csokkeno β) (hle : ∀ k, α k ≤ β k)
    (hhossz : HatarErtek (fun k => β k - α k) 0) :
    ∃! x : ℝ, ∀ k, α k ≤ x ∧ x ≤ β k := by
  obtain ⟨x, hx⟩ := skatulyazott_intervallumok hα hβ hle
  refine ⟨x, hx, fun y hy => ?_⟩
  by_contra hne
  have hdpos : 0 < |x - y| := abs_pos.mpr (sub_ne_zero.mpr (Ne.symm hne))
  obtain ⟨K, hK⟩ := hhossz |x - y| hdpos
  have h₁ := hx (K + 1)
  have h₂ := hy (K + 1)
  have h₃ := hK (K + 1) (by omega)
  have hβα : 0 ≤ β (K + 1) - α (K + 1) := by linarith [h₁.1, h₁.2]
  rw [sub_zero, abs_of_nonneg hβα] at h₃
  rcases abs_cases (x - y) with ⟨he, -⟩ | ⟨he, -⟩ <;> rw [he] at h₃ <;>
    linarith [h₁.1, h₁.2, h₂.1, h₂.2]

/-- **4.14.8. Tétel (Bolzano–Weierstrass).** Korlátos végtelen sorozatból kiválasztható
legalább egy konvergens részsorozat; más fogalmazásban: korlátos végtelen sorozatnak van
legalább egy torlódási pontja.

*Megjegyzés.* A könyv bizonyítása intervallumfelezéssel történik (a 4.14.6. Tételre
támaszkodva); itt ezt a klasszikus kompaktsági érvvel helyettesítjük: a sorozat egy
`[k, K]` zárt intervallumban halad, amely kompakt. -/
theorem bolzano_weierstrass {a : Sorozat} (h : Korlatos a) :
    ∃ A : ℝ, TorlodasiPontReszsorozattal a A := by
  obtain ⟨⟨k, hk⟩, ⟨K, hK⟩⟩ := h
  obtain ⟨A, -, φ, hφ, htend⟩ :=
    (isCompact_Icc (a := k) (b := K)).tendsto_subseq (x := a) fun n => ⟨hk n, hK n⟩
  exact ⟨A, φ, hφ, (hatarErtek_iff_tendsto _ _).mpr htend⟩

/-- **4.14.8. Tétel (a torlódási pontos megfogalmazásban).** -/
theorem bolzano_weierstrass_torlodasi {a : Sorozat} (h : Korlatos a) :
    ∃ A : ℝ, TorlodasiPont a A := by
  obtain ⟨A, hA⟩ := bolzano_weierstrass h
  exact ⟨A, (torlodasiPont_iff a A).mpr hA⟩

/-- **4.14.9. Tétel.** Ha egy korlátos sorozatnak csak egy torlódási pontja van, akkor
konvergens.

*Bizonyítás.* Indirekt: ha a sorozat nem tartana `A`-hoz, akkor volna olyan `ε₀ > 0`,
amelyre végtelen sok tagra `|aₙ - A| ≥ ε₀`.  Ezekből a tagokból álló (korlátos)
részsorozatnak a Bolzano–Weierstrass-tétel szerint volna egy torlódási pontja, amely
`A`-tól legalább `ε₀`-ra van, tehát a sorozatnak `A`-tól különböző torlódási pontja is
volna; ez ellentmond a feltevésnek.

(Megjegyzés: azt, hogy `A` maga is torlódási pont, nem kell külön feltenni: a
Bolzano–Weierstrass-tétel szerint van torlódási pont, s az a feltevés szerint `A`.) -/
theorem egy_torlodasi_pont_konvergens {a : Sorozat} {A : ℝ} (hkorl : Korlatos a)
    (hegy : ∀ B, TorlodasiPont a B → B = A) : HatarErtek a A := by
  by_contra hcon
  unfold HatarErtek at hcon
  push_neg at hcon
  obtain ⟨ε₀, hε₀, hmany⟩ := hcon
  have hfreq : ∃ᶠ n in Filter.atTop, ε₀ ≤ |a n - A| := by
    rw [Filter.frequently_atTop]
    intro N
    obtain ⟨n, hn, hge⟩ := hmany N
    exact ⟨n, le_of_lt hn, hge⟩
  obtain ⟨φ, hφ, hprop⟩ := Filter.extraction_of_frequently_atTop hfreq
  obtain ⟨⟨k, hk⟩, ⟨K, hK⟩⟩ := hkorl
  obtain ⟨B, -, ψ, hψ, htend⟩ :=
    (isCompact_Icc (a := k) (b := K)).tendsto_subseq (x := fun m => a (φ m))
      fun m => ⟨hk _, hK _⟩
  have hBlim : HatarErtek (fun j => a (φ (ψ j))) B := (hatarErtek_iff_tendsto _ _).mpr htend
  have hBtorl : TorlodasiPont a B := by
    refine (torlodasiPont_iff a B).mpr ⟨φ ∘ ψ, hφ.comp hψ, hBlim⟩
  have hBA : B = A := hegy B hBtorl
  have habs : HatarErtek (fun j => |a (φ (ψ j)) - A|) |B - A| := by
    have := hatarErtek_sub hBlim (allando_hatarerteke A)
    exact hatarErtek_abs this
  have : ε₀ ≤ |B - A| :=
    hatarErtek_le (a := fun _ => ε₀) (b := fun j => |a (φ (ψ j)) - A|)
      (allando_hatarerteke ε₀) habs (N₀ := 0) fun j _ => hprop (ψ j)
  rw [hBA, sub_self, abs_zero] at this
  linarith

/-! ## 4.15. Konvergenciakritériumok -/

/-- **4.15.1. Tétel.** A konvergencia szükséges feltétele a korlátosság. -/
theorem konvergencia_szukseges_korlatossag {a : Sorozat} (h : Konvergens a) : Korlatos a :=
  konvergens_korlatos h

/-- **Definíció (Cauchy-féle feltétel).** Bármely `ε > 0`-hoz megadható olyan `ν`
küszöbszám, hogy `n, m > ν` esetén `|aₙ - aₘ| < ε`. -/
def CauchyFeltetel (a : Sorozat) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n > N, ∀ m > N, |a n - a m| < ε

/-- A Cauchy-feltételt teljesítő sorozat korlátos.

*Bizonyítás (a könyv szerint).* Válasszuk `ε = 1`-et; ekkor `n > ν` esetén
`|aₙ - a_{ν+1}| < 1`, így minden `n`-re
`min(a₀, …, a_ν, a_{ν+1} - 1) ≤ aₙ ≤ max(a₀, …, a_ν, a_{ν+1} + 1)`. -/
theorem cauchy_korlatos {a : Sorozat} (h : CauchyFeltetel a) : Korlatos a := by
  obtain ⟨N, hN⟩ := h 1 one_pos
  refine ⟨⟨min (a (N + 1) - 1) ((Finset.range (N + 1)).inf' (by simp) a), fun n => ?_⟩,
    ⟨max (a (N + 1) + 1) ((Finset.range (N + 1)).sup' (by simp) a), fun n => ?_⟩⟩
  · rcases Nat.lt_or_ge N n with hlt | hge
    · have := abs_lt.mp (hN n hlt (N + 1) (by omega))
      exact le_trans (min_le_left _ _) (by linarith [this.1])
    · exact le_trans (min_le_right _ _) (Finset.inf'_le _ (by simp [hge]))
  · rcases Nat.lt_or_ge N n with hlt | hge
    · have := abs_lt.mp (hN n hlt (N + 1) (by omega))
      exact le_trans (by linarith [this.2]) (le_max_left _ _)
    · exact le_trans (Finset.le_sup' _ (by simp [hge])) (le_max_right _ _)

/-- **4.15.4. Tétel (Cauchy-féle konvergenciakritérium).** Ahhoz, hogy egy `{aₙ}` sorozat
konvergens legyen, szükséges és elegendő, hogy teljesítse a Cauchy-féle feltételt.

*Bizonyítás.* *Elegendőség:* a Cauchy-feltételből következik a korlátosság, így a
Bolzano–Weierstrass-tétel szerint kiválasztható egy `a_{nₖ} → A` konvergens részsorozat.
Ekkor `ε/2`-höz véve a Cauchy-feltétel `ν(ε/2)` küszöbszámát és a részsorozat `k₀`
küszöbszámát, `n > ν(ε/2)` esetén elég nagy `k`-ra
`|aₙ - A| ≤ |aₙ - a_{nₖ}| + |a_{nₖ} - A| < ε/2 + ε/2 = ε`.
*Szükségesség:* ha `aₙ → A`, akkor `ε/2`-höz van olyan `μ`, hogy `n > μ`-re
`|aₙ - A| < ε/2`, s így `n, m > μ`-re `|aₙ - aₘ| ≤ |aₙ - A| + |A - aₘ| < ε`. -/
theorem cauchy_kriterium (a : Sorozat) : Konvergens a ↔ CauchyFeltetel a := by
  constructor
  · rintro ⟨A, hA⟩ ε hε
    obtain ⟨μ, hμ⟩ := hA (ε / 2) (by linarith)
    refine ⟨μ, fun n hn m hm => ?_⟩
    have h₁ := hμ n hn
    have h₂ := hμ m hm
    calc |a n - a m| = |(a n - A) + (A - a m)| := by ring_nf
      _ ≤ |a n - A| + |A - a m| := Ch03.haromszog_egyenlotlenseg _ _
      _ = |a n - A| + |a m - A| := by rw [abs_sub_comm A (a m)]
      _ < ε := by linarith
  · intro h
    obtain ⟨A, φ, hφ, hlim⟩ := bolzano_weierstrass (cauchy_korlatos h)
    refine ⟨A, fun ε hε => ?_⟩
    obtain ⟨ν, hν⟩ := h (ε / 2) (by linarith)
    obtain ⟨k₀, hk₀⟩ := hlim (ε / 2) (by linarith)
    refine ⟨ν, fun n hn => ?_⟩
    set k := max k₀ ν + 1 with hk
    have hφk : φ k > ν := lt_of_lt_of_le (by omega) (strictMono_id_le hφ k)
    have h₁ : |a n - a (φ k)| < ε / 2 := hν n hn (φ k) hφk
    have h₂ : |a (φ k) - A| < ε / 2 := hk₀ k (by omega)
    calc |a n - A| = |(a n - a (φ k)) + (a (φ k) - A)| := by ring_nf
      _ ≤ |a n - a (φ k)| + |a (φ k) - A| := Ch03.haromszog_egyenlotlenseg _ _
      _ < ε := by linarith

/-! ## 4.16. Az `(1 + 1/n)ⁿ` sorozat határértéke -/

/-- Az `(1 + 1/n)ⁿ` sorozat monoton növekedő (`n ≥ 1`).

*Bizonyítás.* A Bernoulli-egyenlőtlenség (4.7.4. Tétel) alkalmazásával:
`(1 - 1/(n+1)²)^{n+1} ≥ 1 - (n+1)/(n+1)² = n/(n+1)`, és
`(1 + 1/(n+1))^{n+1} = (1 + 1/n)^{n+1} · (1 - 1/(n+1)²)^{n+1} ≥ (1 + 1/n)ⁿ`. -/
theorem e_sorozat_novekedo {n : ℕ} (hn : 1 ≤ n) :
    (1 + 1 / (n : ℝ)) ^ n ≤ (1 + 1 / ((n : ℝ) + 1)) ^ (n + 1) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by linarith
  set x : ℝ := 1 - 1 / ((n : ℝ) + 1) ^ 2 with hx
  have hxb : (n : ℝ) / ((n : ℝ) + 1) ≤ x ^ (n + 1) := by
    have hsmall : 1 / ((n : ℝ) + 1) ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]
      nlinarith
    have hb := bernoulli (α := -(1 / ((n : ℝ) + 1) ^ 2)) (by linarith) (n + 1)
    rw [show (1 : ℝ) + -(1 / ((n : ℝ) + 1) ^ 2) = x from by rw [hx]; ring] at hb
    push_cast at hb
    have e2 : (1 : ℝ) + ((n : ℝ) + 1) * -(1 / ((n : ℝ) + 1) ^ 2) = (n : ℝ) / ((n : ℝ) + 1) := by
      field_simp
      ring
    linarith
  have hid : (1 + 1 / ((n : ℝ) + 1)) = (1 + 1 / (n : ℝ)) * x := by
    rw [hx]
    field_simp
    ring
  have hpos : (0 : ℝ) < 1 + 1 / (n : ℝ) := by positivity
  calc (1 + 1 / (n : ℝ)) ^ n
      = (1 + 1 / (n : ℝ)) ^ (n + 1) * ((n : ℝ) / ((n : ℝ) + 1)) := by
        rw [pow_succ]
        field_simp
    _ ≤ (1 + 1 / (n : ℝ)) ^ (n + 1) * x ^ (n + 1) := by
        exact mul_le_mul_of_nonneg_left hxb (by positivity)
    _ = (1 + 1 / ((n : ℝ) + 1)) ^ (n + 1) := by rw [hid, mul_pow]

/-- **4.16.1. Tétel.** `lim (1 + 1/n)ⁿ = e`.

A könyv a konvergenciát a monotonitás és a korlátosság igazolásával (4.15.2. Tétel)
bizonyítja, és a határértéket nevezi el `e`-nek.  Itt a határértéket a Mathlib
`Real.exp 1` konstansával azonosítjuk. -/
theorem e_sorozat_hatarerteke :
    HatarErtek (fun n : ℕ => (1 + 1 / (n : ℝ)) ^ n) (Real.exp 1) := by
  rw [hatarErtek_iff_tendsto]
  simpa using Real.tendsto_one_add_div_pow_exp 1

/-- Az `(1 + 1/n)ⁿ` sorozat korlátos: minden `n ≥ 1` esetén `(1 + 1/n)ⁿ < 3`.

A könyv ezt a Newton-féle binomiális tétellel igazolja
(`(1+1/n)ⁿ < 1 + 1 + 1/2 + … + 1/2^{n-1} < 3`); itt a monotonitásból és a
határértékből következtetünk: a sorozat minden tagja legfeljebb a limesz, `e < 3`. -/
theorem e_sorozat_korlatos {n : ℕ} (hn : 1 ≤ n) : (1 + 1 / (n : ℝ)) ^ n < 3 := by
  have hmono : ∀ m : ℕ, n ≤ m → (1 + 1 / (n : ℝ)) ^ n ≤ (1 + 1 / (m : ℝ)) ^ m := by
    intro m hm
    induction m with
    | zero => omega
    | succ k ih =>
        rcases Nat.lt_or_ge n (k + 1) with hlt | hge
        · have hk : 1 ≤ k := by omega
          have hstep := e_sorozat_novekedo hk
          push_cast
          exact le_trans (ih (by omega)) hstep
        · have : n = k + 1 := by omega
          simp [this]
  have hle : (1 + 1 / (n : ℝ)) ^ n ≤ Real.exp 1 :=
    hatarErtek_le (a := fun _ => (1 + 1 / (n : ℝ)) ^ n)
      (b := fun m => (1 + 1 / (m : ℝ)) ^ m)
      (allando_hatarerteke _) e_sorozat_hatarerteke (N₀ := n) fun m hm => hmono m (le_of_lt hm)
  have : Real.exp 1 < 3 := by
    have := Real.exp_one_lt_d9
    linarith
  linarith

/-! ## 4.17. Valós számsorok -/

/-! **4.17.1. Definíció.** Az `a₁ + a₂ + ⋯ + aₙ + ⋯` valós tagokból álló kifejezést,
rövidebben `∑_{n=1}^∞ aₙ`-t, *végtelen valós számsornak* nevezzük. A sort tehát a tagjaiból
álló `{aₙ}` sorozat határozza meg; ezért a következőkben a sort magával a `Sorozat`
típusú `a` tagsorozattal adjuk meg. -/

/-- **4.17.2. Definíció.** A `∑ aᵢ` végtelen sor `n`-edik *részletösszege* az
`sₙ = a₀ + a₁ + … + a_{n-1}` véges összeg. -/
def Reszletosszeg (a : Sorozat) (n : ℕ) : ℝ := ∑ i ∈ Finset.range n, a i

/-- **4.17.3. Definíció.** A `∑ aᵢ` sort *konvergensnek* nevezzük, ha a
részletösszegeiből képzett sorozat konvergens. -/
def SorKonvergens (a : Sorozat) : Prop := Konvergens (Reszletosszeg a)

/-- **4.17.4. Definíció.** Konvergens sor összege a részletösszegek sorozatának
határértéke. -/
def SorOsszege (a : Sorozat) (S : ℝ) : Prop := HatarErtek (Reszletosszeg a) S

/-- "Nyilvánvaló, hogy `n ≥ 1` esetén `aₙ = sₙ₊₁ - sₙ`." -/
theorem tag_reszletosszegbol (a : Sorozat) (n : ℕ) :
    a n = Reszletosszeg a (n + 1) - Reszletosszeg a n := by
  unfold Reszletosszeg
  rw [Finset.sum_range_succ]
  ring

/-- A geometriai sor: ha `|q| < 1`, akkor `∑ qⁿ` konvergens és összege `1/(1-q)`. -/
theorem geometriai_sor {q : ℝ} (hq : |q| < 1) : SorOsszege (fun n => q ^ n) (1 / (1 - q)) := by
  have hq1 : q ≠ 1 := by
    intro h
    rw [h] at hq
    simp at hq
  have hkey : ∀ n, Reszletosszeg (fun n => q ^ n) n = (1 - q ^ n) / (1 - q) := by
    intro n
    unfold Reszletosszeg
    rw [geom_sum_eq hq1, show q ^ n - 1 = -(1 - q ^ n) from by ring,
      show q - 1 = -(1 - q) from by ring, neg_div_neg_eq]
  have h1 : HatarErtek (fun n => (1 - q ^ n) / (1 - q)) (1 / (1 - q)) := by
    have hsub : HatarErtek (fun n => 1 - q ^ n) 1 := by
      have := hatarErtek_sub (a := fun _ => (1 : ℝ)) (b := fun n => q ^ n)
        (allando_hatarerteke 1) (q_hatvany_nullahoz hq)
      simpa using this
    have := hatarErtek_const_mul (c := 1 / (1 - q)) hsub
    simpa [div_eq_mul_inv, mul_comm] using this
  intro ε hε
  obtain ⟨N, hN⟩ := h1 ε hε
  exact ⟨N, fun n hn => by rw [hkey n]; exact hN n hn⟩

end Ch04
end Leindler
