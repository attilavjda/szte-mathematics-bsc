import Mathlib
import Analizis.Ch07b_TaylorFormula
import Analizis.Ch08b_KonvexsegInflexio

/-!
# Leindler László: Analízis — 8.7.3. Tétel

## Inflexiós pont magasabbrendű differenciálhányadosokkal

Ez a fájl a **8.7.3. Tételt** formalizálja: ha `f⁽ⁱ⁾(x₀) = 0` minden `i = 1, …, 2k`
esetén (`k ≥ 1`) és `f⁽²ᵏ⁺¹⁾(x₀) ≠ 0`, akkor `f`-nek `x₀`-ban inflexiós pontja van.

A könyv gondolatmenete: a legfeljebb `2k`-adrendű deriváltak `x₀` félkörnyezeteiben
jeltartók, így `f''(x)` az `x₀` helyen előjelet vált, azaz `f'(x)`-nek ott szélső értéke
van (8.4.1–8.4.2. Tétel), ez pedig a 8.5.2. Tétel szerint éppen azt jelenti, hogy
`f(x)`-nek `x₀`-ban inflexiós pontja van.

A formalizálásban ezt a gondolatmenetet a 8.5.2. Tétel bizonyításának magját adó
`Ch07.elso_nemnulla_derivalt_elojel` és `Ch07.derivalt_elojel` segédtételekre építjük:
belőlük közvetlenül adódik, hogy `f''` az `x₀` bal, illetve jobb oldali
félkörnyezetében ellentétes előjelű, ebből pedig a 8.6.1. Tétel (konvexség a második
derivált előjelével) alapján következik az inflexió.
-/

namespace Leindler.Ch08

open Set Leindler Leindler.Ch05 Leindler.Ch06 Leindler.Ch07

/-- Az iterált differenciálhányadosok összeadódnak: `(f⁽ʲ⁾)⁽ⁱ⁾ = f⁽ⁱ⁺ʲ⁾`. -/
theorem nDerivalt_nDerivalt (i j : ℕ) (f : ℝ → ℝ) :
    nDerivalt i (nDerivalt j f) = nDerivalt (i + j) f := by
  induction i with
  | zero => simp
  | succ m ih =>
    rw [nDerivalt_succ, ih, show m + 1 + j = (m + j) + 1 by omega, nDerivalt_succ]

/-- Ha `f` a `s` halmazon `(2k+1)`-szer differenciálható, akkor `f''` ugyanott
`(2k-1)`-szer differenciálható. -/
theorem nszerDifferencialhato_masodik {f : ℝ → ℝ} {n m : ℕ} {s : Set ℝ}
    (hf : NszerDifferencialhato f n s) (hm : m + 2 ≤ n) :
    NszerDifferencialhato (nDerivalt 2 f) m s := by
  intro i hi x hx
  have h := hf (i + 2) (by omega) x hx
  rw [nDerivalt_nDerivalt i 2 f, nDerivalt_nDerivalt (i + 1) 2 f]
  simpa [Nat.add_comm, Nat.add_assoc, Nat.add_left_comm] using h

/-- **Segédtétel a 8.7.3. Tételhez.** Ha `f⁽ⁱ⁾(x₀) = 0` minden `1 ≤ i ≤ 2k` esetén és
`L = f⁽²ᵏ⁺¹⁾(x₀) ≠ 0`, akkor az `x₀` egy környezetében `f''(y)` előjele megegyezik
`L·(y - x₀)` előjelével, azaz `f''(y)·L·(y - x₀) > 0`.

*Bizonyítás.* Az `F = f''` függvényre `F(x₀) = 0`, továbbá `F⁽ⁱ⁾(x₀) = f⁽ⁱ⁺²⁾(x₀) = 0`
minden `1 ≤ i ≤ 2k - 2` esetén, és `F⁽²ᵏ⁻¹⁾(x₀) = L ≠ 0`. `k = 1` esetén ez éppen a
derivált előjelhatásáról szóló segédtétel; `k ≥ 2` esetén az első el nem tűnő
magasabbrendű differenciálhányados előjeléről szóló segédtételt alkalmazzuk, majd az
`(y - x₀)^{2k-1} = (y - x₀)·((y - x₀)^{k-1})²` azonossággal egyszerűsítünk. -/
theorem masodik_derivalt_elojele {f : ℝ → ℝ} {c d x₀ : ℝ} {k : ℕ} (hk : 0 < k)
    (hf : NszerDifferencialhato f (2 * k + 1) (Ioo c d)) (hx₀ : x₀ ∈ Ioo c d)
    (hzero : ∀ i, 1 ≤ i → i ≤ 2 * k → nDerivalt i f x₀ = 0)
    (hL : nDerivalt (2 * k + 1) f x₀ ≠ 0) :
    ∃ δ > 0, ∀ y, |y - x₀| < δ → y ≠ x₀ →
      0 < nDerivalt 2 f y * nDerivalt (2 * k + 1) f x₀ * (y - x₀) := by
  have hG0 : nDerivalt 2 f x₀ = 0 := hzero 2 (by omega) (by omega)
  rcases Nat.lt_or_ge k 2 with hk1 | hk2
  · -- `k = 1`: a derivált előjelhatásáról szóló segédtétel
    have hk1' : k = 1 := by omega
    subst hk1'
    have hFd : Derivalt (nDerivalt 2 f) x₀ (nDerivalt 3 f x₀) := hf 2 (by omega) x₀ hx₀
    have hLne : nDerivalt 3 f x₀ ≠ 0 := by simpa using hL
    obtain ⟨δ, hδ, hsign⟩ := derivalt_elojel hFd hG0 hLne
    refine ⟨δ, hδ, fun y hy hyne => ?_⟩
    simpa using hsign y hy hyne
  · -- `k ≥ 2`: az első el nem tűnő magasabbrendű derivált előjele
    obtain ⟨N, hN⟩ : ∃ N, 2 * k - 1 = N + 1 := ⟨2 * k - 2, by omega⟩
    have hNpos : 1 ≤ N := by omega
    have hGdiff : NszerDifferencialhato (nDerivalt 2 f) (N + 1) (Ioo c d) :=
      nszerDifferencialhato_masodik hf (by omega)
    have hGzero : ∀ i, 1 ≤ i → i ≤ N → nDerivalt i (nDerivalt 2 f) x₀ = 0 := by
      intro i h1 h2
      rw [nDerivalt_nDerivalt]
      exact hzero (i + 2) (by omega) (by omega)
    have hGL : nDerivalt (N + 1) (nDerivalt 2 f) x₀ = nDerivalt (2 * k + 1) f x₀ := by
      rw [nDerivalt_nDerivalt]
      congr 1
      omega
    obtain ⟨δ, hδ, hsign⟩ :=
      elso_nemnulla_derivalt_elojel hNpos hGdiff hx₀ hGzero (by rw [hGL]; exact hL)
    refine ⟨δ, hδ, fun y hy hyne => ?_⟩
    have h := hsign y hy hyne
    rw [hG0, sub_zero, hGL] at h
    -- `(y - x₀)^{N+1} = (y - x₀)·((y - x₀)^{k-1})²`
    have hexp : (y - x₀) ^ (N + 1) = (y - x₀) * ((y - x₀) ^ (k - 1)) ^ 2 := by
      rw [← pow_mul, ← pow_succ']
      congr 1
      omega
    rw [hexp] at h
    have hw : 0 < ((y - x₀) ^ (k - 1)) ^ 2 := by
      have : (y - x₀) ≠ 0 := sub_ne_zero.2 hyne
      positivity
    nlinarith [h, hw]

/-- **8.7.3. Tétel.** Ha `f⁽ⁱ⁾(x₀) = 0` minden `i = 1, …, 2k` esetén (`k ≥ 1`) és
`f⁽²ᵏ⁺¹⁾(x₀) ≠ 0`, akkor `f(x)`-nek `x₀`-ban inflexiós pontja van.

*Bizonyítás (a könyv gondolatmenete).* A legfeljebb `2k`-adrendű deriváltak `x₀`
félkörnyezeteiben jeltartók, ezért `f''(x)` az `x₀` helyen előjelet vált: az egyik
félkörnyezetben nempozitív, a másikban nemnegatív. A 8.6.1. Tétel szerint tehát `f` az
egyik oldalon konkáv, a másikon konvex, azaz `x₀`-ban inflexiós pontja van. -/
theorem inflexios_pont_paratlan_rendu_derivalt {f : ℝ → ℝ} {c d x₀ : ℝ} {k : ℕ} (hk : 0 < k)
    (hf : NszerDifferencialhato f (2 * k + 1) (Ioo c d)) (hx₀ : x₀ ∈ Ioo c d)
    (hzero : ∀ i, 1 ≤ i → i ≤ 2 * k → nDerivalt i f x₀ = 0)
    (hL : nDerivalt (2 * k + 1) f x₀ ≠ 0) :
    InflexiosPont f x₀ := by
  obtain ⟨δ, hδ, hsign⟩ := masodik_derivalt_elojele hk hf hx₀ hzero hL
  have hd1 : 0 < x₀ - c := sub_pos.2 hx₀.1
  have hd2 : 0 < d - x₀ := sub_pos.2 hx₀.2
  set r : ℝ := min δ (min (x₀ - c) (d - x₀)) with hrdef
  have hr : 0 < r := lt_min hδ (lt_min hd1 hd2)
  have hrδ : r ≤ δ := min_le_left _ _
  have hrc : r ≤ x₀ - c := le_trans (min_le_right _ _) (min_le_left _ _)
  have hrd : r ≤ d - x₀ := le_trans (min_le_right _ _) (min_le_right _ _)
  have hmem : ∀ y ∈ Ioo (x₀ - r) (x₀ + r), y ∈ Ioo c d := by
    intro y hy
    exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have habs : ∀ y ∈ Ioo (x₀ - r) (x₀ + r), |y - x₀| < δ := by
    intro y hy
    rw [abs_lt]
    exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hd : ∀ x ∈ Ioo (x₀ - r) (x₀ + r), Derivalt f x (nDerivalt 1 f x) := by
    intro x hx
    exact hf 0 (by omega) x (hmem x hx)
  have hdd : ∀ x ∈ Ioo (x₀ - r) (x₀ + r),
      Derivalt (nDerivalt 1 f) x (nDerivalt 2 f x) := by
    intro x hx
    exact hf 1 (by omega) x (hmem x hx)
  have hsubL : Ioo (x₀ - r) x₀ ⊆ Ioo (x₀ - r) (x₀ + r) := fun y hy =>
    ⟨hy.1, by linarith [hy.2]⟩
  have hsubR : Ioo x₀ (x₀ + r) ⊆ Ioo (x₀ - r) (x₀ + r) := fun y hy =>
    ⟨by linarith [hy.1], hy.2⟩
  have hkey : ∀ y, |y - x₀| < δ → y ≠ x₀ →
      0 < nDerivalt 2 f y * (nDerivalt (2 * k + 1) f x₀ * (y - x₀)) := by
    intro y hy hyne
    rw [← mul_assoc]
    exact hsign y hy hyne
  rcases lt_or_gt_of_ne hL with hneg | hpos
  · -- `L < 0`: balra `f'' ≥ 0`, jobbra `f'' ≤ 0`
    refine inflexios_ha_masodik_derivalt_pozitivbol_negativba hr hd hdd ?_ ?_
    · intro y hy
      have h := hkey y (habs y (hsubL hy)) (ne_of_lt hy.2)
      have hA : 0 < nDerivalt (2 * k + 1) f x₀ * (y - x₀) :=
        mul_pos_of_neg_of_neg hneg (by linarith [hy.2])
      nlinarith [h, hA]
    · intro y hy
      have h := hkey y (habs y (hsubR hy)) (ne_of_gt hy.1)
      have hA : nDerivalt (2 * k + 1) f x₀ * (y - x₀) < 0 :=
        mul_neg_of_neg_of_pos hneg (by linarith [hy.1])
      nlinarith [h, hA]
  · -- `L > 0`: balra `f'' ≤ 0`, jobbra `f'' ≥ 0`
    refine inflexios_ha_masodik_derivalt_negativbol_pozitivba hr hd hdd ?_ ?_
    · intro y hy
      have h := hkey y (habs y (hsubL hy)) (ne_of_lt hy.2)
      have hA : nDerivalt (2 * k + 1) f x₀ * (y - x₀) < 0 :=
        mul_neg_of_pos_of_neg hpos (by linarith [hy.2])
      nlinarith [h, hA]
    · intro y hy
      have h := hkey y (habs y (hsubR hy)) (ne_of_gt hy.1)
      have hA : 0 < nDerivalt (2 * k + 1) f x₀ * (y - x₀) :=
        mul_pos hpos (by linarith [hy.1])
      nlinarith [h, hA]

end Leindler.Ch08
