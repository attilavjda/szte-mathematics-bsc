import Mathlib
import Analizis.Ch05c_ZartIntervallum
import Analizis.Ch06a_Differencialhatosag
import Analizis.Ch06b_ElemiDerivaltak
import Analizis.Ch08a_MonotonitasSzelsoertek
import Analizis.Ch08b_KonvexsegInflexio

/-!
# Alkalmazás: folyók hosszmetszete, elágazások és vízkészletek

Ez a modul **nem a Leindler-jegyzet része**, hanem annak alkalmazása: azt mutatja meg,
hogy a jegyzet 5–8. fejezetének fogalmai (folytonosság, derivált, Lagrange-tétel,
monotonitás, konvexség, függvénydiszkusszió) hogyan mondanak ki *hegyvidéki vízrajzi*
állításokat. Minden bizonyítás a **jegyzet saját tételeire** épül
(5.14.5. Bolzano–Darboux, 6.10.3. Lagrange, 8.1.2. monotonitás, 8.6.1. konvexség),
és a jegyzet saját fogalmait (`Derivalt`, `KonvexGorbe`, `FolytonosZarton`) használja.

## Tartalom

1. **A folyó hosszmetszete.** A vízrajzban a lejtő–vízgyűjtő terület összefüggésből
   (`S ~ A^(-θ)`) és Hack törvényéből (`A ~ x^(1/h)`) a főmeder magassági profiljára
   `z(x) = H - a·x^p` alakú hatványfüggvény adódik, `0 < p < 1` mellett. A 8.8. séma
   szerinti diszkusszió: `z` szigorúan csökkenő és **konvex** (a geomorfológia szavával
   „konkáv felfelé”), azaz a meredek hegyvidéki felső szakaszt lapos alföldi szakasz
   követi.
2. **Miért egyesülnek a patakok?** Az optimális csatornahálózat- (OCN-) modellben egy
   `Q` vízhozamú meder fajlagos energiaköltsége `Q^p`, `0 < p < 1`. A hatványfüggvény
   szigorú szubadditivitása (`(x+y)^p < x^p + y^p`) pontosan azt jelenti, hogy *egyetlen
   egyesített meder olcsóbb, mint két külön meder* — ez a folyóhálózatok fa-szerkezetének
   variációs magyarázata.
3. **Vízkészlet-mérleg.** Ha a tároló `S(t)` készletének deriváltja a betáplálás és a
   kivétel különbsége, akkor tartós hiány esetén a készlet lineáris ütemben fogy
   (Lagrange-tétel), és véges idő alatt el is fogy (Bolzano–Darboux-tétel); ha viszont a
   kivétel sosem haladja meg az utánpótlást, a készlet nem csökken. Ez a „fenntartható
   vízkivétel” feltételének egyszerű, de teljesen precíz alakja.
-/

namespace Leindler.Vizrajz

open Set Leindler Leindler.Ch05 Leindler.Ch06 Leindler.Ch08

/-! ## 1. A folyó hosszmetszete: `z(x) = H - a·x^p` -/

/-- A főmeder magassági profilja a forrástól mért `x` távolságban:
`z(x) = H - a·x^p`, ahol `H` a forrás magassága, `a > 0` és `0 < p < 1`. -/
noncomputable def profil (H a p x : ℝ) : ℝ := H - a * x ^ p

/-- A profil első deriváltja (a meder lejtése): `z'(x) = -a·p·x^(p-1)`. -/
noncomputable def profil' (a p x : ℝ) : ℝ := -(a * p * x ^ (p - 1))

/-- A profil második deriváltja: `z''(x) = a·p·(1-p)·x^(p-2)`. -/
noncomputable def profil'' (a p x : ℝ) : ℝ := a * p * (1 - p) * x ^ (p - 2)

/-- A profil differenciálható minden pozitív helyen, és deriváltja `profil'`
(a jegyzet 6.8.2. Tétele: `(xᵃ)' = a·xᵃ⁻¹`). -/
theorem derivalt_profil {H a p x : ℝ} (hx : 0 < x) :
    Derivalt (profil H a p) x (profil' a p x) := by
  have h := (derivalt_iff_hasDerivAt _ _ _).1 (derivalt_rpow hx p)
  have h2 : HasDerivAt (fun y : ℝ => H - a * y ^ p) (-(a * (p * x ^ (p - 1)))) x := by
    simpa using (h.const_mul a).const_sub H
  rw [derivalt_iff_hasDerivAt]
  simpa [profil, profil', mul_assoc] using h2

/-- A lejtésfüggvény differenciálható minden pozitív helyen, deriváltja `profil''`. -/
theorem derivalt_profil' {a p x : ℝ} (hx : 0 < x) :
    Derivalt (profil' a p) x (profil'' a p x) := by
  have h := (derivalt_iff_hasDerivAt _ _ _).1 (derivalt_rpow hx (p - 1))
  have h2 : HasDerivAt (fun y : ℝ => -(a * p * y ^ (p - 1)))
      (-(a * p * ((p - 1) * x ^ (p - 1 - 1)))) x := (h.const_mul (a * p)).neg
  rw [derivalt_iff_hasDerivAt]
  have hx2 : p - 1 - 1 = p - 2 := by ring
  rw [hx2] at h2
  simpa [profil', profil''] using h2.congr_deriv (by ring)

/-- A profil folytonos minden olyan zárt intervallumon, amely a pozitív félegyenesen van. -/
theorem profil_continuousOn {H a p u v : ℝ} (hu : 0 < u) :
    ContinuousOn (profil H a p) (Icc u v) := by
  refine continuousOn_const.sub (continuousOn_const.mul ?_)
  refine ContinuousOn.rpow_const continuousOn_id ?_
  intro x hx
  exact Or.inl (ne_of_gt (lt_of_lt_of_le hu hx.1))

/-- **A hosszmetszet szigorúan csökkenő** (8.1.2. Tétel): a folyó a forrástól a torkolat
felé mindenütt lejt. -/
theorem profil_szigoruan_csokkeno {H a p u v : ℝ} (hu : 0 < u) (ha : 0 < a) (hp : 0 < p) :
    ∀ x₁ ∈ Icc u v, ∀ x₂ ∈ Icc u v, x₁ < x₂ → profil H a p x₂ < profil H a p x₁ := by
  intro x₁ h₁ x₂ h₂ hlt
  have hmono :=
    szigoruan_novekedo_ha_derivalt_pozitiv (f := fun x => -profil H a p x)
      (f' := fun x => -profil' a p x) (a := u) (b := v)
      ((profil_continuousOn hu).neg)
      (fun x hx => by
        rw [derivalt_iff_hasDerivAt]
        exact ((derivalt_iff_hasDerivAt _ _ _).1
          (derivalt_profil (H := H) (a := a) (p := p) (lt_trans hu hx.1))).neg)
      (fun x hx => by
        have hxpos : 0 < x := lt_trans hu hx.1
        have : 0 < a * p * x ^ (p - 1) :=
          mul_pos (mul_pos ha hp) (Real.rpow_pos_of_pos hxpos _)
        simpa [profil'] using this)
      x₁ h₁ x₂ h₂ hlt
  linarith [hmono]

/-- **A hosszmetszet konvex** (8.6.1. Tétel), ha `0 < p < 1`: a meredek hegyvidéki
szakaszt egyre laposabb szakasz követi — ez a „konkáv felfelé” folyóprofil. -/
theorem profil_konvex {H a p u v : ℝ} (hu : 0 < u) (ha : 0 < a) (hp : 0 < p) (hp1 : p < 1) :
    KonvexGorbe (profil H a p) (Ioo u v) := by
  refine (konvex_iff_masodik_derivalt_nemnegativ
    (f := profil H a p) (f' := profil' a p) (f'' := profil'' a p)
    (fun x hx => derivalt_profil (lt_trans hu hx.1))
    (fun x hx => derivalt_profil' (lt_trans hu hx.1))).2 ?_
  intro x hx
  have hxpos : 0 < x := lt_trans hu hx.1
  have : 0 ≤ a * p * (1 - p) * x ^ (p - 2) :=
    le_of_lt (mul_pos (mul_pos (mul_pos ha hp) (by linarith))
      (Real.rpow_pos_of_pos hxpos _))
  simpa [profil''] using this

/-! ## 2. Miért egyesülnek a patakok? A hatványköltség szigorú szubadditivitása -/

/-- **A hatványfüggvény szigorú szubadditivitása `p < 1` esetén:**
`(x + y)^p < x^p + y^p` pozitív `x, y`-ra.

*Bizonyítás.* Legyen `s = x + y` és `t = x/s ∈ (0,1)`. Mivel `p < 1` és `0 < t < 1`,
`t = t^1 < t^p`, ugyanígy `1 - t < (1-t)^p`, tehát `1 = t + (1-t) < t^p + (1-t)^p`.
Beszorozva `s^p`-vel és felhasználva `(s·t)^p = s^p·t^p`-t adódik az állítás.
(A vízrajzi alkalmazásban `0 < p < 1`; a bizonyítás azonban csak `p < 1`-et használ.) -/
theorem rpow_szig_szubadditiv {p x y : ℝ} (hp1 : p < 1) (hx : 0 < x)
    (hy : 0 < y) : (x + y) ^ p < x ^ p + y ^ p := by
  have hspos : 0 < x + y := by linarith
  have hne : x + y ≠ 0 := ne_of_gt hspos
  have htpos : 0 < x / (x + y) := div_pos hx hspos
  have ht1 : x / (x + y) < 1 := by
    rw [div_lt_one hspos]; linarith
  set s : ℝ := x + y with hs
  set t : ℝ := x / s with ht
  have h1t : 0 < 1 - t := by linarith
  have h1t1 : 1 - t < 1 := by linarith
  have hA : t < t ^ p := by
    have := Real.rpow_lt_rpow_of_exponent_gt htpos ht1 hp1
    simpa using this
  have hB : (1 - t) < (1 - t) ^ p := by
    have := Real.rpow_lt_rpow_of_exponent_gt h1t h1t1 hp1
    simpa using this
  have hsum : (1 : ℝ) < t ^ p + (1 - t) ^ p := by linarith
  have hxeq : x = s * t := by
    rw [ht, hs]; field_simp
  have hyeq : y = s * (1 - t) := by
    rw [ht, hs]; field_simp; ring
  have hxp : x ^ p = s ^ p * t ^ p := by
    rw [hxeq, Real.mul_rpow hspos.le htpos.le]
  have hyp : y ^ p = s ^ p * (1 - t) ^ p := by
    rw [hyeq, Real.mul_rpow hspos.le h1t.le]
  have hsp : 0 < s ^ p := Real.rpow_pos_of_pos hspos p
  calc s ^ p = s ^ p * 1 := by ring
    _ < s ^ p * (t ^ p + (1 - t) ^ p) := by
        exact (mul_lt_mul_of_pos_left hsum hsp)
    _ = x ^ p + y ^ p := by rw [hxp, hyp]; ring

/-- **Az egyesült meder olcsóbb (OCN-elv).** Ha egy meder fajlagos energiaköltsége a
vízhozam `p`-edik hatványa (`0 < p < 1`), akkor két, `x` és `y` hozamú párhuzamos meder
költsége szigorúan nagyobb, mint az `x + y` hozamú egyesített mederé. Ez a variációs oka
annak, hogy a hegyoldal vizei fává szerveződve, elágazások helyett *összefolyva* jutnak
le a völgybe. -/
theorem egyesules_olcsobb {p x y : ℝ} (hp1 : p < 1) (hx : 0 < x) (hy : 0 < y) :
    (x + y) ^ p < x ^ p + y ^ p :=
  rpow_szig_szubadditiv hp1 hx hy

/-- Ugyanez a `Q` hozam kettéosztásának alakjában: `Q` hozamot `x` és `Q - x` részre
bontva a költség szigorúan nő. (`p = 1/2` a szokásos OCN-kitevő.) -/
theorem szetvalas_dragabb {p Q x : ℝ} (hp1 : p < 1) (hx : 0 < x) (hxQ : x < Q) :
    Q ^ p < x ^ p + (Q - x) ^ p := by
  have h := rpow_szig_szubadditiv hp1 hx (by linarith : (0:ℝ) < Q - x)
  simpa using h

/-! ## 3. Vízkészlet-mérleg: fenntartható és fenntarthatatlan kivétel -/

/-- **Tartós hiány melletti fogyás (Lagrange-tétel, 6.10.3.).** Ha a tároló `S(t)`
készletének deriváltja a `be(t)` utánpótlás és a `ki(t)` kivétel különbsége, és a hiány
tartósan legalább `c > 0`, akkor `S(b) ≤ S(a) - c·(b - a)`: a készlet legalább lineáris
ütemben fogy. -/
theorem keszlet_fogyas {S be ki : ℝ → ℝ} {a b c : ℝ}
    (hcont : ContinuousOn S (Icc a b))
    (hd : ∀ t ∈ Ioo a b, Derivalt S t (be t - ki t))
    (hhiany : ∀ t ∈ Ioo a b, be t + c ≤ ki t) (hab : a < b) :
    S b ≤ S a - c * (b - a) := by
  have hmono :=
    novekedo_ha_derivalt_nemnegativ (f := fun t => -(S t + c * t))
      (f' := fun t => -(be t - ki t + c)) (a := a) (b := b)
      ((hcont.add (continuousOn_const.mul continuousOn_id)).neg)
      (fun t ht => by
        rw [derivalt_iff_hasDerivAt]
        have h1 := (derivalt_iff_hasDerivAt _ _ _).1 (hd t ht)
        have h2 : HasDerivAt (fun s : ℝ => c * s) c t := by
          simpa using (hasDerivAt_id t).const_mul c
        simpa using (h1.add h2).neg)
      (fun t ht => by
        have := hhiany t ht
        simp only [neg_nonneg]
        linarith)
      a (left_mem_Icc.2 hab.le) b (right_mem_Icc.2 hab.le) hab
  have : -(S b + c * b) ≥ -(S a + c * a) := hmono
  nlinarith [this]

/-- **A fenntarthatatlan kivétel kiüríti a tárolót.** Ha a hiány tartósan legalább
`c > 0`, a kezdeti készlet pozitív, és a vizsgált időszak elég hosszú
(`S(a) < c·(b - a)`), akkor van olyan időpont, amikor a készlet éppen elfogy
(`S(t) = 0`) — a Bolzano–Darboux-tétel (5.14.5.) alkalmazása. -/
theorem keszlet_kiurul {S be ki : ℝ → ℝ} {a b c : ℝ}
    (hcont : ContinuousOn S (Icc a b))
    (hd : ∀ t ∈ Ioo a b, Derivalt S t (be t - ki t))
    (hhiany : ∀ t ∈ Ioo a b, be t + c ≤ ki t) (hab : a < b)
    (hSa : 0 < S a) (hhossz : S a < c * (b - a)) :
    ∃ t ∈ Ioo a b, S t = 0 := by
  have hb : S b ≤ S a - c * (b - a) := keszlet_fogyas hcont hd hhiany hab
  have hbneg : S b < 0 := by linarith
  obtain ⟨t, ht, hteq, -⟩ :=
    bolzano_darboux_elso_eleres (f := fun x => -S x) (C := 0) hab hcont.neg
      (by simpa using hSa) (by simpa using hbneg)
  exact ⟨t, ht, by simpa using neg_eq_zero.1 hteq⟩

/-- **A fenntartható kivétel feltétele (8.1.2. Tétel).** Ha a kivétel sehol nem haladja
meg az utánpótlást, akkor a készlet (tágabb értelemben) növekedő: a tároló sosem fogy. -/
theorem keszlet_fenntarthato {S be ki : ℝ → ℝ} {a b : ℝ}
    (hcont : ContinuousOn S (Icc a b))
    (hd : ∀ t ∈ Ioo a b, Derivalt S t (be t - ki t))
    (hfenn : ∀ t ∈ Ioo a b, ki t ≤ be t) :
    ∀ t₁ ∈ Icc a b, ∀ t₂ ∈ Icc a b, t₁ < t₂ → S t₁ ≤ S t₂ :=
  novekedo_ha_derivalt_nemnegativ (f := S) (f' := fun t => be t - ki t) hcont hd
    (fun t ht => sub_nonneg.2 (hfenn t ht))

end Leindler.Vizrajz
