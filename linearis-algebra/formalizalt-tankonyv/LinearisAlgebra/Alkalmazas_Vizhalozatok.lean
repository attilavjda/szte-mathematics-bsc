import LinearisAlgebra.Ch02_Matrixok
import LinearisAlgebra.Ch04_Inverzmatrix
import LinearisAlgebra.Ch05_Egyenletrendszerek

/-!
# Alkalmazás: vízgyűjtő-hálózatok lineáris algebrája és a Horton–Strahler-rend

Ez a modul **nem a Szabó-jegyzet része**, hanem annak alkalmazása: azt mutatja meg, hogy a
jegyzet fogalmai (mátrix, mátrixszorzás, inverz mátrix, lineáris egyenletrendszer)
hogyan írják le egy hegyvidéki **vízgyűjtő-hálózat** működését, és hogy a folyóhálózatok
klasszikus, empirikus törvényei (Horton törvényei, Strahler-rend) hogyan válnak bizonyított
állításokká.

## Tartalom

1. **Lefolyás-mátrix és lefolyás-akkumuláció.** A hálózat celláit egy `M` *átirányítási
   mátrix* köti össze: `M i j = 1`, ha a `j` cella vize az `i` cellába folyik. A hálózat
   körmentessége azt jelenti, hogy `M` nilpotens (`M ^ k = 0`). Ekkor az `a = r + M·a`
   *lefolyás-akkumulációs egyenletnek* (minden cella hozama a saját csapadéka plusz a
   felette lévők hozama) **pontosan egy** megoldása van, mégpedig
   `a = (I + M + M² + … + M^(k-1))·r`; a jegyzet nyelvén: az `(I - M)` mátrix invertálható,
   és az egyenletrendszer egyértelműen megoldható (5. fejezet).
2. **Tömegmegmaradás.** Ha a `M` átirányítási mátrix oszlopösszegei 1-ek (minden cella
   minden vizét továbbadja), akkor a teljes vízmennyiség nem változik; az ilyen mátrixok
   zártak a szorzásra, és az egységmátrix is ilyen — vagyis a vízmegőrző hálózatok
   *kategóriát/monoidot* alkotnak, a kompozíció pedig a mátrixszorzás (12.6. funktorialitás).
3. **Horton–Strahler-rend.** A patakhálózatot bináris fával modellezve a Strahler-rend
   rekurzív definíciója (két azonos rendű ág összefolyása eggyel nagyobb rendet ad) és
   Horton *elsőrendű törvénye* (az egyes rendekhez tartozó szakaszok száma mértani sorozat,
   `R_b = 2` a teljes bináris hálózaton) formalizálva és bizonyítva.
-/

namespace SzaboLinAlg
namespace Vizhalozat

open scoped BigOperators
open Matrix Finset

variable {T : Type*} [CommRing T] {n : ℕ}

/-! ## 1. Lefolyás-mátrix, körmentesség, lefolyás-akkumuláció -/

/-- Egy hálózat *körmentes* (aciklikus), ha az átirányítási mátrixának valamely hatványa
a nullmátrix: a víz véges sok lépésben elhagyja a rendszert. -/
def Kormentes (M : Matrix' T n n) : Prop := ∃ k : ℕ, M ^ k = 0

/-- A `Neumann`-sor (véges mértani sor): `I + M + M² + … + M^(k-1)`. -/
def neumannOsszeg (M : Matrix' T n n) (k : ℕ) : Matrix' T n n := ∑ i ∈ range k, M ^ i

/-- Ha `M ^ k = 0`, akkor `(I - M)` invertálható, inverze a véges mértani sor.
(A jegyzet 4.1. Definíciója szerinti inverz: kétoldali inverz.) -/
theorem neumann_inverz {M : Matrix' T n n} {k : ℕ} (hk : M ^ k = 0) :
    (1 - M) * neumannOsszeg M k = 1 ∧ neumannOsszeg M k * (1 - M) = 1 := by
  have h1 : neumannOsszeg M k * (M - 1) = M ^ k - 1 := geom_sum_mul M k
  have h2 : (M - 1) * neumannOsszeg M k = M ^ k - 1 := mul_geom_sum M k
  rw [hk] at h1 h2
  constructor
  · rw [← neg_sub M 1, neg_mul, h2]; simp
  · rw [← neg_sub M 1, mul_neg, h1]; simp

/-- **A lefolyás-akkumuláció egyértelműen megoldható.** Körmentes hálózatban minden `r`
csapadék-vektorhoz pontosan egy olyan `a` hozamvektor tartozik, amelyre minden cellában
`a = r + M·a` (a cella hozama = a saját csapadéka + a fölötte lévő cellák hozama), és ez
`a = (I + M + … + M^(k-1))·r`.

Ez ugyanaz az egyenlet, mint a jegyzet alkalmazásai közt szereplő Leontyev-féle
input–output egyenlet (`Tematika.leontyev_egyenlet`): `(I - M)·a = r`. -/
theorem lefolyas_egyertelmu {M : Matrix' T n n} {k : ℕ} (hk : M ^ k = 0)
    (r : Fin n → T) :
    ∃! a : Fin n → T, a = r + M *ᵥ a := by
  obtain ⟨hbal, hjobb⟩ := neumann_inverz hk
  have hS : neumannOsszeg M k = 1 + M * neumannOsszeg M k := by
    rw [sub_mul, one_mul] at hbal
    exact sub_eq_iff_eq_add.mp hbal
  refine ⟨neumannOsszeg M k *ᵥ r, ?_, ?_⟩
  · calc neumannOsszeg M k *ᵥ r = (1 + M * neumannOsszeg M k) *ᵥ r := by rw [← hS]
      _ = r + M *ᵥ (neumannOsszeg M k *ᵥ r) := by
          rw [Matrix.add_mulVec, Matrix.one_mulVec, Matrix.mulVec_mulVec]
  · intro b hb
    have hb' : (1 - M) *ᵥ b = r := by
      rw [Matrix.sub_mulVec, Matrix.one_mulVec]
      exact sub_eq_iff_eq_add.mpr hb
    calc b = (neumannOsszeg M k * (1 - M)) *ᵥ b := by rw [hjobb, Matrix.one_mulVec]
      _ = neumannOsszeg M k *ᵥ ((1 - M) *ᵥ b) := by rw [← Matrix.mulVec_mulVec]
      _ = neumannOsszeg M k *ᵥ r := by rw [hb']

/-! ## 2. Tömegmegmaradás: vízmegőrző átirányítási mátrixok -/

/-- Egy mátrix *vízmegőrző*, ha minden oszlopának összege `1`: minden cella a hozzá érkező
teljes vízmennyiséget továbbadja. -/
def Vizmegorzo (M : Matrix' T n n) : Prop := ∀ j, ∑ i, M i j = 1

/-- **Tömegmegmaradás.** Vízmegőrző mátrix a teljes vízmennyiséget nem változtatja meg:
`∑ᵢ (M·v)ᵢ = ∑ⱼ vⱼ`. -/
theorem vizmegorzo_osszeg {M : Matrix' T n n} (hM : Vizmegorzo M) (v : Fin n → T) :
    ∑ i, (M *ᵥ v) i = ∑ j, v j := by
  have h : ∑ i, (M *ᵥ v) i = ∑ i, ∑ j, M i j * v j := by
    simp [Matrix.mulVec, dotProduct]
  rw [h, Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [← Finset.sum_mul, hM j, one_mul]

/-- Az egységmátrix vízmegőrző (a „semmit sem csinálunk” hálózat). -/
theorem vizmegorzo_egyseg : Vizmegorzo (1 : Matrix' T n n) := by
  intro j
  simp [Matrix.one_apply]

/-- **A vízmegőrző hálózatok zártak a kompozícióra:** két vízmegőrző lépés egymás utáni
elvégzése (mátrixszorzat) is vízmegőrző. Az egységmátrixszal együtt ez azt jelenti, hogy a
vízmegőrző hálózatok monoidot (egyobjektumú kategóriát) alkotnak, amelyben a kompozíció a
mátrixszorzás (12.6. Tétel: a kompozíció mátrixa a mátrixok szorzata). -/
theorem vizmegorzo_szorzat {M N : Matrix' T n n} (hM : Vizmegorzo M) (hN : Vizmegorzo N) :
    Vizmegorzo (M * N) := by
  intro j
  have h : ∑ i, (M * N) i j = ∑ i, ∑ l, M i l * N l j := by
    simp [Matrix.mul_apply]
  rw [h, Finset.sum_comm]
  have h2 : ∀ l : Fin n, ∑ i, M i l * N l j = N l j := by
    intro l
    rw [← Finset.sum_mul, hM l, one_mul]
  rw [Finset.sum_congr rfl fun l _ => h2 l]
  exact hN j

/-! ## 3. Horton–Strahler-rend és Horton törvénye a szakaszok számáról -/

/-- Egy patakhálózat modellje: vagy egy forrás, vagy két hálózat összefolyása. -/
inductive Vizfolyas : Type
  | forras : Vizfolyas
  | osszefolyas : Vizfolyas → Vizfolyas → Vizfolyas
  deriving DecidableEq

/-- **Strahler-rend.** A forrás rendje `1`; két ág összefolyásánál a rend eggyel nő, ha a
két ág rendje egyenlő, egyébként a nagyobbik rend marad. -/
def rend : Vizfolyas → ℕ
  | .forras => 1
  | .osszefolyas l r => if rend l = rend r then rend l + 1 else max (rend l) (rend r)

/-- A `n`-edik *teljes* (szabályos, kétfelé ágazó) hálózat. -/
def teljes : ℕ → Vizfolyas
  | 0 => .forras
  | n + 1 => .osszefolyas (teljes n) (teljes n)

/-- A teljes, `n` szintű hálózat Strahler-rendje `n + 1`. -/
theorem rend_teljes (n : ℕ) : rend (teljes n) = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [teljes, rend, ih]

/-- Ugyanez az összefolyás alakjában kiírva. -/
theorem rend_teljes_succ (n : ℕ) :
    rend (Vizfolyas.osszefolyas (teljes n) (teljes n)) = n + 2 := rend_teljes (n + 1)

/-- A `k`-adrendű szakaszok száma egy hálózatban. -/
def szam : Vizfolyas → ℕ → ℕ
  | .forras, k => if k = 1 then 1 else 0
  | .osszefolyas l r, k =>
      szam l k + szam r k + (if rend (.osszefolyas l r) = k then 1 else 0)

/-- A hálózat rendjénél magasabb rendű szakasz nincs. -/
theorem szam_teljes_nagy (n k : ℕ) (h : n + 1 < k) : szam (teljes n) k = 0 := by
  induction n generalizing k with
  | zero =>
      have hk : k ≠ 1 := by omega
      simp [teljes, szam, hk]
  | succ n ih =>
      have h1 : n + 1 < k := by omega
      have h2 : rend (Vizfolyas.osszefolyas (teljes n) (teljes n)) ≠ k := by
        rw [rend_teljes_succ]; omega
      simp [teljes, szam, ih k h1, h2]

/-- **Horton első törvénye (a szakaszok száma).** A teljes, `n` szintű hálózatban a
`k`-adrendű szakaszok száma `2^(n+1-k)`, ha `1 ≤ k ≤ n+1`. -/
theorem szam_teljes (n k : ℕ) (h1 : 1 ≤ k) (h2 : k ≤ n + 1) :
    szam (teljes n) k = 2 ^ (n + 1 - k) := by
  induction n generalizing k with
  | zero =>
      have hk : k = 1 := by omega
      subst hk
      simp [teljes, szam]
  | succ n ih =>
      rcases Nat.lt_or_ge k (n + 2) with hk | hk
      · have hkn : k ≤ n + 1 := by omega
        have hrend : rend (Vizfolyas.osszefolyas (teljes n) (teljes n)) ≠ k := by
          rw [rend_teljes_succ]; omega
        have hstep : szam (teljes (n + 1)) k = szam (teljes n) k + szam (teljes n) k := by
          simp [teljes, szam, hrend]
        rw [hstep, ih k h1 hkn]
        have he : n + 1 + 1 - k = (n + 1 - k) + 1 := by omega
        rw [he, pow_succ]
        ring
      · have hk2 : k = n + 2 := by omega
        subst hk2
        have hzero : szam (teljes n) (n + 2) = 0 := szam_teljes_nagy n (n + 2) (by omega)
        simp [teljes, szam, rend_teljes_succ n, hzero]

/-- **Horton elágazási aránya (`R_b = 2`).** A teljes hálózatban az egymást követő
rendekhez tartozó szakaszszámok hányadosa állandó `2`: `N_k = 2·N_(k+1)`. -/
theorem horton_elagazasi_arany (n k : ℕ) (h1 : 1 ≤ k) (h2 : k + 1 ≤ n + 1) :
    szam (teljes n) k = 2 * szam (teljes n) (k + 1) := by
  rw [szam_teljes n k h1 (by omega), szam_teljes n (k + 1) (by omega) h2]
  have he : n + 1 - k = (n + 1 - (k + 1)) + 1 := by omega
  rw [he, pow_succ]
  ring

/-- Két azonos rendű patak összefolyása eggyel nagyobb rendű patakot ad (a Strahler-szabály
lényege), míg különböző rendűek esetén a nagyobbik rend öröklődik. -/
theorem rend_osszefolyas (l r : Vizfolyas) :
    (rend l = rend r → rend (.osszefolyas l r) = rend l + 1) ∧
      (rend l ≠ rend r → rend (.osszefolyas l r) = max (rend l) (rend r)) :=
  ⟨fun h => by simp [rend, h], fun h => by simp [rend, h]⟩

end Vizhalozat
end SzaboLinAlg
