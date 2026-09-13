import LinearisAlgebra.Ch12_LekepezesMatrixa
import LinearisAlgebra.Alkalmazas_Vizhalozatok

/-!
# Közös kategóriaelméleti mintázatok — a lineáris algebra oldala

Ez a modul **nem a Szabó-jegyzet része**, hanem a két formalizált tankönyv (Leindler:
*Analízis*, Szabó: *Bevezetés a lineáris algebrába*) **közös szerkezeti mintázatait**
gyűjti össze, a Lawvere–Schanuel-féle *Conceptual Mathematics* fogalmi nyelvén, és
mindegyiket egy hegyvidéki vízrajzi kérdésre alkalmazza.

Ugyanaz a hat mintázat szerepel, mint az analízis oldalán
(`Analizis/Analizis/Mintazatok_Kategoriaelmelet.lean`):

| # | mintázat | itt (lineáris algebra) | ott (analízis) |
|---|----------|------------------------|----------------|
| 1 | **kategória** | `linearis_kategoria`, `matrix_kategoria` | `folytonos_kategoria` |
| 2 | **funktor** | `atviteli_matrixok_szorzodnak` (12.3.) | `erzekenyseg_szorzodik` (6.4.1.) |
| 3 | **adjunkció / univerzális tulajdonság** | `generalt_adjunkcio` (6.10.) | `szupremum_adjunkcio` (3. fej.) |
| 4 | **rendezéstartás (poset-funktor)** | `nemnegativ_monoton`, `nemnegativ_kompozicio` | `csokkeno_kompozicio` (8.1.2.) |
| 5 | **lax struktúra (kociklus)** | `Vizhalozat.veszteseg_szorzat` | `veszteseg_kompozicio` |
| 6 | **fixpont / mértani sor** | `Vizhalozat.neumann_inverz` | `veszteseg_iteralt` |

A mintázatok vízrajzi olvasata a `KATEGORIAELMELETI_MINTAZATOK.md` dokumentumban van
kifejtve. Minden bizonyítás a **jegyzet saját tételeire** épül (2.5. mátrixszorzás
asszociativitása, 6.10. generált altér, 10.7. lineáris leképezések kompozíciója,
12.3. a kompozíció mátrixa).
-/

namespace SzaboLinAlg.Mintazatok

open scoped BigOperators
open Matrix Finset SzaboLinAlg.Ch02 SzaboLinAlg.Ch06 SzaboLinAlg.Ch10 SzaboLinAlg.Ch12

/-! ## 1. mintázat: kategória — a kompozíció és amit megőriz -/

variable {T : Type*} [Field T]
variable {U V W : Type*} [AddCommGroup U] [Module T U] [AddCommGroup V] [Module T V]
  [AddCommGroup W] [Module T W]

/-- **A lineáris leképezések kategóriát alkotnak.** A kompozíció asszociatív, egysége az
identitás, és a linearitás öröklődik a kompozícióra (10.7.). Ez a Lawvere–Schanuel-féle
első fogalom, és pontosan megfelel az analízis oldali `folytonos_kategoria`-nak. -/
theorem linearis_kategoria (f : U → V) (g : V → W) :
    ((fun u => id (f u)) = f ∧ (fun u => f (id u)) = f)
      ∧ (LinearisLekepezes T f → LinearisLekepezes T g →
          LinearisLekepezes T (fun u => g (f u))) := by
  refine ⟨⟨rfl, rfl⟩, fun hf hg => ⟨fun u v => ?_, fun c u => ?_⟩⟩
  · show g (f (u + v)) = g (f u) + g (f v)
    rw [hf.1 u v, hg.1 (f u) (f v)]
  · show g (f (c • u)) = c • g (f u)
    rw [hf.2 c u, hg.2 c (f u)]

/-- **A mátrixok kategóriát alkotnak** (2.5. Tétel + egységmátrix): a szorzás asszociatív,
és az egységmátrix kétoldali egység. Vízrajzi olvasat: egy vízgyűjtő-hálózatot tetszőleges
módon bonthatunk részhálózatokra, az eredő átviteli mátrix ugyanaz. -/
theorem matrix_kategoria {m n s t : ℕ} (A : Matrix' T m n) (B : Matrix' T n s)
    (C : Matrix' T s t) :
    (A * B) * C = A * (B * C) ∧ (1 : Matrix' T m m) * A = A ∧ A * (1 : Matrix' T n n) = A :=
  ⟨(szorzas_asszociativ A B C).symm, (egysegmatrix_szorzas A).1, (egysegmatrix_szorzas A).2⟩

/-! ## 2. mintázat: funktor — a kompozíció szorzattá válik

A 12.3. Tétel (`matrixa_comp`) szerint a „mátrixot rendelünk a leképezéshez” hozzárendelés
*funktor*: a kompozíciót mátrixszorzattá alakítja. Ez ugyanaz a mintázat, mint az analízis
oldalán a láncszabály. -/

/-- **Funktorialitás (12.3.).** Két egymás utáni hálózati szakasz átviteli mátrixa a két
mátrix szorzata; a hozamvektorra alkalmazva: a szakaszokat egyenként vagy egyszerre
számolva ugyanazt kapjuk. Vízrajzi olvasat: a részvízgyűjtőkre külön kalibrált átviteli
mátrixok **összeszorozhatók**, és az eredmény független attól, hogyan daraboltuk fel a
hálózatot — ez teszi lehetővé, hogy különböző csoportok külön mérjenek, majd az
eredményeket kompozicionálisan összerakják. -/
theorem atviteli_matrixok_szorzodnak {m n s : ℕ} (A : Matrix' T m n) (B : Matrix' T n s)
    (v : Fin s → T) : (A * B) *ᵥ v = A *ᵥ (B *ᵥ v) :=
  (Matrix.mulVec_mulVec v A B).symm

omit [AddCommGroup U] [Module T U] in
/-- Ugyanez absztrakt lineáris leképezésekre, a jegyzet 12.3. Tételével: a kompozíció
mátrixa a mátrixok szorzata. -/
theorem lekepezes_funktorialis {m n p : ℕ} {f : U → V} {g : V → W}
    (hg : LinearisLekepezes T g) {e : Fin m → U} {fb : Fin n → V} {gb : Fin p → W}
    {A : Matrix' T m n} {B : Matrix' T n p} (hA : LekepezesMatrixa f e fb A)
    (hB : LekepezesMatrixa g fb gb B) :
    LekepezesMatrixa (fun u => g (f u)) e gb (A * B) :=
  matrixa_comp hg hA hB

/-! ## 3. mintázat: adjunkció — a *legkisebb* lefedő objektum

A generált altér a legszűkebb olyan altér, amely tartalmazza az adathalmazt (6.10.). Az
`⟨lefedés⟩ ↔ ⟨tartalmazás⟩` alakú ekvivalencia ugyanaz az univerzális tulajdonság, mint a
szuprémumé az analízisben. -/

/-- **Adjunkció-alak (6.10. Tétel).** Ha `U` altér, akkor `[X] ⊆ U` **pontosan akkor**,
ha `X ⊆ U`. Vízrajzi olvasat: a mért állapotvektorok halmazát egy „modelltér” pontosan
akkor fedi le, ha az egyes méréseket lefedi; a generált altér tehát a *legkisebb modell*,
amely az összes mérést megmagyarázza. -/
theorem generalt_adjunkcio {X Y : Set V} (hY : Alter T Y) :
    Generalt T X ⊆ Y ↔ X ⊆ Y := by
  constructor
  · exact fun h => (subset_generalt X).trans h
  · exact fun h => generalt_minimal hY h

/-- Az adjunkció következménye: **a generátorokon való egyezés elég**. Ha két lineáris
leképezés az `X` halmaz minden elemén megegyezik, akkor a generált altéren is. Vízrajzi
olvasat: elég a mérőhálózatot a bázist adó (független) helyszíneken kalibrálni, a modell
ezzel az egész állapottéren egyértelműen meghatározott. -/
theorem linearis_egyertelmu_generatoron {f g : V → W} (hf : LinearisLekepezes T f)
    (hg : LinearisLekepezes T g) {X : Set V} (h : ∀ x ∈ X, f x = g x) :
    ∀ v ∈ Generalt T X, f v = g v := by
  rintro v ⟨n, w, l, hw, rfl⟩
  have hfsum : f (∑ i, l i • w i) = ∑ i, l i • f (w i) := map_kombinacio hf l w
  have hgsum : g (∑ i, l i • w i) = ∑ i, l i • g (w i) := map_kombinacio hg l w
  rw [hfsum, hgsum]
  exact Finset.sum_congr rfl fun i _ => by rw [h (w i) (hw i)]

/-! ## 4. mintázat: rendezéstartás (poset-funktor)

A nemnegatív együtthatós („fizikailag értelmes”) átviteli mátrixok rendezéstartó
leképezéseket adnak: több befolyó vízből sosem lesz kevesebb kifolyó. A monoton
leképezések — poset-funktorok — zártak a kompozícióra, akárcsak az analízis oldalán. -/

variable {n : ℕ}

/-- Egy mátrix *nemnegatív*, ha minden eleme nemnegatív (rendezett test felett). -/
def Nemnegativ [LinearOrder T] [IsStrictOrderedRing T] {m k : ℕ} (M : Matrix' T m k) : Prop :=
  ∀ i j, 0 ≤ M i j

/-- **Poset-funktor.** Nemnegatív mátrix monoton: ha minden cellában legalább annyi víz
érkezik, akkor minden cellából legalább annyi távozik. -/
theorem nemnegativ_monoton [LinearOrder T] [IsStrictOrderedRing T] {m k : ℕ}
    {M : Matrix' T m k} (hM : Nemnegativ M) {u v : Fin k → T} (huv : ∀ j, u j ≤ v j) :
    ∀ i, (M *ᵥ u) i ≤ (M *ᵥ v) i := by
  intro i
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left (huv j) (hM i j)

/-- A monoton (nemnegatív) leképezések zártak a kompozícióra: a poset-funktorok
kategóriát alkotnak. -/
theorem nemnegativ_kompozicio [LinearOrder T] [IsStrictOrderedRing T] {m k s : ℕ}
    {M : Matrix' T m k} {N : Matrix' T k s} (hM : Nemnegativ M) (hN : Nemnegativ N) :
    Nemnegativ (M * N) := by
  intro i j
  simp only [Matrix.mul_apply]
  exact Finset.sum_nonneg fun l _ => mul_nonneg (hM i l) (hN l j)

/-! ## 5–6. mintázat: lax struktúra és fixpont

Ez a két mintázat már bizonyítva van az `Alkalmazas_Vizhalozatok` modulban
(`Vizhalozat.veszteseg_szorzat`, illetve `Vizhalozat.neumann_inverz`); itt csak azt a
következményt rögzítjük, amely a két mintázatot összeköti: körmentes hálózaton a
veszteségmentesség lépésenként ellenőrizhető, és a lefolyás-akkumuláció fixpontja a véges
mértani sorral áll elő. -/

/-- A vízmegőrző hálózatok **monoidot** alkotnak (egység: `1`, művelet: szorzás), és a
vízmegőrzés pontosan a veszteség eltűnése — a lax struktúra „szigorú” része. -/
theorem vizmegorzo_monoid {M N : Matrix' T n n}
    (hM : Vizhalozat.Vizmegorzo M) (hN : Vizhalozat.Vizmegorzo N) :
    Vizhalozat.Vizmegorzo (1 : Matrix' T n n) ∧ Vizhalozat.Vizmegorzo (M * N)
      ∧ (∀ j, Vizhalozat.veszteseg (M * N) j = 0) :=
  ⟨Vizhalozat.vizmegorzo_egyseg, Vizhalozat.vizmegorzo_szorzat hM hN,
    Vizhalozat.vizmegorzo_iff_veszteseg_nulla.1 (Vizhalozat.vizmegorzo_szorzat hM hN)⟩

/-- **Fixpont mintázat.** Körmentes (nilpotens) hálózaton az `a = r + M·a`
lefolyás-akkumulációs egyenlet egyetlen megoldása a véges mértani sor alkalmazása a
csapadékvektorra — ugyanaz a mintázat, mint az analízis oldali `akkumulacio_egyertelmu`. -/
theorem akkumulacio_fixpont {M : Matrix' T n n} (h : Vizhalozat.Kormentes M)
    (r : Fin n → T) : ∃! a : Fin n → T, a = r + M *ᵥ a :=
  Vizhalozat.lefolyas_kormentes h r

end SzaboLinAlg.Mintazatok
