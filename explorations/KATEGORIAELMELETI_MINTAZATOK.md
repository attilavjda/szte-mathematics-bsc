# Közös kategóriaelméleti mintázatok a két könyv formalizációjában — és mire használhatók a folyó- és hegyvidéki kutatásban

*(Shared categorical patterns in the two formalised textbooks — and how they transfer to river & mountain research. English summary at the end.)*

Ez a dokumentum arra a kérdésre válaszol, hogy **milyen közös szerkezeti mintázatok** vannak
a két formalizált tankönyv anyagában — Leindler László: *Analízis* (Polygon, 2001) és
Szabó László: *Bevezetés a lineáris algebrába* (2006) —, ha a Lawvere–Schanuel-féle
*Conceptual Mathematics* kategóriaelméleti nyelvén nézzük őket, és hogy **ezek a mintázatok
hogyan alkalmazhatók** a hegyvidéki vízrajzi (folyó–hegy) kutatás feltáró szakaszában, illetve
milyen gyakorlati, „pozitív változást” hozó döntéseket támogatnak.

Minden mintázathoz megadjuk:

* mit mond a mintázat kategóriaelméletileg,
* hol jelenik meg a **Leindler**-jegyzetben (analízis) és hol a **Szabó**-jegyzetben (lineáris algebra),
* melyik **gépileg ellenőrzött Lean-deklaráció** rögzíti (a két új modul:
  `Analizis/Analizis/Mintazatok_Kategoriaelmelet.lean`,
  `LinearisAlgebra/LinearisAlgebra/Mintazatok_Kategoriaelmelet.lean`),
* mire jó a terepen, és milyen döntés lesz tőle jobb.

---

## 0. Áttekintő táblázat

| # | Mintázat (kategóriaelmélet) | Analízis (Leindler) | Lineáris algebra (Szabó) | Vízrajzi olvasat |
|---|------------------------------|---------------------|--------------------------|------------------|
| 1 | **Kategória**: objektumok + kompozíció, asszociativitás, egység; a „jó tulajdonság” öröklődik | 5.5.1–5.5.2. összetett függvény, a folytonosság öröklődik — `folytonos_kategoria` | 2.5. mátrixszorzás asszociativitása, 10.7. lineáris leképezések kompozíciója — `matrix_kategoria`, `linearis_kategoria` | A vízgyűjtő tetszőlegesen darabolható részszakaszokra; az eredő ugyanaz |
| 2 | **Funktor**: a kompozíció szorzattá válik, az identitás egységgé | 6.4.1. láncszabály — `erzekenyseg_szorzodik`, `erzekenyseg_identitas` | 12.3. a kompozíció mátrixa a mátrixok szorzata — `atviteli_matrixok_szorzodnak`, `lekepezes_funktorialis` | Érzékenységek/átvitelek **szorzódnak** a lánc mentén: hibaterjedés, kalibráció |
| 3 | **Univerzális tulajdonság / adjunkció**: a *legkisebb* lefedő objektum | 3. fejezet, 10. (teljességi) axióma: szuprémum — `szupremum_adjunkcio`, `legkisebb_biztonsagos_szint` | 6.10. generált altér `[X]` — `generalt_adjunkcio`, `linearis_egyertelmu_generatoron` | „Legkisebb elegendő beavatkozás”, „legkisebb modell, amely az összes mérést megmagyarázza” |
| 4 | **Poset-funktor**: rendezéstartó leképezések, zártak a kompozícióra | 8.1.2. monotonitás — `csokkeno_kompozicio`, `novekedo_kompozicio`, `profil_csokkeno` | nemnegatív mátrixok monotonitása — `nemnegativ_monoton`, `nemnegativ_kompozicio` | Monotonitási garanciák: „több csapadékból sosem lesz kevesebb lefolyás” |
| 5 | **Lax struktúra (kociklus)**: a megmaradás *sérülésének* mértéke maga is kompozicionális | `veszteseg`, `veszteseg_kompozicio`, `megorzo_kompozicio` | `Vizhalozat.veszteseg`, `veszteseg_szorzat`, `merleg_veszteseggel`, `vizmegorzo_monoid` | A mért mérleghiány szakaszonkénti járulékokra bomlik — **a szivárgás lokalizálható** |
| 6 | **Fixpont / initial algebra**: rekurzió véges összeggé oldva | mértani sor, `veszteseg_iteralt`, `akkumulacio_egyertelmu` | `Vizhalozat.neumann_inverz`, `lefolyas_kormentes`, `akkumulacio_fixpont`; Strahler-rend rekurzióval (`rend`, `szam`, `horton_elagazasi_arany`) | Lefolyás-akkumuláció egyértelmű megoldása; hálózati önhasonlóság |
| (+) | **Szorzatobjektum** (Lawvere 1. session) | `Lawvere_SzorzatObjektum.lean`: `galilei_univerzalis`, `folytonosSikba_iff` | `szorzat_univerzalis_linearis`, `koordinatak_univerzalis` | Terep = alaprajz × magasság; „két filmből visszaállítható a röpte” = két adatsorból az állapot |

A táblázat lényege: **a két könyv ugyanazt a hat mintázatot mondja el kétszer**, más
anyagon. Az analízisben a mintázatok „egydimenziósak és folytonosak”, a lineáris algebrában
„sokdimenziósak és diszkrétek”; kategóriaelméletileg azonban ugyanazok az állítások. Ez az,
ami a hegyvidéki vízrajzra közvetlenül átvihető, mert egy vízgyűjtő egyszerre folytonos
(profil, hozamgörbe, energia) és diszkrét-hálózatos (cellák, szakaszok, összefolyások).

---

## 1. mintázat — Kategória: a rendszer tetszőlegesen darabolható

**Kategóriaelméletileg.** Egy kategóriában a nyilak összetehetők, az összetétel asszociatív,
és minden objektumon van egységnyíl. Ebből következik, hogy egy hosszú lánc értéke független
a zárójelezéstől: mindegy, hogyan bontjuk részekre.

**A két könyvben.** Leindlernél az 5.5.1. összetett függvény és az 5.5.2. Tétel: a
folytonosság öröklődik a kompozícióra. Szabónál a 2.5. Tétel (mátrixszorzás asszociativitása)
és a lineáris leképezések kompozíciója. Formalizálva: `folytonos_kategoria`,
`matrix_kategoria`, `linearis_kategoria`.

**Terepi jelentés.** Egy vízgyűjtőt szakaszokra (részvízgyűjtőkre, mérőpontok közti
szelvényekre) bontunk. A kategória-axiómák azt garantálják, hogy **a felbontás választása nem
befolyásolja az eredményt** — két csoport különböző szakaszolással dolgozhat, az eredményük
összeilleszthető.

**Pozitív változás.** Ez a *megosztott, moduláris monitorozás* matematikai engedélye: egy
menedékház, egy egyetemi csoport és egy tartományi vízrajzi szolgálat külön-külön mérheti a
saját szakaszát, és az eredmények utólag, veszteség nélkül összerakhatók. Ez csökkenti a
belépési küszöböt önkéntes/kisléptékű méréshez.

---

## 2. mintázat — Funktor: az érzékenységek szorzódnak

**Kategóriaelméletileg.** A funktor a kompozíciót kompozícióba, az identitást identitásba
viszi. Két klasszikus példa: a derivált (`D(f∘g) = Df·Dg`, láncszabály) és a mátrix-hozzárendelés
(`[g∘f] = [f]·[g]`).

**A két könyvben.** 6.4.1. láncszabály (`erzekenyseg_szorzodik`), illetve 12.3. Tétel
(`lekepezes_funktorialis`, `atviteli_matrixok_szorzodnak`).

**Terepi jelentés.** A „csapadék → vízállás → vízhozam → hordalék” lánc mentén a
végérzékenység a lokális érzékenységek szorzata. Ugyanez hálózatos alakban: az egymás utáni
szakaszok átviteli mátrixai összeszorzódnak.

**Pozitív változás.** Két gyakorlati következmény:

1. **Hibabüdzsé.** Mivel a hatások szorzódnak, a relatív hibák jó közelítéssel összeadódnak;
   így *előre* megmondható, melyik szakasz kalibrálása javít legtöbbet a végeredményen. Ez
   szűkös terepi idővel gazdálkodó projektben közvetlen prioritási sorrend.
2. **Kompozicionális modellépítés.** A részvízgyűjtőkre külön kalibrált modellek
   összeszorozhatók; nem kell egyetlen monolit modellt kalibrálni.

---

## 3. mintázat — Univerzális tulajdonság: a legkisebb elegendő beavatkozás

**Kategóriaelméletileg.** A szuprémum és a generált altér ugyanannak a szerkezetnek
(bal adjungált / univerzális tulajdonság) két példája: mindkettőt egy
`⟨lefedés⟩ ↔ ⟨összehasonlítás⟩` alakú ekvivalencia jellemzi.

* `sSup S ≤ b ↔ (∀ x ∈ S, x ≤ b)` — `szupremum_adjunkcio`
* `[X] ⊆ U ↔ X ⊆ U` (ha `U` altér) — `generalt_adjunkcio`

**Terepi jelentés.**

* *Szuprémum:* a mért árvízszintek halmazát pontosan azok a magasságok „fedik le”, amelyek
  legalább akkorák, mint a szuprémum; a szuprémum tehát a **legkisebb (legolcsóbb) elegendő**
  védelmi szint (`legkisebb_biztonsagos_szint`).
* *Generált altér:* a mért állapotvektorok generálta altér a **legkisebb modell**, amely az
  összes mérést megmagyarázza; és aki a generátorokon kalibrál, az az egész téren kalibrált
  (`linearis_egyertelmu_generatoron`).

**Pozitív változás.** Ez a „minimális beavatkozás” elv formalizált alakja: se túl-, se
alultervezés. A mérőhálózat tervezésénél ugyanez azt mondja, hogy **elég egy generátorrendszert
lefedő mérőpont-halmazt működtetni** — kevesebb műszer, ugyanaz az információ. Költségkorlátos
hegyvidéki monitorozásnál ez a legközvetlenebbül hasznosítható állítás.

---

## 4. mintázat — Poset-funktor: monotonitási garanciák

**Kategóriaelméletileg.** Egy rendezett halmaz kategória, a monoton leképezések a funktorai;
a monoton leképezések zártak a kompozícióra.

**A két könyvben.** 8.1.2. monotonitási tétel és a monoton függvények kompozíciója
(`csokkeno_kompozicio`, `novekedo_kompozicio`, `profil_csokkeno`), illetve a nemnegatív
mátrixok monotonitása (`nemnegativ_monoton`, `nemnegativ_kompozicio`).

**Terepi jelentés.** „Több befolyó vízből sosem lesz kevesebb kifolyó”, „a hosszmetszet a
forrástól a torkolatig lejt”. Ezek nem triviálisak: pontosan az ilyen *irányítási garanciák*
teszik lehetővé, hogy alsó és felső becsléseket adjunk hiányos adatokból (intervallumos,
szcenárió-alapú következtetés).

**Pozitív változás.** Bizonytalan bemenet mellett is adható **igazolt korlát**: ha a
csapadékbecslés `[r⁻, r⁺]` intervallumban van, a lefolyás garantáltan `[a⁻, a⁺]`-ban van. Ez
figyelmeztető rendszereknél sokkal védhetőbb, mint egyetlen pontbecslés.

---

## 5. mintázat — Lax struktúra: a hiány maga is kompozicionális (a szivárgás lokalizálható)

**Kategóriaelméletileg.** Amikor egy hozzárendelés nem szigorúan őrzi meg a szerkezetet, a
sérülés mértéke gyakran maga is szabályos: *lax* struktúrát, kociklust alkot. Itt a
vízmegőrzés a szigorú eset, a veszteség (`1 −` átvitel) a lax korrekció.

**A két könyvben.**

* Analízis: `veszteseg (d·c) = veszteseg d + d · veszteseg c` (`veszteseg_kompozicio`).
* Lineáris algebra: `veszteseg (M·N) j = veszteseg N j + ∑ₗ N l j · veszteseg M l`
  (`Vizhalozat.veszteseg_szorzat`), továbbá `merleg_veszteseggel`: kifolyás = befolyás −
  veszteségek.

Ez ugyanaz az azonosság egy és több dimenzióban.

**Terepi jelentés.** Karsztos (dolomitos, mészköves) vízgyűjtőn a legfontosabb kérdés:
*hol tűnik el a víz?* A kociklus-azonosság szerint két mérőpont közötti mérleghiány
**cellánkénti/szakaszonkénti járulékok súlyozott összege** — vagyis egymásba ágyazott
mérésekből a nyelő helye szűkíthető, nem csak a hiány ténye állapítható meg.

**Pozitív változás.** Konkrét terepi protokoll: egymásba ágyazott szelvényekben végzett
kisvízi hozammérés (nyomjelzős higítás) + a fenti bontás → a szivárgó szakasz azonosítása.
Ez közvetlenül szolgálja a forrásvédelmet és a vízkivételi engedélyek megalapozását.

---

## 6. mintázat — Fixpont és rekurzió: az akkumuláció és az önhasonlóság

**Kategóriaelméletileg.** Az induktív adattípus (patakhálózat mint bináris fa) *initial
algebra*; a rajta értelmezett rekurzív függvények (Strahler-rend, szakaszszám) katamorfizmusok.
Az `a = r + M·a` egyenlet fixpontja pedig a mértani (Neumann-) sorral áll elő.

**A két könyvben.** Analízis: `veszteseg_iteralt` (teleszkóp: `1 − cⁿ = ∑ cⁱ(1−c)`),
`akkumulacio_egyertelmu`. Lineáris algebra: `Vizhalozat.neumann_inverz`,
`lefolyas_kormentes`, `akkumulacio_fixpont`, valamint a Strahler-rend rekurzív definíciója és
Horton első törvénye (`horton_elagazasi_arany`).

**Terepi jelentés.** A lefolyás-akkumuláció (minden cella hozama = saját csapadéka + a felette
lévők hozama) **egyértelműen megoldható**, ha a hálózat körmentes; a megoldás a véges mértani
sor. A Strahler-rend rekurziója pedig a hálózat önhasonlóságát méri.

**Pozitív változás.** Ez a digitális terepmodellen futó lefolyásszámítás korrektségi
igazolása: az eredmény nem egy iteráció önkényes leállításának terméke, hanem az egyetlen
megoldás. A Horton-arány pedig olcsó, robusztus minőségi ellenőrzés (ha a térképezett
hálózaton az elágazási arány messze van a tipikus 3–5 sávtól, a hálózatkivonás küszöbe rossz).

---

## 7. Mit adnak együtt: a „feltáró kutatás” munkamenete

A hat mintázat egy konkrét, olcsó, egyszemélyes kutatási munkamenetté áll össze — ezt a
`ALPOK_DOLOMITOK_TEREPUTMUTATO.md` „fogadj örökbe egy vízgyűjtőt” terve részletezi:

1. **Bontsd fel** a vízgyűjtőt szakaszokra (1. mintázat: a felbontás szabad).
2. **Kalibrálj lokálisan**, és szorozd össze (2. mintázat: funktorialitás).
3. **Kérdezd meg, mi a legkisebb elegendő** mérőhálózat / védelmi szint (3. mintázat).
4. **Adj garantált korlátokat**, ne csak pontbecslést (4. mintázat).
5. **Mérj egymásba ágyazott szelvényekben**, és bontsd fel a mérleghiányt (5. mintázat) —
   ez a karsztkutatás magja.
6. **Ellenőrizd a hálózatkivonást** a rendstatisztikákkal, és oldd meg az akkumulációt zárt
   alakban (6. mintázat).

## 8. Ami még hiányzik (a formalizáció következő lépései)

* **Nyílt hálózatok kategóriája** (kospánok): a részvízgyűjtő mint nyílt rendszer, be- és
  kimeneti határral; a ragasztás mint pushout. Ez tenné teljesen precízzé az 1. mintázat
  „darabolható” állítását.
* **Monoidális funktor**: az akkumuláció mint monoidális funktor a nyílt hálózatok
  kategóriájából a lineáris relációk kategóriájába.
* **Strahler-rend mint funktor** a rang-posetbe, és az önhasonlóság mint endofunktor
  fixpontja.
* **Mérési adatok mint kéve (sheaf)**: a lokális mérések összeragaszthatósága; a
  *ragasztási akadály* (a `H¹`-szerű hiba) pontosan a nyelők/források helyét mutatná — ez a
  5. mintázat elvi általánosítása.

## 9. Óvatosság

A fenti állítások **matematikai** garanciák a modellezett struktúrára; nem helyettesítik a
terepi validációt. A monotonitási és mérleg-állítások csak akkor érvényesek a valóságra, ha a
modell feltevései (körmentesség, időbeli állandóság, lineáris átvitel) teljesülnek. A
formalizáció haszna éppen az, hogy **világossá teszi, pontosan melyik feltevés hol lép be**.

---

## English summary

Both formalised textbooks — Leindler's *Analízis* and Szabó's *Bevezetés a lineáris algebrába* —
turn out to instantiate the **same six categorical patterns**, one in a continuous
one-dimensional setting, the other in a discrete multi-dimensional one:

1. **Category** (composition is associative and unital, and "good behaviour" is inherited):
   continuity of composites (5.5.2) vs. associativity of matrix/linear-map composition
   (2.5, 10.7). *Use:* a catchment may be split into reaches arbitrarily; modular, distributed
   monitoring is mathematically sound.
2. **Functor** (composition becomes multiplication): the chain rule (6.4.1) vs. the matrix of a
   composite (12.3). *Use:* sensitivities and transfer factors multiply along a chain — error
   budgeting and compositional calibration.
3. **Universal property / adjunction** (the *smallest* covering object): the supremum
   (completeness axiom) vs. the span of a set (6.10). *Use:* smallest sufficient flood-defence
   level; smallest gauge network that determines the model.
4. **Poset functor** (order-preserving maps compose): monotonicity (8.1.2) vs. non-negative
   matrices. *Use:* certified upper/lower bounds under uncertain inputs.
5. **Lax structure / cocycle** (the failure of conservation is itself compositional):
   `loss(d·c) = loss d + d·loss c` vs. `veszteseg (M·N)`. *Use:* a measured water-balance
   deficit decomposes into per-reach contributions, so **karst leakage can be localised**.
6. **Fixed point / initial algebra** (recursion resolved into a finite sum): geometric series
   vs. the Neumann series solving `a = r + M·a`, plus the Strahler recursion and Horton's law.
   *Use:* provably correct flow accumulation on a DEM; cheap quality control of extracted
   networks.

All statements listed here are machine-checked Lean theorems in this repository (see the two
`Mintazatok_Kategoriaelmelet.lean` modules and the two application modules
`Alkalmazas_Folyoprofil.lean`, `Alkalmazas_Vizhalozatok.lean`). Section 8 lists what is *not*
yet formalised (open networks as cospans, accumulation as a monoidal functor, measurement data
as a sheaf whose gluing obstruction localises sinks) — that is the natural next step.
