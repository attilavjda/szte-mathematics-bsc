# Folyók, hegyek, víz és fenntarthatóság — mi az átfedés ezzel a könyvtárral, és hogyan lehet belőle kutatás?

*Rivers, mountains, water and sustainability: how this formalization library overlaps with that
research theme, and what a BSc-level research programme could look like. Hungarian first,
English summary at the end.*

> **Megjegyzés a hivatkozott cikkről.** A megadott Quanta-cikket ebből a környezetből nem tudtam
> megnyitni (nincs internetelérés), ezért az alábbi megfeleltetés **nem** a cikk állításaira, hanem
> a folyóhálózatok *standard*, tankönyvi matematikájára épül (Horton- és Strahler-féle rendezés,
> Hack-törvény, lejtő–terület összefüggés, optimális csatornahálózatok energiaelve). Ha egy konkrét
> állítást a cikkből formalizálni szeretnél, elég idemásolnod a szövegét, és pontosan arra
> építhetjük a következő lépést.

---

## 0. Rövid válasz

Három, egymástól jól elkülönülő átfedés van, és mindhárom **valódi**, nem analógia:

| Terület a könyvtárban | Vízrajzi/hegyvidéki megfelelő | Mi ebből most **bizonyítva** van |
| --- | --- | --- |
| **Kalkulus (Leindler 5–8. fejezet, Kalkulus I. tematika, gyakorló feladatok)** | folyó hosszmetszete (függvénydiszkusszió), energiaminimum-elv, vízkészlet-mérleg | `Analizis/Analizis/Alkalmazas_Folyoprofil.lean` — 3 definíció, 11 tétel |
| **Lineáris algebra (Szabó-jegyzet, Lineáris algebra I. tematika)** | lefolyás-akkumuláció mátrixegyenlete, tömegmegmaradás, Horton–Strahler-rend | `LinearisAlgebra/LinearisAlgebra/Alkalmazas_Vizhalozatok.lean` — 7 definíció, 12 tétel |
| **Kategóriaelmélet (Lawvere–Schanuel, szorzatobjektum)** | terep = alaprajz × magasság (DEM), részvízgyűjtők összeillesztése, kompozicionális rendszerek | `*/Lawvere_SzorzatObjektum.lean` (korábbi menetből) + az új modulok kompozíciós tételei |

A „miért matematikai a folyó?” kérdés matematikai magja két dolog: **(a)** a hálózat *fa*, és a fák
rekurzív/kombinatorikus szerkezete törvényeket kényszerít ki (Horton–Strahler); **(b)** a folyó
hosszmetszete és a hálózat alakja egy *szélsőérték-feladat* megoldása (energiaminimum), és a
szélsőérték-feladat nyelve pontosan a derivált–konvexitás-apparátus, ami a jegyzet 6–8. fejezete.

---

## 1. Mi a folyóhálózatok matematikájának magja (röviden, fogalmanként)

1. **Strahler-rend és Horton törvényei (1945, 1957).** A patakhálózat bináris fa: két azonos rendű
   ág összefolyása eggyel magasabb rendű szakaszt ad. Horton „első törvénye” szerint az egyes
   rendekhez tartozó szakaszok száma közelítőleg mértani sorozat (elágazási arány `R_b`, a
   természetben tipikusan 3 és 5 között).
2. **Hack-törvény (1957).** A főág hossza és a vízgyűjtő terület között hatványösszefüggés van:
   `L ≈ c·A^h`, `h ≈ 0,57` — azaz a vízgyűjtők **nem** hasonlók, hanem *önaffinok*.
3. **Lejtő–terület összefüggés.** Egyensúlyi (graded) folyómederben `S ≈ k·A^(-θ)`; ebből és a
   Hack-törvényből a hosszmetszetre `z(x) = H - a·x^p`, `0 < p < 1` adódik: **monoton csökkenő,
   konvex** profil (a geomorfológus szóhasználatával „felfelé konkáv”).
4. **Optimális csatornahálózat (OCN).** A hálózat úgy áll be, hogy a `∑ Q_i^p · L_i` alakú
   energiafunkcionál minimális legyen (`p ≈ 1/2`). Mivel `0 < p < 1`, a `Q ↦ Q^p` költség
   **szigorúan konkáv**, ezért az áramokat *összevonni* olcsóbb, mint szétosztani — innen a
   fa-szerkezet.
5. **Tájfejlődés (stream power).** `∂z/∂t = U - K·A^m·|∇z|^n`: kiemelkedés mínusz erózió. Az
   állandósult állapot (`∂z/∂t = 0`) éppen a 3. pontbeli hatványprofil; a hegységek (Alpok,
   Himalája) magasságát a kiemelkedés és az erózió versenye szabja meg.
6. **Véletlen modellek.** Scheidegger-modell (véletlen bolyongás–folyóhálózat kapcsolat),
   egyenletes feszítőfák, önhasonló Tokunaga-statisztika — itt lép be a valószínűségszámítás.

---

## 2. Átfedések tételről tételre

### 2.1. Kalkulus gyakorló feladatok és a Leindler-jegyzet

A „kalkulus gyakorló feladatok” anyaga (függvénydiszkusszió, szélsőérték, határérték, középérték-tételek)
egy az egyben a vízrajz nyelve:

| Kalkulus-téma (meglévő modul) | Vízrajzi jelentés | Új, bizonyított állítás |
| --- | --- | --- |
| 8.8. **függvénydiszkusszió** (`Ch08e_FuggvenyDiszkusszio`) | a folyó hosszmetszetének teljes diszkussziója | `Vizrajz.profil_szigoruan_csokkeno`, `Vizrajz.profil_konvex` |
| 8.1.2. monotonitás deriválttal (`Ch08a`) | „a folyó mindenütt lejt” | `profil_szigoruan_csokkeno` |
| 8.6.1. konvexség a második deriválttal (`Ch08b`) | „a meredek hegyvidéki szakaszt lapos szakasz követi” | `profil_konvex` |
| 6.8.2. `(xᵃ)' = a·xᵃ⁻¹` (`Ch06b`) | a lejtő–terület hatványtörvény deriválása | `derivalt_profil`, `derivalt_profil'` |
| konkavitás / szubadditivitás | **miért egyesülnek a patakok** (OCN-elv) | `rpow_szig_szubadditiv`, `egyesules_olcsobb`, `szetvalas_dragabb` |
| 6.10.3. **Lagrange-középértéktétel** (`Ch06a`) | vízmérleg: tartós hiány ⇒ lineáris fogyás | `keszlet_fogyas` |
| 5.14.5. **Bolzano–Darboux** (`Ch05c`) | van olyan időpont, amikor a tároló *éppen* kiürül | `keszlet_kiurul` |
| 8.1.2. (nemnegatív derivált) | **fenntartható vízkivétel** feltétele | `keszlet_fenntarthato` |
| határérték `±∞`-ben, L'Hospital (`Ch05h`, `Ch06d`) | skálázási kitevők aszimptotikája (Hack-törvény) | *még nincs formalizálva → 3.1. lépés* |
| Weierstrass-tétel (`Ch05c`) | „van legmélyebb pont / maximális hozam” | meglévő tétel, közvetlenül alkalmazható |

### 2.2. Lineáris algebra (Szabó-jegyzet)

| Lineáris algebra téma | Vízrajzi jelentés | Új, bizonyított állítás |
| --- | --- | --- |
| mátrix mint irányított gráf | `M i j = 1`, ha a `j` cella vize az `i`-be folyik | `Vizhalozat.Kormentes` (nilpotens mátrix) |
| `(I - M)` invertálhatósága, mértani sor | **lefolyás-akkumuláció**: `a = r + M·a` | `neumann_inverz`, `lefolyas_egyertelmu`, `lefolyas_kormentes` |
| Leontyev-féle input–output modell (`Tematika.leontyev_egyenlet`) | **ugyanaz az egyenlet**, más értelmezéssel | a két modell azonossága kimondva a dokumentációban |
| oszlop-sztochasztikus mátrixok | **tömegmegmaradás** a hálózatban | `vizmegorzo_osszeg` |
| mátrixszorzás mint kompozíció (12.6.) | két lépés egymás után; a vízmegőrző hálózatok monoidot alkotnak | `vizmegorzo_szorzat`, `vizmegorzo_egyseg` |
| rekurzív fastruktúra | **Strahler-rend**, Horton I. törvénye | `rend`, `szam`, `rend_teljes`, `szam_teljes`, `horton_elagazasi_arany` |
| LU-felbontás, Cramer-szabály (`Tematika.lu_megoldas`) | nagy hálózatok numerikus megoldása | meglévő tételek, közvetlenül használhatók |
| sajátérték, Perron–Frobenius (`Ch14`) | stacionárius vízeloszlás, keveredés | *következő lépés → 3.2.* |
| Cauchy–Schwarz, legkisebb négyzetek (`Tematika.KalkulusI`, `Ch17`) | skálázási kitevő becslése log–log illesztéssel | *következő lépés → 3.3.* |
| determináns = térfogat (`Tematika.determinans_terfogat`) | terület-/térfogatszámítás, koordinátatranszformáció | meglévő tétel |

### 2.3. Kategóriaelmélet (Lawvere–Schanuel)

A Lawvere-részlet fő gondolata — `SPACE = PLANE × LINE`, `shadow` és `level` vetítésekkel — a
földtudományban **szó szerint** a digitális domborzatmodell: a terep egy `alaprajz ↦ magasság`
leképezés, egy térbeli pontot pedig a vízszintes vetülete és a magassága együtt határoz meg. Ez
már formalizálva van (`Lawvere_SzorzatObjektum.lean`, `galilei_univerzalis`, `folytonosSikba_iff`).

Ami ebből *kutatási* irányba mutat:

* **Kompozicionális hidrológia.** Egy részvízgyűjtő „nyílt rendszer”: van bemenete (felső határ) és
  kimenete (torkolat). Az ilyen rendszerek összeillesztése kospánokkal (cospan) írható le, és a
  „vízhozam-hozzárendelés” funktor: a rendszerek összeillesztésének a hozamok összeillesztése felel
  meg. Az itt bizonyított `vizmegorzo_szorzat` + `vizmegorzo_egyseg` pár ennek a legegyszerűbb
  (egyobjektumú, monoid) esete.
* **Kévék hálózaton (cellular sheaves).** A vízhozam/nyomás lokális adat, a konzisztencia
  (Kirchhoff-szabály) pedig kéve-feltétel; a kéve-Laplace-operátor lineáris algebrája pontosan a
  jegyzet 9–13. fejezetének gépezete.
* **Univerzális tulajdonság mint modellezési elv.** „A vízgyűjtő a részvízgyűjtőinek kolimesze” —
  ez pontosan az a fajta állítás, amelyet a Lawvere-könyv tanít, és amely a jelenlegi
  formalizációból hiányzik (nincs benne kategória/funktor fogalom).

---

## 3. Mit tud ez a könyvtár *most*, és mi a következő 3 lépés

### Ami elkészült ebben a menetben (mind `sorry`-mentes, a két projekt teljes `lake build`-je hibátlan)

**`Analizis/Analizis/Alkalmazas_Folyoprofil.lean`**

* `profil`, `profil'`, `profil''` — a `z(x) = H - a·x^p` hosszmetszet és deriváltjai;
* `derivalt_profil`, `derivalt_profil'`, `profil_continuousOn`;
* `profil_szigoruan_csokkeno` — a folyó mindenütt lejt (8.1.2. Tétel);
* `profil_konvex` — a profil konvex, ha `0 < p < 1` (8.6.1. Tétel);
* `rpow_szig_szubadditiv`, `egyesules_olcsobb`, `szetvalas_dragabb` — az OCN-elv magja:
  `(x+y)^p < x^p + y^p`, azaz **az egyesült meder olcsóbb, mint két külön meder**;
* `keszlet_fogyas`, `keszlet_kiurul`, `keszlet_fenntarthato` — vízkészlet-mérleg: fogyás üteme,
  kiürülés időpontja, a fenntarthatóság feltétele.

**`LinearisAlgebra/LinearisAlgebra/Alkalmazas_Vizhalozatok.lean`**

* `Kormentes`, `neumannOsszeg`, `neumann_inverz` — körmentes hálózat, `(I - M)⁻¹ = ∑ Mᵏ`;
* `lefolyas_egyertelmu`, `lefolyas_kormentes` — a lefolyás-akkumuláció egyértelmű megoldhatósága;
* `Vizmegorzo`, `vizmegorzo_osszeg`, `vizmegorzo_egyseg`, `vizmegorzo_szorzat` — tömegmegmaradás és
  a kompozícióra való zártság;
* `veszteseg`, `vizmegorzo_iff_veszteseg_nulla`, `veszteseg_szorzat`, `merleg_veszteseggel` —
  „szivárgó” (karsztos) hálózatok: a mérleghiány pontosan a veszteség, és a kompozíció során
  cellánkénti járulékokra bomlik (lásd `ALPOK_DOLOMITOK_TEREPUTMUTATO.md`);
* `Vizfolyas`, `rend`, `teljes`, `szam` — patakhálózat, Strahler-rend, teljes hálózat;
* `rend_teljes`, `szam_teljes_nagy`, `szam_teljes`, `horton_elagazasi_arany`, `rend_osszefolyas` —
  **Horton első törvénye bizonyítva**: a teljes bináris hálózatban a `k`-adrendű szakaszok száma
  `2^(n+1-k)`, tehát az elágazási arány pontosan 2.

### 3.1. lépés — a kalkulus-oldal kiterjesztése (könnyű, 1–2 hét)

* Hack-törvény és a skálázási kitevők **határérték-alakja**: `lim (log L / log A) = h` — a meglévő
  `Ch05h` (végtelenben vett határérték) és `Ch06d` (L'Hospital) modulokra épül.
* A hosszmetszet **teljes 8.8. diszkussziója** a `Ch08e` mintájára (értékkészlet, aszimptotika,
  inflexió hiánya, `x → 0+` viselkedés = a vízválasztó környéki meredekség).
* **Knickpoint** (lépcső a hosszmetszetben) mint szakadási/inflexiós pont: a `Ch05b`, `Ch08b`
  fogalmaival kimondható, hogy egy emelkedési ütem-ugrás után a profil két hatványszakaszból áll.
* **Manning-képlet** monotonitása: `v = k·R^(2/3)·S^(1/2)` szigorúan nő a lejtésben — egyszerű
  gyakorlat a `Ch06b` deriváltjaival, jó „gyakorló feladat” anyag.

### 3.2. lépés — a lineáris algebra-oldal kiterjesztése (közepes, 3–6 hét)

* **Horton II–III. törvénye** (hosszak és területek mértani sorozata) a `Vizfolyas` fán, hosszakkal
  dekorált fákra.
* **Shreve-magnitúdó** és Tokunaga-önhasonlóság: `magnitudo (osszefolyas l r) = magnitudo l + magnitudo r`,
  és a rend–magnitúdó egyenlőtlenség (`rend ≤ log₂ magnitudo + 1`).
* **Perron–Frobenius / Markov-lánc**: a vízmegőrző mátrixok stacionárius vektora (a `Ch14`
  sajátérték-anyagra építve).
* **Kirchhoff-mátrix és feszítőfák**: a hálózat Laplace-mátrixa, a fa-számláló tétel — az OCN
  modell diszkrét oldala.
* **Legkisebb négyzetek** a `Ch17` euklideszi tereire építve: a normálegyenlet megoldhatósága, ezzel
  a `log L ~ h·log A` illesztés hibabecslése.

### 3.3. lépés — az OCN-elv teljes, diszkrét bizonyítása (nehéz, de a legértékesebb)

**Sejtés/állítás:** rögzített csúcshalmazon, rögzített csapadékkal, ha a költség `∑ Q_e^p` alakú
`0 < p < 1` mellett, akkor **minden energiaminimalizáló lefolyási irányítás fa** (minden csúcsból
pontosan egy kifolyó él).

Ez a `rpow_szig_szubadditiv` állítás globális, kombinatorikus megfelelője: a szigorú konkávitás
miatt egy csúcsban a kimenő áram szétosztása mindig szigorúan drágább, mint az egy élre koncentrálás.
Lean-ben ez véges optimalizálási feladat (`Finset`-ek fölött), tehát reálisan formalizálható; a
könyvtárban jelenleg nincs meg, és jó BSc/TDK-témának tűnik.

### 3.4. lépés — kategóriaelméleti keret (kutatási, nyílt végű)

* `CategoryTheory` (Mathlib) fölött: **nyílt vízgyűjtők kategóriája** kospánokkal; a
  „lefolyás-akkumuláció” mint funktor; a `vizmegorzo_szorzat` általánosítása funktorialitási
  tétellé.
* **Kévék hálózaton**: a hozam mint kéve szekciója; a globális megoldhatóság mint `H⁰`, az
  ellentmondások (túlhasználat) mint `H¹` — ez adja a „mely részrendszerek nem illeszthetők össze
  fenntarthatóan” kérdés pontos alakját.

---

## 4. Víz és fenntarthatóság: hol tud a formalizáció valódi hozzáadott értéket adni?

A vízgazdálkodásban a modellek nagyok és numerikusak; a formalizáció ott hasznos, ahol egy
**garantált, ellenőrzött állítás** ér többet egy szimulációnál:

1. **Fenntarthatósági küszöbök gépi bizonyítással.** A `keszlet_fenntarthato` / `keszlet_kiurul`
   pár prototípusa annak, hogy egy vízkivételi szabályról *bizonyítható* legyen: adott
   utánpótlás mellett a készlet nem fogy el (vagy: legkésőbb `T` időpontban elfogy). Kiterjesztés:
   több tároló, késleltetés, szezonalitás (periodikus be/kifolyás), sztochasztikus utánpótlás alsó
   becsléssel.
2. **Vízkiosztási szabályok helyessége.** A vízmegőrző mátrixok kompozíciós tétele azt garantálja,
   hogy egy összetett elosztóhálózat nem „veszít” és nem „gyárt” vizet — ez pontosan az a fajta
   invariáns, amit egy döntéstámogató szoftverben verifikálni érdemes.
3. **Lineáris programozás / dualitás.** A tározó-üzemeltetés LP-feladat; a dualitás (árnyékárak =
   a víz határértéke) a lineáris algebra anyagra épül, és formalizálható (Farkas-lemma).
4. **Adatelemzés hibakorlátokkal.** A skálázási kitevők (Hack, lejtő–terület) becslésének
   érvényességi feltételei: mikor jogos a log–log illesztés? Cauchy–Schwarz és a legkisebb
   négyzetek formalizált változatával *bizonyított* hibakorlát adható.
5. **Hegyvidéki „víztornyok”.** Az Alpok és a Himalája hó- és gleccserkészlete a lefolyás
   szezonális pufferje. A legegyszerűbb hó-olvadás modell (degree-day: az olvadás a hőmérséklet
   pozitív részével arányos) monotonitási állításai ugyanazok, mint a `keszlet_*` tételek —
   ez a leggyorsabban elérhető, valóban „fenntarthatósági” formalizáció.

---

## 5. Hegyek: mi a matematikailag érdekes az Alpokban és a Himalájában?

* **Antecedens folyók.** A Himalája több nagy folyója (Indus, Szatledzs, Arun, Jarlung Cangpo /
  Brahmaputra) *átvágja* a hegyláncot: a folyó idősebb, mint a hegység, és a kiemelkedéssel lépést
  tartva vágta be magát. Matematikailag: az erózió és a kiemelkedés versenyének stabilitási
  kérdése — a stream-power egyenlet állandósult megoldásának létezése.
* **Erózió–tektonika visszacsatolás.** Ahol a folyó gyorsan vág (nagy csapadék), ott a kéreg
  kompenzálva gyorsabban emelkedik. Ez egy csatolt dinamikus rendszer; a legegyszerűbb változata
  egy 1D ODE, amelynek monotonitási és fixpont-tulajdonságai a jegyzet eszközeivel tárgyalhatók.
* **Vízválasztók vándorlása.** Két szomszédos vízgyűjtő versenyez; a vízválasztó akkor mozdul el,
  ha a két oldal `A^m S^n` értéke eltér — diszkrét dinamika a `Vizfolyas`-szerű fákon.
* **Hipszometrikus görbe.** Egy hegység magasság szerinti területeloszlása: monoton csökkenő
  függvény, alakja a hegység „érettségét” jellemzi — közvetlenül a függvénydiszkusszió témaköre.
* **Önaffin domborzat.** A hegyvidéki felszín magasságprofilja statisztikailag önaffin
  (Hurst-kitevő); a fraktáldimenzió fogalma Mathlibben elérhető (Hausdorff-dimenzió), tehát
  formalizálható állítások is megfogalmazhatók egyszerű önhasonló modellekre.
* **Érdekes tény.** A tökéletes bináris hálózat elágazási aránya pontosan 2 (`horton_elagazasi_arany`),
  a valódi folyóhálózatoké tipikusan 3–5 — a különbség maga is információ: a valódi hálózatok
  „laposabbak”, mint a teljes bináris fa, mert a kis patakok gyakran magasabb rendű ágba
  torkollanak (ezt írja le a Tokunaga-statisztika).

---

## 6. Hogyan illeszkedik mindez a meglévő ROADMAP-hez

A két projekt eddigi célja a **tankönyvhű** formalizáció volt (Leindler 3–8. fejezet, Szabó 1–18.
fejezet, plusz a két tantárgyi tematika). Az itt hozzáadott két modul szándékosan **külön,
„Alkalmazás” előtagú fájl**: nem módosítja a tankönyvi anyagot, csak épít rá, és minden bizonyítása
a jegyzetek saját tételeire hivatkozik. Ezzel a könyvtár egy új réteget kap:

```
tankönyv (Leindler / Szabó)  →  tematika (Kalkulus I., Lineáris algebra I.)  →  alkalmazás (vízrajz)
```

A 3.1.–3.4. lépések ugyanebbe a rétegbe illeszkednek, és mindegyik önállóan, külön fájlban
végezhető el.

---

## 6b. Terepmunka és mobilitás az Alpokban

Az „hol, kivel és mit csináljak ebből a témából a Dolomitokban / az Alpokban” kérdésre külön
útmutató készült: `ALPOK_DOLOMITOK_TEREPUTMUTATO.md` (intézménytípusok, kiket érdemes megszólítani,
szezonális naptár, egyszemélyes projektterv, és a hozzá tartozó kategóriaelméleti program).

---

## 7. English summary

This document maps the two formalized textbooks (Leindler, *Analízis*, ch. 3–8; Szabó,
*Bevezetés a lineáris algebrába*) and the Lawvere–Schanuel category-theoretic material onto the
mathematics of river networks, mountains and water sustainability.

**Newly formalized and proved in this session (both projects build cleanly, no `sorry`):**

* *Calculus side* (`Analizis/Analizis/Alkalmazas_Folyoprofil.lean`): the longitudinal river profile
  `z(x) = H − a·x^p` is strictly decreasing and convex for `0 < p < 1` (proved with the textbook's
  own monotonicity and convexity theorems); strict subadditivity of power costs
  `(x+y)^p < x^p + y^p`, i.e. the variational reason why streams merge (optimal channel networks);
  a water-balance package proved with the textbook's mean value theorem and Bolzano–Darboux theorem:
  a persistent deficit depletes storage at least linearly, storage hits zero in finite time, and
  withdrawal never exceeding recharge is exactly the sustainability condition.
* *Linear algebra side* (`LinearisAlgebra/LinearisAlgebra/Alkalmazas_Vizhalozatok.lean`): for an
  acyclic (nilpotent) routing matrix, `I − M` is invertible with Neumann inverse, hence the flow
  accumulation equation `a = r + M·a` has a unique solution (the same equation as the Leontief
  input–output model already in the library); column-stochastic routing preserves total water and
  is closed under composition (a monoid, i.e. a one-object category); and Horton's first law is
  proved for the complete binary network: there are `2^(n+1−k)` streams of Strahler order `k`, so
  the bifurcation ratio is exactly 2.

**Research options** (Sections 3–5): extending the tree module to Horton's laws of lengths and areas,
Shreve magnitude and Tokunaga self-similarity; Perron–Frobenius and Kirchhoff/spanning-tree theory;
verified least-squares estimation of scaling exponents; a full discrete proof that energy-minimizing
drainage configurations are trees (the most valuable of these directions); compositional (cospan/sheaf-theoretic) models of open catchments; and degree-day
snow/glacier storage models for Alpine and Himalayan "water towers", which reuse the water-balance
theorems verbatim.
