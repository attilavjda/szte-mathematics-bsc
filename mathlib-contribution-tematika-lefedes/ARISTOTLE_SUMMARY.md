# Summary of changes for run a47ea138-cc4d-43c6-a331-8b61f95d0bec
Frissítettem mind a négy oklevél-változatot (`Oklevel/oklevel-A-klasszikus`, `-B-modern`, `-C-akademiai`, `-D-kalligrafikus`, `.tex` + újrafordított `.pdf`), és minden kért adatot beletettem.

**Mi került bele**

1. **GitHub-repó.** A korábbi helykitöltő link helyére mindenhol (1. és 2. oldal) a valódi cím került: `https://github.com/attilavjda/szte-mathematics-bsc`. Ellenőriztem, hogy a repó nyilvánosan létezik.
2. **Tematika ↔ PR táblázat merge-pipákkal.** Az oklevelek 2. oldalán új, 20 soros táblázat: a Kalkulus I Neptun-tárgytematika minden pontja (T‑1 … T‑20), mellette a hozzá tartozó pull request (vagy benyújtásra kész patch / PR-jelölt), és egy „Merge” oszlop: ✔ = a ponthoz tartozó PR bekerült a Mathlib `master` ágába, üres négyzet = még nem. Pipát a **T‑2, T‑12, T‑13, T‑16, T‑18** pont kapott.
3. **Merge-elt PR-ok linkjei a diffekhez.** A 3. oldalon külön táblázat a hat merge-elt pull requestről: kattintható PR-link (a nyilvános diffhez), a `master`-beli merge-commit, dátum és a hozzá tartozó tematikai pont — #42810 (Darboux), #42579 (konvexitás, hibás állítás javítása), #42592, #42763, #42907, #42493. A státuszokat ma közvetlenül a GitHubról ellenőriztem: 18 beküldött PR, ebből 6 merge-elt (a Mathlibben `bors` merge-el, ezért a cím `[Merged by Bors]` előtaggal szerepel — ezt a lap meg is magyarázza).
4. **A két könyv formalizációja.** Új szakasz az oklevél 3. oldalán és említés a díszes 1. oldal méltatásában is: Szabó László *Bevezetés a lineáris algebrába* → `linearis-algebra/`, Leindler László *Analízis* → `kalkulus/`, ugyanabban a nyilvános repóban, Lean 4 (Mathlib) formalizációként, nyílt forráskódú hozzájárulásként. A pontosság kedvéért lábjegyzetben jelezve, hogy a jegyzék lezárásakor (2026‑08‑30) a repóban a `README` volt közzétéve, a két könyvtár feltöltése folyamatban.
5. **Összesítő számok javítva** az 1. oldalon: „6 merge-elt pull request (18 beküldöttből) · 18 saját Lean-modul · 0 `sorry`”.

**Karbantarthatóság.** Az adatokat egyetlen közös fájlba tettem (`Oklevel/oklevel-adatok.tex`: repó-URL, tematika-táblázat, merge-elt PR-ok, könyvek), amelyet mind a négy változat beolvas, és csak a megjelenítést (booktabs vagy sávos, színes fejléc) adja a saját stílusa — így új merge esetén elég egy helyen frissíteni. Mind a négy PDF hibátlanul lefordul (tectonic/XeTeX), és most 3 oldalas.

Frissítettem a kapcsolódó leírásokat is: `Oklevel/README.md` (új szerkezet, adatforrások, mi cserélendő beadás előtt), a projekt `README.md` (repó-link, merge-elt PR-linkek, `Oklevel/` sor a belépési pontok táblázatában) és a `KALKULUS-TEMATIKA-PR-TABLAZAT.md` (új 1/b. szakasz a repóról és a két tankönyv-formalizációról). A Lean-könyvtárhoz nem nyúltam, továbbra is `sorry`-mentes. Minden változtatás commitolva és feltolva.

# Summary of changes for run 006f578b-417c-4c0a-a5ca-5de480779c55
## Mit csináltam

A csatolt archívumból kibontottam a **`pr-attekintes/`** mappát, és **bemásoltam a projektbe** (`pr-attekintes/`: `pr_attekintes.pdf` + `.tex` forrás, `README.md`, és a hat, ma is tisztán illeszkedő patch a `patches/` alatt). Ezután a benne felsorolt **valódi Mathlib pull requesteket hozzáfűztem a tematika-megfeleltetési táblázathoz**, pipákkal.

### Ellenőrzés (nem csak átvettem az adatokat)
A PR-státuszokat **ma, közvetlenül a GitHubról** kérdeztem le (`author:attilavjda`, 18 PR), és a merge-elteket a Mathlib `master` git-történetében is visszakerestem — a Mathlibben `bors` merge-el, ezért a GitHub API `merged` mezője félrevezetően `false`, a bizonyíték a `[Merged by Bors]` cím + a `master`-beli commit:

| PR | merge-commit | dátum |
|---|---|---|
| #42810 (Darboux) | `e72c1e277` | 2026‑08‑18 |
| #42579 (konvexitás, hibás állítás) | `8fecc3d4d` | 2026‑08‑13 |
| #42592 | `4a3cbc9c7` | 2026‑08‑10 |
| #42763 | `bec97d68e` | 2026‑08‑15 |
| #42907 | `4ac22c7ef` | 2026‑08‑18 |
| #42493 | `3cf9c0a79` | 2026‑08‑10 |

Ellenőriztem a mai `master` forrását is: a Darboux-fájlban a két javított lemma külön állítás, a `Monotone.convex_gt` pedig a dualitáson keresztül van levezetve — azaz **mindkét javítás benne van** a Mathlibben.

### A `KALKULUS-TEMATIKA-PR-TABLAZAT.md` változásai
* A T‑1…T‑20 főtáblázat kapott egy **új „(C) beküldött PR” oszlopot**: **✅ = már merge-elve** a `master`-be, **⬜ = még nincs** (nyitott, merge nélkül lezárt, vagy be sem küldött).
* Új **2/b. szakasz** mind a 18 PR-ral, három táblázatban (6 merge-elt ✅ / 9 nyitott ⬜ / 3 merge nélkül lezárt ⬜), tematikaelemmel és a kapcsolat erősségével.
* Ahogy kérted, a **Darboux-PR (#42810)** pipát kapott a **T‑16** („Monotonitás és derivált — a derivált Darboux-tulajdonsága”, erős kapcsolat), plusz T‑12 és T‑13 közvetett kapcsolattal. Merge-elt PR fedi még: **T‑2** (#42592, #42763, #42907) és **T‑18** (#42579, tartalmi hibajavítás a konvexitásban). Nyitott PR (⬜) kapcsolódik a T‑1, T‑4, T‑8, T‑9, T‑13 pontokhoz; a többi elemnél ⬜ „nincs beküldve”.
* Frissítettem az őszinteség-záradékot és a „mit nem állít” szakaszt: most már **világosan elkülönül** a (B) oszlop (benyújtásra kész patch, PR-szám nélkül) és a (C) oszlop (valódi, számmal hivatkozható PR, ✅ = a `master`-ben van, merge-committal).
* A kreditátviteli teendők táblázatában a T‑2, T‑11–T‑12, T‑15–T‑17 és T‑18 sorokhoz odaírtam a csatolható merge-elt PR-okat.

### Egyéb frissítések
* `KALKULUS-TEMATIKA-MATHLIB-4.34-PRJELOLTEK.md`: figyelmeztetés, hogy ott a ✅ „kész patch”-et jelent, nem merge-et, hivatkozással az új (C) oszlopra.
* `KOMPETENCIA-LEFEDETTSEG.md` és `README.md`: kereszthivatkozás az új oszlopra és a `pr-attekintes/` mappára.

A Lean-könyvtár változatlan, továbbra is `sorry`-mentes. Minden változtatás commitolva és feltolva.


# Summary of changes for run 3cce36a9-fcaf-47fe-9cf9-b5cdfacc842a
## Mit készítettem

Létrehoztam a kért Markdown-fájlt: **`KALKULUS-TEMATIKA-MATHLIB-4.34-PRJELOLTEK.md`**.

A `KalkulusIelőadás-3.pdf` **„Tantárgy tartalma”** mezőjének minden egyes elemét **külön szakaszra bontottam** (T‑1 … T‑20: a valós számtest, teljes indukció, nevezetes egyenlőtlenségek, elemi függvények és inverzeik, értelmezési tartomány/értékkészlet/kompozíció, grafikonok és szimmetria, függvénytranszformációk, határérték és annak formális tulajdonságai, határérték-számítási technikák, folytonosság, középérték-tétel és kompaktság, derivált és érintő, láncszabály és implicit deriválás, középérték-tételek, monotonitás, szélsőértékek, konvexitás, függvényvizsgálat, L'Hospital), és **mindegyikhez kizárólag a hozzá tartozó Mathlib-hozzájárulást** adtam meg — a hozzájárulás olyan típusú, amit a maintainerek „near‑unambiguously improvement”-nek tekintenek, *és* matematikailag az adott tematikai pontot fedi le.

## A vizsgált bázis

Nem a projekt rögzített Mathlib-verziója ellen dolgoztam, hanem a **mai upstream master** ellen: `leanprover-community/mathlib4`, commit `58e016c6f6c829b5f25b1a87a88f495f40e70aa7` (2026‑08‑29), toolchain `leanprover/lean4:v4.34.0-rc2` — ez a „4.34”.

## Ellenőrzött patchek

A `mathlib-prs/master-4.34/` mappában **21 benyújtásra kész patch** található (+ README a bázissal és az ellenőrzés módjával). **Mind a 20 tematikai ponthoz tartozik legalább egy kész patch.** Minden patch alkalmazása után az érintett fájlokat lefordítottam a fenti commit ellen, hibaüzenet nélkül; a törölt `deprecated` aliasokra pedig ellenőriztem, hogy 0 hívóhelyük van az egész repóban (Mathlib, Archive, Counterexamples, MathlibTest). A patchek most, a dokumentum lezárásakor mind tisztán alkalmazódnak a bázis-commitre.

A típusok szerinti megoszlás:
- **12 tiszta törlés** (0 hozzáadott sor): lejárt `deprecated` aliasok a teljességi axióma, a rendezett struktúrák, a Hölder-egyenlőtlenség, a polinomok végtelenbeli viselkedése, a `logDeriv`/exp, a `Function.partialInv`, az intervallum-egyesítések, a határértékek, a `ContinuousOn` elgépelt nevei, az `IsBigO`, a láncszabály `_of_eq` változatai és a körintegrál-átlagok körül.
- **2 maintainer-TODO végrehajtása:** a `Filter.Tendsto.*_atTop'` család átnevezése (+ 4 feleslegessé vált explicit `to_additive` argumentum törlése), illetve a kompakt halmazon vett lokális szélsőérték-tételek általánosítása, ahol **két hipotézis helyére egy** kerül (`s ⊆ t` + `IsOpen s` → `t ∈ 𝓝ˢ s`), az egyetlen hívóhely átvezetésével.
- **3 hibás/elavult docstring javítása**, köztük egy nem létező tételre hivatkozó dokumentáció és két docstring, amely az állításnál erősebbet ígért.
- **1 deduplikáció** (14 sor duplikált bizonyítás → 7 sor).
- **4 szimmetria-hézag pótlása:** `Function.Even/Odd` hiányzó `neg`/`sub` lemmái; egy félrevezető nevű antiperiodikus lemma átnevezése a periodikus párjához igazítva (+ `deprecated alias`); a `ConcaveOn` hiányzó három `isMaxOn_*` duálisa; a `deriv` névtérből hiányzó `lhopital_zero_left_on_Ioc`.

Két patch **dátumhoz kötött** (a bennük törölt deprecationök 2026‑09‑11, illetve 2026‑09‑18 / 2026‑10‑07 után lesznek 6 hónapnál régebbiek) — ezt a dokumentum jelöli.

## Fontos őszinteségi megjegyzés

**Ezek nem beküldött vagy merged pull requestek**, hanem gépileg ellenőrzött, benyújtásra kész diffek: a nevedben nem nyújtottam be PR-t. A dokumentum tartalmazza a reprodukálás és a benyújtás lépéseit is, valamint azt a figyelmeztetést, hogy a lejárt aliasokat egy havi ütemezésű upstream munkafolyamat is törölheti, ezért az ilyen patcheket beküldés előtt érdemes újra ellenőrizni.

A `README.md`-ből hivatkoztam az új dokumentumra, hogy elkülönüljön a korábbi, rögzített bázisú táblázattól. A projekt Lean-könyvtára változatlan és továbbra is `sorry`-mentes. Minden változtatás commitolva és feltolva.

# Summary of changes for run c29efdb0-b7f3-4892-84de-a6feb6b52a12
## Mit készítettem el

### 1. `KALKULUS-TEMATIKA-PR-TABLAZAT.md` — a kért táblázat

A `KalkulusIelőadás-3.pdf` (Neptun Tárgytematika, Kalkulus I előadás, MBLK37E) **„Tantárgy tartalma”** mezőjét elemekre bontottam (**T‑1 … T‑20**: „A valós számtest. Teljes indukció. Nevezetes egyenlőtlenségek. …” → az utolsó elem a L'Hospital-szabályok), és minden elemhez megadtam:

* **(A) saját, gépileg ellenőrzött Lean-bizonyíték** — melyik modul melyik tétele fedi le (deklarációnevekkel);
* **(B) Mathlib-hozzájárulás** — melyik kész patch tartozik hozzá a `mathlib-prs/` mappából, és mi a státusza a mai upstream masterhez képest; ahol nincs kész patch, ott **konkrét, a rögzített Mathlib-bázison ellenőrzött PR‑jelölt** (fájl + sorszám), pl. L'Hospital `LHopital.lean:53–54`, Hölder `MeanInequalities.lean:872`, arkuszfüggvények `Trigonometric/Inverse.lean:293–294`, féloldali határértékek `Topology/Order/LeftRight.lean:67`, darabonként definiált függvények folytonossága `Topology/Piecewise.lean:95`, láncszabály magasabb rendben `ContDiff/FaaDiBruno.lean:291,340`, középértéktétel `Calculus/MeanValue.lean:585`;
* **miért high‑leverage** — külön fejezet rangsorolja a hozzájárulás-típusokat (hibás állítás javítása > hiányzó tétel pótlása > bizonyítás átírása linter-kivétel megszüntetéséhez > deduplikáció > tiszta törlés) és megmondja, mit bizonyít mindegyik a bizottság felé;
* **mit kell tenni a kreditátvételhez** — pontonként: mit csatolj bizonyítékként, mi a gyenge pont és mivel pótold (a TVSZ 3. sz. melléklet 3.8., 4.1. b), 4.2., 4.4., 4.5. pontjaira hivatkozva);
* **kereső-receptek**, amivel magad is találsz jelöltet: tematikai pont → Mathlib-könyvtár megfeleltetés + négy konkrét `rg`-parancs + a benyújtás előtti ellenőrző lépések.

Mérleg: a 20 tematikai elemből **20-hoz** van saját, `sorry`-mentes bizonyíték (100 %); **14 elemhez** kapcsolható Mathlib-hozzájárulás vagy ellenőrzött PR‑jelölt (70 %), ebből **7 elemhez** kész, benyújtható patch (35 %).

**Fontos, hogy ne legyen félreértés:** PR‑számot egyik sorhoz sem írtam, mert a `mathlib-prs/` alatti diffek *benyújtásra kész* patchek, nem merged pull requestek. A jelöltek fájl+sorszám találatai a projekt rögzített Mathlib-bázisára (`8f9d9cf`, Lean 4.28.0) vonatkoznak; benyújtás előtt a mai masteren újra kell ellenőrizni őket.

### 2. Új Lean-modul: `RequestProject/Kreditelismeres/KalkulusTematika.lean`

Azokat a tematikai pontokat, amelyeket a korábbi modulok még nem fedtek le, formálisan bebizonyítottam (mind `sorry` nélkül fordul, csak a standard axiómákra épül):

* **T‑1** `isLUB_sqrt_two` (a teljességi axióma √2‑t állít elő ⇒ ℚ nem elég), `archimedean_real`;
* **T‑2** `sum_odd_eq_sq` (szokásos indukció), `exists_prime_dvd_of_two_le` (erős indukció);
* **T‑3** `abs_sum_le_sum_abs'`, `am_gm_three`;
* **T‑4** `polynomial_continuous`, `rational_continuousAt`, `sqrt_inverse_on_nonneg`, `arctan_tan_inverse`;
* **T‑5** `range_sq`, `exists_inverse_iff_bijective`, `comp_injective_surjective`;
* **T‑6** `sq_symmetry_monotonicity`, `sin_periodic_odd`;
* **T‑7** `graph` + `graph_translate`, `graph_scale_shift`, `graph_reflect_y` (függvénytranszformációk grafikonszinten);
* **T‑13** `tangentLine`, `hasDerivAt_iff_tangentLine` (elsőrendű érintkezés), `tangent_slope_unique`;
* **T‑14** `implicit_deriv_circle` (implicit deriválás az x²+y²=1 görbén);
* **T‑19** teljes függvényvizsgálat az `x³ − 3x` függvényen: derivált, második derivált, monotonitási intervallumok, lokális szélsőértékek, konvexitás/konkávitás, inflexiós pont.

### 3. A projekt buildje helyreállt

A korábbi állapotban a Lean-fájlok a projekt gyökerében voltak, miközben a `lakefile.toml` a `RequestProject/` könyvtárat célozza, és a modulok is `import RequestProject.…` sorokat használnak — így a `lake build` valójában semmit sem fordított. Visszaállítottam a szerkezetet (`RequestProject/`, `mathlib-prs/`, `mathlib-scan/` a dokumentációban hivatkozott módon). Most a **teljes projekt hibátlanul és figyelmeztetés nélkül fordul** (`lake build`), és a `sorry`-keresés 0 találatot ad.

A `README.md` kapott egy „belépési pontok” táblázatot, a `KOMPETENCIA-LEFEDETTSEG.md` pedig kereszthivatkozást az új tematika-táblázatra. Minden változás commitolva és feltöltve.


# Summary of changes for run 20d0e99e-b1b1-4f4a-8072-0415c20bf320
Elkészítettem az önkéntes munka oklevelet **négy különböző dizájnváltozatban**, mindegyiket `.tex` forrással és lefordított, **kétoldalas PDF**-fel, az `Oklevel/` mappában (a `README.md` a mappában összefoglalja a változatokat, a fordítás módját és a beadás előtt cserélendő elemeket).

**A négy változat** (eltérő betűk, színvilág, díszítés és szövegezés, azonos tartalmi adatokkal):

| Fájl | Stílus | Betűk | Díszítés |
|---|---|---|---|
| `oklevel-A-klasszikus` | klasszikus arany–sötétkék, pergamen alap | Times-jellegű | hármas keret, legyező-sarokdíszek, körpecsét („LEAN 4 · MATHLIB · OPEN SOURCE”) |
| `oklevel-B-modern` | minimalista türkiz–grafit–korall | groteszk (Helvetica-jellegű) | bal oldali színsáv függőleges felirattal, hatszög-jelvény, KPI-kártyák, sávozott táblázatok |
| `oklevel-C-akademiai` | akadémiai bordó–mohazöld, krém alap | Palatino-jellegű | hullámos „guilloche” keret, babérkoszorús V A monogram, kurzív megfogalmazás |
| `oklevel-D-kalligrafikus` | kalligrafikus tintakék–szépia | kancelláris kalligrafikus + Palatino | tollvonás-cirádák, sarokörvények, monogram-medál és **halvány kalkulus-vízjelek** a háttérben (Newton–Leibniz-formula, differenciahányados, ε–δ, az `e` határértéke, Taylor-sor, `d/dx sin x`, Moivre, rangszámtétel) |

**Minden változat felépítése:**
1. **oldal – az oklevél:** „Önkéntes munka oklevél”, Vajda Attila nevére, a Lean 4 / Mathlib nyílt forráskódú könyvtárhoz végzett önkéntes, nyilvánosan bírált hozzájárulásokért (kiemelten kalkulus/analízis és lineáris algebra), díszkerettel, pecséttel/medállal, dátum- és aláírássávval, „MVP-tervezet” megjegyzéssel.
2. **oldal – bizonyítékjegyzék:** repository-link (helykitöltő GitHub-cím) és upstream Mathlib-link, alapverzió (Lean 4.28.0, Mathlib v4.28.0, pinned commit); **lefedettségi táblázat** (Kalkulus I 18/18 = 100 %, ebből 9 ponthoz Mathlib-hozzájárulás is = 50 %; Lineáris algebra I 8/8 = 100 %, ebből 7 blokk = 87,5 %); a **17 benyújtásra kész PR/patch** táblázata (mit tesz, patch-fájl neve, melyik tematikai ponthoz tartozik); végül a **saját Lean-modulok ↔ tematika** megfeleltetés (KalkulusHatarertek, KalkulusDifferencial, LinAlgKomplexVektor, LinAlgMatrixDeterminans, valamint a további tárgyak portfólió-moduljai).

A számadatok a repó meglévő dokumentumaiból származnak (`KOMPETENCIA-LEFEDETTSEG.md`, `MATHLIB-PR-JAVASLATOK.md`, `MASTER-2026-08-STATUS.md`); a Lean-forrásokban `sorry`-keresés 0 találatot ad. A PR-ok státusza a lapokon őszintén „benyújtásra kész”-ként szerepel, a repo-link pedig jelölten helykitöltő. Minden változás commitolva és feltöltve.

# Summary of changes for run 20afc380-4a31-478e-b3e1-05efb3a073da
## Mit fejeztem be ebben a menetben

**1. A Lean-könyvtár készen áll a beadásra (MVP).**
A Kalkulus I és a Lineáris algebra I kreditelismerési anyaga hiánytalan: a `RequestProject/` alatti mind a 17 modul (köztük `Kreditelismeres/KalkulusHatarertek.lean`, `Kreditelismeres/KalkulusDifferencial.lean`, `Kreditelismeres/LinAlgKomplexVektor.lean`, `Kreditelismeres/LinAlgMatrixDeterminans.lean`) **`sorry` nélkül, hiba és figyelmeztetés nélkül fordul** a projekt rögzített Lean 4.28.0 / Mathlib `v4.28.0` verziójával. Ellenőrizve teljes build + `sorry`-keresés (0 találat).

**2. Lezártam a legfrissebb Mathlibbel való kompatibilitás nyitott pontjait.**
A korábbi próbafordításkor a mai Mathlib master (Lean `v4.34.0-rc2`) alatt hat modul még hibázott. Ezeket **verziófüggetlenül** javítottam ki — vagyis ugyanaz a forrás fordul a rögzített verzióval és a masterrel is:

* `Portfolio/Kalkulus.lean` – 3 helyen `simpa using` → közvetlen `exact` (a `Tendsto`-cél pontonkénti vs. `Pi`-alakja miatt);
* `Kreditelismeres/KalkulusDifferencial.lean` – `simpa` → `rwa [sub_self]`; a Taylor-tételhez új `taylor_mean_remainder_lagrange_Icc` burkoló, amely a Mathlib régi (`Icc`, `a < b`) és új (`uIcc`/`uIoo`, `a ≠ b`) szignatúráját is kiszolgálja;
* `Kreditelismeres/LinAlgKomplexVektor.lean` – explicit típusú `have` a `congrFun` után;
* `Portfolio/Automatak.lean` – 4 helyen a `Language.mem_leftQuotient` explicit alkalmazása;
* `Portfolio/Szamitastudomany.lean` – a Rice-tétel alkalmazásánál explicit egyenlőség-típusú `have`;
* `Kreditelismeres/KalkulusHatarertek.lean` – a fenti javításokkal áttételesen rendben.

Eredmény: **mind a 17 modul hibátlanul lefordul a mai Mathlib master ellen is** (ott csak néhány `deprecated` figyelmeztetés marad: `push_neg`, `if_pos`, `if_neg` — ezek a rögzített verzióban még a hivatalos nevek). A `lean-toolchain` / `lake-manifest.json` szándékosan változatlan, hogy a beadott build a rögzített verzióval reprodukálható maradjon.

**3. Dokumentáció frissítve.**
A `mathlib-prs/MASTER-2026-08-STATUS.md` 7. szakaszát pontosítottam: táblázatba szedtem, melyik modulban mi tért el a legújabb Mathlibhez képest és milyen javítás oldotta meg, valamint rögzítettem a végeredményt (17/17 modul mindkét verzióval fordul). A korábbi menetek Mathlib-hozzájárulási anyaga változatlanul a `mathlib-prs/master-2026-08/` mappában található, a kreditelismerési dosszié pedig a `KREDITELISMERES.md`, `PORTFOLIO.md` és `KOMPETENCIA-LEFEDETTSEG.md` fájlokban (a `KREDITELISMERES.md` C.5. és C.6. szakasza a Kalkulus I, illetve a Lineáris algebra I kérelem tanulási eredmény ↔ bizonyíték mátrixa, a D. szakasz az indoklás-sablon, az E. szakasz a beadás előtti ellenőrzőlista).

Minden változás commitolva és push-olva.


# Summary of changes for run 5bf77d3c-e77f-4703-998a-8e68c8c8e1b0
## Mit tartalmaz a projekt most

### 1. `KREDITELISMERES.md` — a kérdésedre adott válasz (magyarul)

Végigolvastam a repóban lévő `kreditatviteli_tajekoztato_hallgatoknak_2026_27_.pdf`-et, és ebből építettem fel egy teljes „mit kell tenni" dossziét:

- **A jogalap:** a **3.8. pont** kifejezetten megengedi a kreditelismerést *validáció* formájában, nem felsőoktatásban szerzett kompetenciák, informális tudás, tanulási eredmények vagy munkatapasztalat alapján — pontosan ez a te eseted.
- **A legerősebb érv:** a **4.1. b) pont** szerint a Bizottság **nem tagadhatja meg** a kreditet, ha a megszerzett kompetenciák (tanulási eredmények) aránya eléri a kiváltandó tanegység tanulási eredményeinek **75%-át**. Ezért a portfólió gerince egy **tanulási eredmény ↔ bizonyíték mátrix**, számszerűsített lefedettséggel.
- **A 4.4. pont** kimondja, hogy ugyanaz a kompetencia **több tárgyra vonatkozó párhuzamos kreditelismerés alapja is lehet** — ezt érdemes szó szerint idézni.
- **A 4.2. pont** engedi, hogy a Bizottság az „ismeretek alkalmazásának gyakorlását", a ráfordított munkaidőt és a számonkérési rendszert is mérlegelje — itt a gépi típusellenőrzés + maintaineri code review erős érv.
- Formai rész: **Modulo → rendes kérelem, kérelmenként egyetlen tárgyelem** (tehát hat külön kérelem), 3.1./3.3./3.5./5./6./8. pontok követelményei táblázatban, a **2026/27-es határidők**, valamint a 4.5. szerinti **előzetes kreditátviteli döntés** lehetősége.
- Külön fejezet arról, hogyan lesz a nyílt forráskódú bizonyíték formálisan is „hiteles igazolás" (PR-permalinkek, commit-hashek, build-napló, FBK-s támogató levél, maintaineri visszaigazolás, **tárgyfelelős oktatói ellenjegyzés** — a 3.3. szerint az oktató aláírása + tanszéki pecsét hitelesít).
- **Tárgyanként** (mind a hatra) tanulási eredmény ↔ bizonyíték táblázat, őszinte **hiányelemzés** és pótlási terv, kész **indoklás-sablon** a Modulo mezőhöz, és beadás előtti ellenőrzőlista.
- Reális várakozás: a Logika, Számítástudomány alapjai, Automaták, Kriptográfia és Lineáris algebra jól lefedett; a **Kalkulus I a legkockázatosabb** (számolási rutin, Riemann-integrál) — erre külön pótlási javaslatokkal.

Fontos: jeleztem, hogy a csatolt tájékoztató az ETSZK változata (bár az egyetemi TVSZ 3. sz. melléklete alapján készült), a hat tárgy viszont TTIK-s, tehát a TTIK Kreditátviteli Bizottsága illetékes; ez nem hivatalos állásfoglalás, a kari sajátosságokat egyeztetni kell.

### 2. `PORTFOLIO.md` — a bizonyítéktár leltára

Tantárgyanként megadja: **melyik feladat/tétel ↔ melyik Lean-deklaráció**, ellenőrzési útmutatóval, plus egy táblázat a **külső projektjeidről** (Mathlib PR-ok, Kasami/APN, FBK Trento, CircomAudit, ArkLib, Cedar) és arról, melyik tárgy melyik tanulási eredményét igazolják.

### 3. A gépileg ellenőrzött Lean-portfólió elkészült

A korábbi munkából megmaradt öt hiányzó bizonyítást befejeztem, és egy továbbit is hozzátettem. **A projekt `lake build`-del hibátlanul fordul, és egyetlen `sorry` sincs benne**; a kulcstételek csak a standard axiómákra (`propext`, `Classical.choice`, `Quot.sound`) épülnek.

Az újonnan bizonyított állítások:
- `isRegular_mul` — a reguláris nyelvek zártsága a **konkatenációra**;
- `isRegular_kstar` — zártság a **Kleene-iterációra** (segédlemmákkal: `cons_mem_kstar`, `kstar_split`);
- `isRegular_symmDiff` — zártság a szimmetrikus differenciára;
- `wwR_not_regular` — a `{w wᴿ}` nyelv nem reguláris (Myhill–Nerode-alapú bizonyítás);
- `squares_not_regular` — az `{aⁿ²}` nyelv nem reguláris;
- `ex_4_13` — **középponti konvexitás + folytonosság ⇒ konvexitás** (kompaktsági/minimalizálós bizonyítás).

Ellenőriztem, hogy `isRegular_mul`, `isRegular_kstar` és a középponti konvexitásról szóló állítás a projektben használt Mathlib-verzióban nem található meg (a `Language.IsRegular` névtérben csak `compl`, `add`, `inf`, `reverse` van; a `Mathlib/Analysis/Convex` alatt nincs midpoint-konvexitási állítás) — ezeket a `PORTFOLIO.md` upstream hozzájárulási célként is felsorolja, a még hiányzó nagyobb célokkal együtt (Kleene tétele, determinizálás, bonyolultságelmélet).

Minden munka commitolva és pusholva.

# Summary of changes for run 5a5a57ca-8f9f-43fc-afce-65908b6d8bf8
Elkészült tárgyanként egy-egy Lean 4 fájl, mindegyikben a kurzus néhány központi tételével, **teljesen bebizonyítva** — a projekt `lake build`-del hibátlanul fordul, és egyetlen `sorry` sincs benne.

**Automaták és formális nyelvek** (`RequestProject/AutomatakEsFormalisNyelvek.lean`)
- `prodDFA` / `accepts_prodDFA`, `unionDFA` / `accepts_unionDFA`, `complDFA` / `accepts_complDFA`: a felismerhető nyelvek zártsága metszetre, unióra, komplementerre.
- `parityDFA` / `parityDFA_accepts`: konkrét automata, amely pontosan a páros sok „a” betűt tartalmazó szavakat ismeri fel.
- `anbn` / `anbn_not_recognizable`: az `{aⁿbⁿ}` nyelvet semmilyen véges determinisztikus automata nem ismeri fel (a pumpáló lemma mögötti skatulyaelv közvetlen alkalmazásával).

**Logika és informatikai alkalmazásai** (`RequestProject/Logika.lean`)
- Az ítéletkalkulus szintaxisa (`PFormula`), szemantikája (`eval`, `Entails`) és egy Hilbert-kalkulus (`Hilbert`: K, S, `¬¬A → A` + modus ponens).
- `Hilbert.soundness` (helyességi tétel), `Hilbert.deduction` (dedukciótétel, mindkét irány), `Hilbert.weaken`, `Hilbert.id'`, `Hilbert.consistent`.

**A számítástudomány alapjai** (`RequestProject/SzamitastudomanyAlapjai.lean`)
- `words_countable`, `languages_not_countable` (Cantor-átló), `instFiniteDFA`, `recognizableLanguages_countable`, és ebből `exists_not_recognizable`: létezik nem felismerhető nyelv; továbbá `no_universal_decider` (diagonalizáció).

**Kriptográfia és adatbiztonság** (`RequestProject/Kriptografia.lean`)
- `pow_mod_prime_of_exp_congr` (kis Fermat-tételre épülő kulcslemma, a `p ∣ m` esetet is kezelve), `rsa_correct` (az RSA helyessége minden üzenetre, nem csak a modulushoz relatív prímekre), `diffie_hellman_correct`, `elgamal_correct`.

**Kalkulus I** (`RequestProject/KalkulusI.lean`)
- `sup_unique`, `tendsto_one_div_atTop`, `frog_series` (a jegyzetbeli „szélesszájú kisbéka” feladat mértani sora), `exists_root_cubic` (Bolzano-tétel), `strictMono_cube`.

**Lineáris algebra I** (`RequestProject/LinearisAlgebraI.lean`)
- `rank_nullity` (dimenziótétel), `det_two_by_two`, `isUnit_iff_det_ne_zero`, `cramer_two` (Cramer-szabály 2×2-re, az egyértelműséggel), `eigen_example`.

A `TANULAS.md` magyar nyelvű áttekintés: melyik fájlban melyik tétel található, mi az egyes bizonyítások „matematikai magja”, és milyen továbbvivő gyakorlatokat érdemes megcsinálni (pl. szimmetrikus differencia automatája, `{wwᴿ}` nem felismerhetősége). A dokumentáció és a kommentek magyarul, a Lean azonosítók angolul készültek, ahogy kérted. Minden változtatás commitolva és feltöltve.