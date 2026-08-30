# Kreditelismerés (validáció) hat tárgyra formális matematikai / Lean 4 hozzájárulások alapján

**Cél.** A következő hat tanegység elismertetése kreditelismerés – ezen belül *validáció* – útján,
nem-formális és informális tanulási eredmények (nyílt forráskódú formalizációs munka, kutatási
együttműködés) alapján:

| # | Tanegység | Jelleg |
|---|-----------|--------|
| 1 | Automaták és formális nyelvek | Számítástudomány Alapjai Tanszék |
| 2 | Logika és informatikai alkalmazásai | Számítástudomány Alapjai Tanszék |
| 3 | A számítástudomány alapjai | Számítástudomány Alapjai Tanszék |
| 4 | Kriptográfia és adatbiztonság | Számítástudomány Alapjai Tanszék |
| 5 | Kalkulus I | matematika BSc kötelező |
| 6 | Lineáris algebra I | matematika BSc kötelező |

Ez a dokumentum három részből áll:

* **A. rész** – mit mond a szabályzat, és pontosan mit kell teljesíteni;
* **B. rész** – hogyan épül fel egy validációs portfólió, és hogyan lesz a bizonyíték „hiteles”;
* **C. rész** – tárgyanként: tanulási eredmény ↔ bizonyíték mátrix, indoklás-sablon, hiányelemzés.

A gépileg ellenőrzött bizonyíték-anyag leltára a [`PORTFOLIO.md`](PORTFOLIO.md) fájlban van.

---

> **Fontos jogi jellegű megjegyzés.** Ez a dokumentum a repóban található
> `kreditatviteli_tajekoztato_hallgatoknak_2026_27_.pdf` szövegének olvasata és gyakorlati
> munkaanyag; **nem hivatalos állásfoglalás és nem jogi tanácsadás**. A csatolt tájékoztató fejlécén
> az *Egészségtudományi és Szociális Képzési Kar* szerepel, viszont maga a tájékoztató kifejezetten
> **az SZTE Tanulmányi és Vizsgaszabályzat 3. számú melléklete alapján** készült, tehát a benne
> idézett elvek egyetemi szintűek. A felsorolt tárgyak azonban **TTIK-s** tanegységek, ezért a
> hatáskörrel rendelkező testület a **TTIK Kreditátviteli Bizottsága**. A tényleges beadás előtt
> mindenképpen ellenőrizni kell a TTIK saját kari kiegészítéseit (elfogadható igazolásfajták,
> kari naptár), és érdemes a Tanulmányi Osztályon rákérdezni.

---

## A. rész — Mit ír elő a szabályzat?

### A.1. A validáció mint jogalap

A tájékoztató **3.8. pontja** a döntő:

> „Kreditelismerés (validáció formájában) kérhető **nem felsőoktatásban megszerzett kompetenciák,
> informális tudás, tanulási eredmények vagy munkatapasztalat** alapján is.”

Ez pontosan a szóban forgó eset: a Mathlib / Lean 4 hozzájárulások, a Kasami–APN formalizáció, az
FBK Trento-val közös temporális logikai és modellellenőrzési munka, a CircomAudit, valamint az
ArkLib / Cedar típusú projektek nem felsőoktatási kurzusteljesítések, hanem informálisan megszerzett,
dokumentálható tanulási eredmények.

Tehát **nem** a „rendes kreditátvitel” (kurzus ↔ kurzus tematikai egyezés) útját kell járni, hanem a
validációét: **kompetencia ↔ tanulási eredmény** megfeleltetést kell igazolni.

### A.2. A 75%-os szabály — a legerősebb érv

**4.1. b) pont:** a Bizottság **nem tagadhatja meg** a kredit elfogadását

> „validáció esetén, ha a megszerzett kompetenciák (illetve az azoknak megfelelő tanulási
> eredmények) aránya legalább ilyen mértékben [ti. 75%-ban] eléri a kiváltandó tantervi egység
> esetén megállapított tanulási eredményeket”.

Ebből a portfólió teljes felépítése következik:

1. **A kiváltandó tanegység tanulási eredményeit kell alapul venni** — nem a saját projektek
   listáját. A hivatalos tantárgyleírás (tantárgyi adatlap / tematika) tanulási eredmény pontjait
   kell kimásolni, és **soronként** kell melléjük bizonyítékot rendelni.
2. **Számszerűsíteni kell a lefedettséget.** Ha a tantárgyleírás pl. 12 tanulási eredményt sorol
   fel, és ezekből 10-hez van bizonyíték, az 83% — ezt ki kell írni a kérelembe, mert így a
   4.1.b) alapján a megtagadás kizárt.
3. **A hiányzó 25%-ot is meg kell nevezni** és pótolni. Az őszinte hiányelemzés (C. rész) nemcsak
   korrekt, hanem meggyőző is: azt mutatja, hogy a kérelmező érti a tantárgy teljes ívét.

### A.3. Amit a Bizottság még mérlegelhet (4.2.)

A 4.2. pont kifejezetten megengedi, hogy a Bizottság a formális tematikai összevetésen túl
mérlegelje az elért tanulási eredmény **körülményeit**:

* **az ismeretek alkalmazásának gyakorlása** („az ismeretek alkalmazásának gyakorlása is az
  ismerethez tartozik”) — egy elfogadott (merge-elt) Mathlib PR pontosan ez: a tudás
  *alkalmazása*, nem pusztán reprodukálása;
* a **gyakorlati és elméleti ismeretek mélysége és aránya**;
* a **ráfordított munkaidő** — ezt érdemes órában is megbecsülni és igazolni (commit-történet,
  PR-ok időbélyegei);
* a **számonkérési rendszer** — itt kifejezetten jó érv, hogy a Lean 4 típusellenőrzője és a
  Mathlib CI-ja **gépi, hibatűrés nélküli számonkérés**, a Mathlib code review pedig
  szakértői (maintaineri) bírálat. Ez szigorúbb ellenőrzés, mint egy írásbeli vizsga.

Ugyanakkor a 4.2. első francia bekezdése az **elévülésről** szól (informatikában gyors);
ez itt nem probléma, mert a hozzájárulások frissek — de a PR-ok dátumát emiatt is fel kell tüntetni.

### A.4. Egy kompetencia — több tárgy (4.4.)

**4.4. pont:**

> „Amennyiben az elismerni kívánt tanulási eredmény (megszerzett kompetencia) ennél szélesebb körű,
> és a tanterv több tárgyának is megfeleltethető, ugyanaz a tanulási eredmény … **több tantárgyra
> vonatkozó párhuzamos kreditelismerés alapja is lehet**.”

Ez kulcsfontosságú: a formalizációs munka átfogó kompetencia, és **ugyanaz a bizonyíték
(pl. a nyelvek/automaták formalizáció) egyszerre szolgálhat az „Automaták és formális nyelvek” és
„A számítástudomány alapjai” tárgyakhoz**. Ezt a pontot érdemes szó szerint idézni a kérelmekben,
mert megelőzi azt az ellenvetést, hogy „ezt már beszámítottuk máshol”.

Ugyanakkor a **4.4. első mondata** szerint az elismert kredit értékét mindig a **kiváltandó**
tantárgy tantervi kreditértéke adja — tehát nem kell „kreditet gyűjteni” a bizonyítékhoz.

### A.5. Formai követelmények

| Szabálypont | Követelmény | Teendő |
|---|---|---|
| Beadási hely | Modulo → Karközi Beadási helyek → **Rendes** kreditátvitel | listás kérelem itt nem alkalmazható (nincs korábbi SZTE-s kurzus) |
| Rendes kérelem | **kérelmenként csak egy tárgyelem** | **hat külön kérelmet** kell beadni |
| 3.1. | csak **még nem teljesített**, **kredittel rendelkező** tanegységre | ellenőrizni a mintatantervben a kreditértéket |
| 3.3. | teljesítést **hiteles igazolással** kell bizonyítani; a 75%-os egyezőség vizsgálatához hitelesített tematika | lásd B.3. — validációnál a „tematika” szerepét a **tanulási eredmény ↔ bizonyíték mátrix** tölti be |
| 3.5. | **korábbi kreditelismerés nem lehet alap** | a hat kérelem egymásra nem hivatkozhat; mindegyik önállóan az eredeti (informális) tanulási eredményre épül |
| 5. | a Bizottság **köteles szakmailag indokolni** a döntést; azonos kérelmet azonosan kell elbírálni | elutasítás esetén az indoklás kikérhető |
| 6. | elutasítás után a kérelem **megismételhető**, ha az indok megszüntethető | ezért érdemes már az első körben mindent csatolni |
| 8. | kreditelismerés esetén a Bizottság **érdemjegyet is ad**; ha a teljesítés nem képezhető le ötfokozatú skálára, azt a Bizottság állapítja meg | validációnál tipikusan ez az eset — érdemes javaslatot tenni és megindokolni |
| 7.2. | a jóváírt kreditek az összes kredithez számítanak, a tantervi követelmények teljesítéséhez hozzájárulnak | (7.1.: az ösztöndíjátlagba nem számítanak bele) |

### A.6. Határidők (2026/2027)

| Időszak | Típus | Kinek |
|---|---|---|
| 2026.08.24 – 2026.09.06. | Kreditátviteli **pótkör** | újonnan felvett / átvett / szak- és tagozatváltó hallgatóknak |
| 2026.11.23 – 2026.12.06. | **Kreditátvitel** | minden hallgatónak, a következő félévre |
| 2027.01.11 – 2027.02.07. | Kreditátviteli **pótkör** | újonnan felvett / átvett / szak- és tagozatváltó hallgatóknak |
| 2027.04.26 – 2027.05.09. | **Kreditátvitel** | minden hallgatónak, a következő félévre |

A kérelem **a következő félévre** vonatkozik, és a döntésnek a kurzusfelvétel kezdete előtt meg kell
születnie. A **4.5. pont** szerint **előzetes kreditátviteli döntés** is kérhető (papíron bármikor
benyújtható); ez itt hasznos lehet: kockázat nélkül kiderül, elfogadja-e a Bizottság az elvet,
mielőtt mind a hat dossziét összeállítanád.

---

## B. rész — A validációs portfólió felépítése

### B.1. Ajánlott szerkezet (kérelmenként)

Minden egyes tárgyhoz egy önálló, tárgyanként ~8–15 oldalas PDF-dosszié, ebben a sorrendben:

1. **Fedlap** – tanegység neve és kódja, kreditérték, a kérelem jogalapja (TVSZ 3. sz. melléklet
   3.8. pont – validáció), a kérelmező adatai.
2. **Vezetői összefoglaló (1 oldal)** – mi a megszerzett kompetencia, hol szerezted, mivel
   igazolod, és mennyi a lefedettség százalékban.
3. **Tanulási eredmény ↔ bizonyíték mátrix** – a tantárgyleírás *minden* tanulási eredménye egy
   sor; oszlopok: (a) tanulási eredmény szó szerint, (b) a bizonyíték megnevezése,
   (c) permalink / azonosító, (d) rövid szakmai magyarázat, (e) lefedve: igen / részben / nem.
4. **Összesítés**: „N/M tanulási eredmény teljesen lefedve = X% ≥ 75%”.
5. **Bizonyítéktár** – PR-listák, commit-hashek, CI-log kivonatok, forráskód-részletek.
6. **Külső igazolások** – maintaineri / témavezetői / FBK-s támogató levelek.
7. **Hiányelemzés és pótlás** – mi nincs lefedve, és azt hogyan pótoltad.
8. **Érdemjegy-javaslat** és annak indoklása (8. pont).

### B.2. Miért „nyílt forráskód” = hiteles bizonyíték?

Érdemes a kérelemben külön alfejezetben elmagyarázni a Bizottságnak (amely nem feltétlenül ismeri a
formalizációs kultúrát), hogy a bizonyíték miért **ellenőrizhető és hamisíthatatlan**:

* **Gépi ellenőrzés.** Egy Lean 4 tétel akkor és csak akkor „kész”, ha a Lean magja (kernel)
  elfogadja. Nincs részpontszám, nincs jóindulatú javítás. A `#print axioms` paranccsal
  ellenőrizhető, hogy a bizonyítás nem támaszkodik-e nem szokványos feltevésre; a jelen
  portfólióban minden tétel csak a `propext`, `Classical.choice`, `Quot.sound` standard
  axiómákra épül, és **egyetlen `sorry` sincs benne**.
* **Szakértői bírálat.** A Mathlib-be csak maintaineri review után kerül be kód; ez név szerint
  azonosítható szakemberek szakmai értékelése.
* **Nyilvános, időbélyegzett, megváltoztathatatlan nyom.** A GitHub PR-permalink, a commit-hash
  és a CI-futás naplója utólag nem módosítható.
* **Reprodukálhatóság.** A bizottság bármely tagja `lake build`-del ellenőrizheti az egész
  portfóliót; a repó tartalmazza a pontos toolchain- és Mathlib-verziót.

### B.3. Hogyan lesz a bizonyíték formálisan is „hiteles igazolás” (3.3.)?

A 3.3. pont hiteles igazolást vár. Validációnál nincs leckekönyv, ezért:

* **Támogató levél a projektfelelőstől / témavezetőtől.** Az FBK Trento-s együttműködésről a
  fogadó kutatótól aláírt (lehetőleg intézményi fejléces) levél, amely megnevezi az elvégzett
  munkát, az időtartamot és a becsült munkaterhelést. Ez a legerősebb dokumentum.
* **Maintaineri visszaigazolás.** Ha egy Mathlib-maintainer hajlandó rövid e-mailben megerősíteni
  a merge-elt PR-okat, azt is csatold (a PR-oldalak kinyomtatva/PDF-be mentve önmagukban is
  bizonyítékok).
* **Saját, aláírt nyilatkozat** a portfólió tartalmáról és arról, hogy a felsorolt munka a sajátod
  (társszerzős munkánál a saját közreműködés arányának pontos megjelölésével).
* **SZTE-s oktatói ellenjegyzés.** A 3.3. szerint hitelesnek az számít, amit a Tanulmányi Osztály
  vagy **az oktató** aláírásával és pecséttel ellátnak. Ezért gyakorlati javaslat: **a
  tárgyfelelős oktatót előzetesen keresd meg**, mutasd meg neki a dossziét, és kérd, hogy a
  tanulási eredmény ↔ bizonyíték mátrixot ellenjegyezze. Egy tanszéki pecséttel ellátott
  szakmai megerősítés a Bizottság dolgát is megkönnyíti.
* **Repó-pillanatkép.** A teljes portfólió-repó archív ZIP-je + a `git log` kivonata, hogy a
  dosszié önmagában is ellenőrizhető legyen internet nélkül.

### B.4. Munkaterhelés-becslés (4.2. — „ráfordított munkaidő”)

Készíts táblázatot: projekt / feladat, időszak, becsült órák, forrás (commit-történet).
Vesd össze a tanegység kreditértékével: 1 kredit ≈ 30 munkaóra. Egy 5 kredites tárgynál tehát a
kb. 150 órányi igazolt munka önmagában is erős érv a 4.2. alapján.

### B.5. Gyakori ellenvetések és a rájuk adott válasz

| Ellenvetés | Válasz |
|---|---|
| „Ez nem tantervi teljesítés.” | A 3.8. pont kifejezetten megengedi a nem felsőoktatásban szerzett tudás validációját. |
| „Nincs rá tematika, nem mérhető a 75%.” | A 4.1.b) validáció esetén nem tematikai, hanem **tanulási eredmény** szerinti egyezést ír elő; a mátrix pontosan ezt méri. |
| „Ugyanazt a munkát több tárgyra is beadja.” | A 4.4. utolsó mondata ezt kifejezetten megengedi. |
| „A gyakorlati számolási készség nem igazolt.” | Lásd a C. rész hiányelemzéseit: erre külön, kifejezetten *számolós* bizonyítékot kell gyártani (kidolgozott feladatsorok, gépileg ellenőrzött numerikus példák), vagy elfogadni a részleges elismerést. |
| „A tudás elévült.” | A 4.2. szerint az elévülési idő nem lehet öt évnél kevesebb; a hozzájárulások ennél frissebbek — dátumokkal igazolva. |

---

## C. rész — Tárgyanként: mit kell lefedni és mivel

> A táblázatok „tanulási eredmény” oszlopa a tananyagok (Ésik-jegyzet, logika-jegyzet,
> kalkulus-gyakorlófüzet stb.) alapján felállított **munkaverzió**. A végleges kérelembe a
> **hivatalos tantárgyi adatlap** szó szerinti tanulási eredményeit kell átemelni — ezt kérd el a
> tanszéktől vagy nézd meg a mintatantervben, mert a 4.1.b) számítás alapja ez.
>
> A „bizonyíték” oszlop deklarációnevei a jelen repó gépileg ellenőrzött portfóliójára utalnak
> (részletes leltár: [`PORTFOLIO.md`](PORTFOLIO.md)).

### C.1. Automaták és formális nyelvek

| Tanulási eredmény | Bizonyíték | Lefedve |
|---|---|---|
| Determinisztikus véges automata, felismert nyelv fogalma | `prodDFA`, `complDFA`, `unionDFA`, `parityDFA` konstrukciók és helyességi tételeik | igen |
| Zártsági tulajdonságok (metszet, unió, komplementer) | `accepts_prodDFA`, `accepts_unionDFA`, `accepts_complDFA` | igen |
| Zártság szimmetrikus differenciára, **konkatenációra** és **Kleene-iterációra** | `isRegular_symmDiff`, **`isRegular_mul`**, **`isRegular_kstar`** (utóbbi kettő a Mathlibből hiányzó állítás, saját bizonyítás) | igen |
| Myhill–Nerode-tétel | `myhill_nerode` (Mathlib-alak), és annak *alkalmazása* a nem-regularitási bizonyításokban | igen |
| Pumpáló lemma / nem reguláris nyelvek | `anbn_not_recognizable`, `wwR_not_regular`, `squares_not_regular` | igen |
| Reguláris kifejezések, Kleene tétele | a Kleene-műveletekre való zártság megvan (`isRegular_mul`, `isRegular_kstar`), a regex ↔ automata ekvivalencia nem | részben |
| Nemdeterminisztikus automaták, determinizálás | Mathlib `NFA`/`DFA` API ismerete; saját tétel nincs | részben |
| Környezetfüggetlen nyelvek, veremautomaták | *nincs lefedve* | nem |

**Hiányelemzés / pótlási terv.** (i) Kleene tétele (reguláris kifejezés ↔ automata ekvivalencia)
a Mathlibben nincs meg — ez egyszerre a legnagyobb hiány és a legjobb upstream hozzájárulási cél
(a hozzá szükséges zártsági tételek — konkatenáció, iteráció — viszont már megvannak).
(ii) A determinizálás (részhalmaz-konstrukció) helyességének formalizálása.
(iii) A környezetfüggetlen rész (CYK, pumpáló lemma CF nyelvekre) külön munka.
Ha ez a három megvan, a lefedettség lényegében 100%.

### C.2. Logika és informatikai alkalmazásai

| Tanulási eredmény | Bizonyíték | Lefedve |
|---|---|---|
| Ítéletlogika szintaxisa és szemantikája | `PFormula`, `eval`, `Entails` | igen |
| Normálformák, DNF/KNF | `litFor`, `conjOf`, `disjOf`, `eval_conjOf`, `eval_disjOf` | igen |
| Funkcionális teljesség, összekötő-rendszerek | `functionally_complete`, és a negatív irány: `not_functionally_complete_iff_neg` | igen |
| Rezolúció és helyessége | `resolution_sound` | igen |
| Hilbert-kalkulus, dedukciós tétel | `Hilbert`, `Hilbert.deduction`, `Hilbert.weaken` | igen |
| Helyességi és **teljességi tétel** | `Hilbert.soundness`, **`Hilbert.completeness`** (Kalmár-féle bizonyítás) | igen |
| Ellentmondás-mentesség | `Hilbert.consistent` | igen |
| Elsőrendű logika, rezolúció elsőrendben, unifikáció | *nincs lefedve* | nem |
| Temporális logika, modellellenőrzés (alkalmazások) | FBK Trento együttműködés: folytonos idejű temporális logika, induktív invariánsok tanúsítványainak ellenőrzése | igen (külső bizonyíték) |

**Hiányelemzés.** Az elsőrendű rész (Herbrand-tétel, unifikáció, elsőrendű rezolúció) hiányzik.
Pótlás: a Mathlib `FirstOrder.Language` API-ra épülő saját formalizáció, vagy kidolgozott
feladatsor a `loginfalk-peldatarnlzv4.pdf` elsőrendű fejezeteiből.
**Megjegyzés:** az FBK-s munka önmagában erős érv a „logika informatikai alkalmazásai” félhez —
pontosan az a tárgy címe. Erre kérj külön támogató levelet.

### C.3. A számítástudomány alapjai

| Tanulási eredmény | Bizonyíték | Lefedve |
|---|---|---|
| Megszámlálhatóság, átlós módszer | `words_countable`, `languages_not_countable`, `exists_not_recognizable` | igen |
| Kiszámíthatóság, Turing-gép / parciálisan rekurzív függvények | Mathlib `Nat.Partrec.Code` alapú tételek | igen |
| **Megállási probléma** | `halting_problem`, `no_universal_decider` | igen |
| s-m-n tétel | `smn_theorem` | igen |
| **Rice tétele** | `rice_theorem_undefined` | igen |
| Post tétele (R = RE ∩ co-RE) | `post_theorem` | igen |
| Nem kiszámítható függvény létezése | `exists_not_computable` | igen |
| Bonyolultságelmélet (P, NP, NP-teljesség, Cook–Levin) | *nincs lefedve* | nem |

**Hiányelemzés.** A bonyolultságelméleti blokk (P vs NP, redukciók, NP-teljesség, Cook–Levin) nincs
lefedve, és a Mathlibben sincs meg — ez nagy, de nagyon értékes upstream cél. Rövid távú pótlás:
konkrét redukciók (SAT → 3SAT, 3SAT → CLIQUE) formalizálása vagy legalább részletes kidolgozása.

### C.4. Kriptográfia és adatbiztonság

| Tanulási eredmény | Bizonyíték | Lefedve |
|---|---|---|
| Tökéletes titkosság, Vernam-rejtjel | `otp_perfect_secrecy` (valószínűségi, `PMF`-alapú megfogalmazás) | igen |
| Számelméleti alapok: Euler–Fermat | `euler_theorem`, `pow_mod_prime_of_exp_congr` | igen |
| **RSA** helyessége | `rsa_correct` | igen |
| Diffie–Hellman, ElGamal | `diffie_hellman_correct`, `elgamal_correct` | igen |
| Titokmegosztás (Shamir) | `shamir_two_shares`, `shamir_one_share_no_info` | igen |
| Blokkrejtjelek, S-dobozok, differenciális kriptoanalízis | **`cube_is_apn`**, `cube_apn_ncard` + a Kasami/APN formalizációs projekt | igen |
| Protokoll- és implementációs biztonság, auditálás | CircomAudit (ZK-áramkörök auditálása); ArkLib | igen (külső bizonyíték) |
| Hash-függvények, digitális aláírás, PKI | *nincs lefedve* | nem |

**Hiányelemzés.** Hiányzik a hash-függvények (ütközésállóság, Merkle–Damgård), a digitális aláírás
és a PKI/protokoll-blokk. Pótlás: a Merkle-fa helyességének formalizálása (ez az ArkLib/CircomAudit
vonalhoz természetesen illeszkedik), illetve az aláírási sémák helyességi tételei.

### C.5. Kalkulus I

| Tanulási eredmény | Bizonyíték | Lefedve |
|---|---|---|
| Valós számok, teljességi axióma, szuprémum | `sup_unique` | igen |
| Irracionalitás, egyenlőtlenségek, háromszög-egyenlőtlenség | `ex_1_9`, `ex_1_11`, `ex_1_13` + **merge-elt Mathlib PR-ok** | igen |
| Teljes indukció, összegzések | `ex_1_14a/b/c`, `ex_1_15a/b/c/d`, `bernoulli_two_le` | igen |
| Függvények, injektivitás, kompozíció, polinomok | `ex_2_11`, `ex_2_18`, `ex_2_19` | igen |
| Sorozatok, határértékek, sorok | `tendsto_one_div_atTop`, `frog_series`, `ex_3_16c` | igen |
| Folytonosság, Bolzano-tétel, egyenletes folytonosság | `exists_root_cubic`, `ex_3_14`, `ex_3_15`, `strictMono_cube` | igen |
| Differenciálhatóság, szélsőérték, L'Hospital | `ex_4_8_18`, `ex_4_10e` | igen |
| Konvexitás | **`ex_4_13`** (középponti konvexitás + folytonosság ⇒ konvexitás) | igen |
| Rutin-számítási készség (határérték-, derivált-, függvényvizsgálat-feladatok) | részben | részben |
| Riemann-integrál | *nincs lefedve* | nem |

**Hiányelemzés.** Két valódi hiány van. (i) A **számolási rutin** (a vizsga „gyakorlati” része:
függvényvizsgálat, konkrét határértékek, deriválás) — ezt a formalizáció nem igazolja jól, mert a
Lean-bizonyítás más készség. Pótlás: a `kalkulus_gyakorlo.pdf` feladatainak kidolgozott, sajátkezű
megoldásait csatolni, illetve a formalizált tételekhez konkrét numerikus példákat (`#eval`,
`norm_num`, `decide`) mellékelni. (ii) A **Riemann-integrál** teljesen hiányzik — érdemes hozzá
legalább néhány tételt (integrálhatóság, Newton–Leibniz alkalmazása) formalizálni.
**Ha e két hiányt nem pótolod, ez a tárgy a legkockázatosabb a hatból** — az „ismeretek
alkalmazásának gyakorlása” (4.2.) itt a Bizottság szemében a számolást is jelenti.

### C.6. Lineáris algebra I

| Tanulási eredmény | Bizonyíték | Lefedve |
|---|---|---|
| Mátrixműveletek, determináns és tulajdonságai | `det_mul_eq`, `det_transpose_eq`, `det_three_sarrus`, `det_example` | igen |
| Lineáris egyenletrendszerek, Cramer-szabály | `cramer_two`, `exists_unique_solution`, `exists_nontrivial_kernel` | igen |
| Vektorterek, bázis, dimenzió, rang | `rank_nullity`, `rank_transpose_eq`, `finrank_submodule_le` | igen |
| Lineáris függetlenség | `linearIndependent_of_orthogonal`, `linearIndependent_pair_of_eigen` | igen |
| Skaláris szorzat, Cauchy–Schwarz | `cauchy_schwarz` | igen |
| Sajátérték, sajátvektor, karakterisztikus polinom | `eigen_example`, `eigenvalues_example`, `linearIndependent_pair_of_eigen` | igen |
| Invertálhatóság | `isUnit_iff_det_ne_zero`, `det_two_by_two` | igen |
| Alkalmazások (véges test feletti lineáris algebra, kódolás, ZK) | ArkLib, Cedar, CircomAudit közreműködés | igen (külső bizonyíték) |
| Gauss-elimináció mint **algoritmus**, konkrét számolás | részben | részben |
| Bilineáris formák, ortogonalizáció (Gram–Schmidt), diagonalizálhatóság | *nincs lefedve* | nem |

**Hiányelemzés.** Pótlásként: a Gram–Schmidt eljárás és a spektráltétel (szimmetrikus mátrixokra)
formalizálása vagy kidolgozása, illetve a Gauss-elimináció konkrét, végigszámolt példái.

---

## D. Indoklás-sablon (Modulo „Indoklás” mező)

> **Tárgy:** *[tanegység neve, kódja, kreditértéke]*
> **A kérelem jogalapja:** SZTE TVSZ 3. sz. melléklet **3.8. pont** (kreditelismerés validáció
> formájában, nem felsőoktatásban megszerzett kompetenciák, informális tudás és tanulási eredmények
> alapján), valamint **4.1. b) pont** (a kredit elfogadása nem tagadható meg, ha a megszerzett
> kompetenciák aránya eléri a kiváltandó tantervi egység tanulási eredményeinek 75%-át).
>
> Kérem a *[tanegység]* tanegység kreditjének elismerését az alábbi, nem felsőoktatási keretek
> között megszerzett és dokumentálható tanulási eredmények alapján.
>
> **1. A megszerzett kompetencia.** *[1–2 bekezdés: mit tudsz, mit csináltál, milyen projektben.]*
>
> **2. A tanulási eredmények megfeleltetése.** A csatolt mellékletben tanulási eredményenként
> megadtam a bizonyítékot. A tantárgyleírásban szereplő *M* tanulási eredményből *N* teljesen
> lefedett, ami **X%**, tehát a 4.1. b) pont szerinti 75%-os küszöböt meghaladja.
>
> **3. A bizonyíték hitelessége és ellenőrizhetősége.** A hivatkozott állítások a Lean 4
> tételbizonyító rendszerben, a Mathlib könyvtárra épülve, **gépileg ellenőrzött** bizonyítással
> szerepelnek; a hivatkozott repó `lake build` paranccsal bárki által újraellenőrizhető, a
> bizonyítások egyetlen `sorry`-t sem tartalmaznak, és csak a rendszer standard axiómáira épülnek.
> A Mathlibbe merge-elt hozzájárulásokat nyilvános, időbélyegzett pull requestek és maintaineri
> code review igazolják *[permalinkek]*. Csatolom továbbá *[támogató levél / oktatói ellenjegyzés]*.
>
> **4. A tanulási eredmény minősége (4.2. pont).** A munka becsült ráfordítása *[óra]*, ami a
> tanegység *[k]* kreditjének megfelelő *[30·k]* órás terhelést eléri/meghaladja. Az ismeretek
> alkalmazásának gyakorlása a formalizációs munkában folyamatos volt; a számonkérés gépi
> (típusellenőrzés, folyamatos integráció) és szakértői (maintaineri bírálat).
>
> **5. Kérem továbbá**, hogy a Bizottság a 8. pont szerint az érdemjegyet *[javaslat]* értékben
> állapítsa meg, tekintettel arra, hogy a teljesítés nem képezhető le közvetlenül ötfokozatú skálára.
>
> **Mellékletek:** 1) tanulási eredmény ↔ bizonyíték mátrix; 2) hozzájárulások jegyzéke
> (permalinkekkel és commit-hashekkel); 3) a portfólió-repó pillanatképe és build-naplója;
> 4) támogató levél/levelek; 5) munkaterhelés-becslés.

---

## E. Ellenőrzőlista a beadás előtt

- [ ] A hat tanegység **hivatalos tantárgyi adatlapját** beszereztem (tanulási eredmények, kreditérték).
- [ ] Ellenőriztem, hogy egyik tanegység sincs még teljesítve, és mindegyik kredites (3.1.).
- [ ] Tárgyanként külön **rendes** kérelmet készítettem (kérelmenként egy tárgyelem).
- [ ] Minden dossziéban kiszámoltam és kiírtam a **lefedettségi százalékot** (≥75%).
- [ ] Minden bizonyítékhoz **permalink + commit-hash + dátum** tartozik.
- [ ] A repó `lake build`-del tisztán fordul, `sorry` nincs benne, és ezt a build-naplóval igazoltam.
- [ ] Beszereztem a **támogató leveleket** (FBK, maintainer, tárgyfelelős oktató ellenjegyzése).
- [ ] Elkészült a **munkaterhelés-becslés** órában, kreditre vetítve.
- [ ] A hiányzó tanulási eredményekre **pótlási tervet** írtam (vagy már pótoltam).
- [ ] Egyeztettem a **TTIK** Tanulmányi Osztályával a kari sajátosságokról.
- [ ] Megfontoltam **előzetes kreditátviteli döntés** kérését (4.5.).
- [ ] Betartom a **határidőt** (lásd A.6.).
- [ ] Tudom, hogy elutasítás esetén a kérelem **megismételhető** (6.), ha az indok megszüntethető.

---

## F. Reális várakozás

A hat tárgy közül a **Logika**, **A számítástudomány alapjai**, az **Automaták és formális nyelvek**
és a **Kriptográfia** esetében a portfólió már most is nagyon erős: a tantárgyak gerincét adó
tételek gépileg ellenőrzött bizonyítással megvannak, több esetben olyan is, ami a Mathlibből
hiányzik. A **Lineáris algebra I** szintén jól lefedett. A **Kalkulus I** a legkockázatosabb, mert
ott a tantárgy jelentős része *számolási rutin*, amit a formalizáció közvetve igazol —
itt érdemes a legtöbb pótlólagos bizonyítékot előállítani, vagy elfogadni, hogy ez a tárgy marad
vizsgás.

A dokumentum nem garantál elfogadást: a 4.1.b) csak akkor köti a Bizottságot, ha a **75%-os
lefedettséget a Bizottság is megállapítja** — a mátrix meggyőző, tételes kidolgozása ezért a
legfontosabb munka.
