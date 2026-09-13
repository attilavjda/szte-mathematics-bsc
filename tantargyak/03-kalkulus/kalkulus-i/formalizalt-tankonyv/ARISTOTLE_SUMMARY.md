# Summary of changes for run b9ab9503-4f11-4a4e-9dd2-085ca806af73
A repó mostantól **két, egymástól teljesen független, külön-külön fordítható Lean 4 + Mathlib projektet** tartalmaz, és bennük kizárólag a tankönyvek formalizációja szerepel.

**1. `Analizis/` — Leindler László: *Analízis* (Polygon, 2001)**
* Saját `lakefile.toml`, `lean-toolchain`, `lake-manifest.json`, `.gitignore`, gyökérmodul: `Analizis/Analizis.lean` (egyetlen `import Analizis` sorral az egész anyag elérhető).
* Tartalom: `Analizis/Analizis/Ch03…Ch08e` (a jegyzet 3–8. fejezete a függvénydiszkusszió végéig) és `Analizis/Analizis/Tematika/KalkulusI*.lean` (Kalkulus I. előadás tematikája) — 32 modul, kb. 10 500 sor, 600-nál több tétel/lemma.
* Fordítás: `cd Analizis && lake exe cache get && lake build` — ellenőrizve, **hibamentesen lefut (8059 job)**.

**2. `LinearisAlgebra/` — Szabó László: *Bevezetés a lineáris algebrába* (2006)**
* Saját `lakefile.toml`, `lean-toolchain`, `lake-manifest.json`, `.gitignore`, gyökérmodul: `LinearisAlgebra/LinearisAlgebra.lean`.
* Tartalom: `LinearisAlgebra/LinearisAlgebra/Ch01…Ch18`, a kidolgozott példamodulok (`Peldak`, `Peldak2_Kidolgozott`) és `…/Tematika/LinearisAlgebraI*.lean` — 29 modul, kb. 8 900 sor, 500-nál több tétel/lemma.
* Fordítás: `cd LinearisAlgebra && lake exe cache get && lake build` — ellenőrizve, **hibamentesen lefut (8056 job)**.

**További változások**
* A modulnevek átnevezve a két új projekt névterére (`Analizis.*`, illetve `LinearisAlgebra.*`); a két projekt között nincs kereszthivatkozás, így valóban külön-külön fordíthatók.
* A nem formalizációs kiegészítők (a korábbi futtatható demó program, a `#eval`-os bemutató modul, az axiómaellenőrző modul, a közös gyökérmodul és a CI-beállítás) eltávolítva — a projektekben csak a formalizált tananyag maradt.
* Mindkét projekt kapott **saját, magyar nyelvű `README.md`-t**: a projekt leírása, fordítási/futtatási útmutató, terjedelmi adatok, a formalizálás alapelvei, a modulok fejezetenkénti táblázata és a hozzá tartozó tantárgyi tematika pontjainak megfeleltetése.
* A tankönyv-PDF-ek a repó gyökerében maradtak.
* A forrásban továbbra sincs `sorry`, `axiom` vagy `@[implemented_by]` (a „sorry-mentes” szó csak dokumentációs szövegben fordul elő).

Minden változtatás commitolva és felpusholva. Megjegyzés: a tulajdonságtáblázat bejegyzéseiben szereplő fájlútvonalak a korábbi, egyesített elrendezésre utalnak; a hivatkozott tételek és definíciók változatlanul, ugyanazzal a névvel érhetők el az új `Analizis/Analizis/…`, illetve `LinearisAlgebra/LinearisAlgebra/…` fájlokban.

# Summary of changes for run 05b15457-600b-45c9-9319-af227fa2fbbc
A repó mostantól egyetlen, egységes, fordítható és **futtatható** Lean 4 + Mathlib könyvtár. Amit ebben a menetben elvégeztem:

**1. Futtathatóság.** Új `demo` végrehajtható cél készült (`Demo.lean` + `lakefile.toml` `[[lean_exe]]` bejegyzés): a `lake exe demo` parancs elindít egy programot, amely a formalizált, kiszámítható definíciókat (a jegyzet rekurzív `det'` determinánsa, mátrixszorzás, inverz, Cramer-szabállyal megoldott egyenletrendszer, binomiális együtthatók) konkrét adatokon meghívja és kiírja az eredményeket. A program lefordul és lefut (kimenetét ellenőriztem).

**2. Új matematikai tartalom (két új modul, `sorry` nélkül).**
* `RequestProject/Leindler/Ch08e_FuggvenyDiszkusszio.lean` — a jegyzet **8.8. függvénydiszkussziós sémája végigvezetve** az `f(x) = x³ − 3x` függvényen, végig a könyv saját tételeire (8.1.2., 8.4.1., 8.5.1., 8.6.1., 8.7.2.) hivatkozva: folytonosság, értékkészlet (az egész ℝ), zérushelyek (`0`, `±√3`), páratlanság, monotonitási intervallumok, szigorú helyi maximum `f(−1) = 2` és minimum `f(1) = −2`, konkáv/konvex szakaszok, inflexiós pont `0`-ban, valamint a `±∞`-beli viselkedés.
* `RequestProject/LinearisAlgebra/Peldak2_Kidolgozott.lean` — kidolgozott gyakorlófeladatok konkrét ℚ feletti mátrixokon: szabályos egyenletrendszer egyértelmű megoldása a **Cramer-szabállyal**, `3×3`-as mátrix inverze a 4.1. Definíció értelmében, valamint a `!![2,1;1,2]` mátrix karakterisztikus gyökei (`1` és `3`) és a hozzájuk tartozó sajátvektorok.

**3. Egységesség és önellenőrzés.** Mindkét új modul be van kötve a `RequestProject.lean` gyökérmodulba (65 almodul, egyetlen `import RequestProject`). Az `Ellenorzes.lean` axiómaellenőrző modult kibővítettem a tematika-modulok és az új példamodulok főtételeivel: minden felsorolt tétel csak a `propext`, `Classical.choice`, `Quot.sound` standard axiómáktól függ. A CI-folyamat (`.github/workflows/build.yml`) most `lake build`-et, `lake exe demo`-t és `sorry`-ellenőrzést is futtat (a szűrőt javítottam, hogy a dokumentációs előfordulásokra ne bukjon el).

**4. Dokumentáció.** A `README.md` és a `ROADMAP.md` frissült: az új modulok, a `demo` cél, a fordítási/futtatási útmutató és az aktuális terjedelmi adatok (Leindler 30 modul / 544 tétel, lineáris algebra 27 modul / 460 tétel, tematikák 4 modul / 115 tétel, kb. 19 800 sor).

**Állapot:** a teljes `lake build` (8091 job) és a `lake build demo` (16072 job) **hibamentesen és figyelmeztetés nélkül** lefut; a forrásban nincs `sorry`, `axiom` vagy `@[implemented_by]` (csak dokumentációs szövegben szerepel a „sorry-mentes” szó). Minden változtatás commitolva és felpusholva.