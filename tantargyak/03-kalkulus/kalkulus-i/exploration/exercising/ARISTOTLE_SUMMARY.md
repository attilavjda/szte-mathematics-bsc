# Summary of changes for run f9386a70-a654-4042-b939-c8bc0a4c816b
Elkészült a teljes feladat. Minden munka commitolva és push-olva.

**1. Lean 4 formalizáció — mind a négy feladatsorból, `sorry` nélkül**

A `RequestProject/` könyvtárban:
- `Szakasz1.lean` — 1. feladatsor (halmazok, számhalmazok, felső/alsó határ, egyenlőtlenségek, teljes indukció): 1.3, 1.4, 1.5, 1.6, 1.9, 1.11, 1.12, 1.13, 1.14, 1.15, 1.16, 1.17, 1.19.
- `Szakasz2.lean` — 2. feladatsor (értelmezési tartomány, injektivitás/szürjektivitás, inverz, kompozíció, polinomok): 2.1, 2.2, 2.3, 2.6, 2.7, 2.10, 2.11, 2.15, 2.17, 2.18, 2.19, 2.20.
- `Szakasz3.lean` — 3. feladatsor (határérték, folytonosság): 3.1 (ε–δ és szűrős alakban is), 3.2, 3.3, 3.4, 3.7, 3.8, 3.10, 3.12, 3.13, 3.14(*), 3.15(*), 3.16.
- `Szakasz4.lean` — 4. feladatsor (derivált és alkalmazásai): 4.1, 4.2, 4.3, 4.5, 4.7, 4.8/18, 4.9, 4.10 (L'Hospital), 4.11, 4.13(*).
- `Kategoria.lean` — a gyakorlatok kategóriaelméleti olvasata.

A `lake build` hibátlanul lefut, a fájlokban nincs `sorry`, és a tételek csak a szokásos axiómákra (`propext`, `Classical.choice`, `Quot.sound`) támaszkodnak.

Ebben a menetben fejeztem be a 4. feladatsort, köztük a 4.13(*) csillagos feladatot (középpontosan konvex + folytonos ⟹ konvex), amelyhez a kompaktságot használó segédállítást (`kozeppontos_nonpos_of_endpoints`) is fel kellett építeni: a hibafüggvény *legnagyobb* maximumhelyét toljuk tovább a felezőpont-egyenlőtlenséggel.

Két helyen a feladatkiírást pontosítani kellett (a Lean-dokumentációs sztringben is jelezve): az 1.15 c) felső becslése `n = 1`-re nem igaz (ott egyenlőség áll), ezért `n ≥ 2`-re szól; a 2.15 egyenletének megoldása `x = 2`.

**2–4. Kísérő dokumentum: `kalkulus_kategoriaelmelet.tex` és a lefordított `kalkulus_kategoriaelmelet.pdf` (12 oldal, magyar nyelvű)**

Tartalma:
- **Tematika-megfeleltetés**: táblázat, amely a Neptun-tárgytematika „Tantárgy tartalma” minden pontjához (valós számtest, teljes indukció, nevezetes egyenlőtlenségek, elemi függvények és inverzeik, értelmezési tartomány/értékkészlet, kompozíció, grafikonok és transzformációk, határérték és formális tulajdonságai, elemi határérték-technikák, folytonosság, kompakt intervallum, pontbeli derivált és érintő, deriválási szabályok, láncszabály, logaritmikus/implicit deriválás, monotonitás, lokális szélsőérték, konvexitás, L'Hospital) hozzárendeli a konkrét gyakorlatokat és a konkrét Lean-tételneveket.
- **Kategóriaelméleti összefüggések**: Set/Top/Filter/poset kategóriák és morfizmusaik; a kategória-axiómák mint 2.10–2.18 feladatok; mono = injektív, izo = bijekció; involúció mint izomorfizmus-objektum; a szuprémum univerzális tulajdonsága; Galois-kapcsolatok (egészrész, sSup); a szűrő mint a határérték egységes fogalma; a derivált funktorialitása (láncszabály); monoton függvény mint funktor.
- **Nagy ötletek (Big Ideas)** — 8 pont (teljesség, lokális linearizálás, kompaktság, sűrűség + folytonosság, monoton + korlátos, univerzális tulajdonság stb.).
- **Bizonyítási fogások**: „mozdulat / papíron / Leanben” táblázat, valamint 9 nevesített trükk (meredekség-átírás, legmagasabb fokú taggal osztás, gyöktelenítés, megszüntethető szakadás, illesztés, féloldali meredekségek, logaritmikus deriválás, szélsőérték → egyenlőtlenség, „legnagyobb maximumhely” mozdulat).
- **10 TikZ-ábra**, mind ceruzával lerajzolható: ε–δ doboz, rendőrelv, teleszkopikus becslés téglalapokkal, (1+1/n)^n monoton és korlátos, középpontos konvexitás, Lagrange-középértéktétel, inverz mint tükrözés, nem differenciálható pontok, L'Hospital linearizálás, szűrő-„tölcsér”, továbbá kommutatív diagramok (asszociativitás, mono-kompozíció, adjunkció, láncszabály-négyzet, szűrő-kompozíció).

A projekthez `README.md` is készült a fájlok áttekintésével és a fordítási parancsokkal.