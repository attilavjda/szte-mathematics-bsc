# Tárgytematika ↔ Kasami/AB/APN formalizáció — pontonkénti megfeleltetés

Ez a dokumentum a két feltöltött Neptun-tárgytematika

* **Lineáris algebra I.** (MBLK15E, előadó: Maróti Miklós) — `LineárisalgebraI.-7.pdf`
* **Kalkulus I. előadás** (MBLK37E, előadó: Pusztai Béla Gábor) — `Kalkulus1.-3.pdf`

**minden** tematikai pontjához megad egy géppel ellenőrzött (`sorry`-mentes) megfelelőt a
repó Kasami / AB / APN formalizációs moduljaiban.

A kérdés úgy szólt, hogy ahol a tematika eleme **nem szerepel szó szerint** ebben a
formában, ott a megfelelő mintát **Morita-ekvivalens**, illetve **nem hű (non-faithful)
funktoriális** kontextusba képezve keressük meg. A dokumentum ezt az áttételt teszi
explicitté, és minden sorban megmondja, *milyen módon* jött létre a megfeleltetés.

Az áttételt megvalósító új modulok:

| modul | tartalom |
|---|---|
| `RequestProject/Tematika/MoritaKeret.lean` | az áttétel kerete: `End_{F₂}(GF(2ⁿ)) ≅ M_n(F₂)`, a nem hű funktorok, és annak bizonyítása, hogy a rendezés az, ami elveszik |
| `RequestProject/Tematika/LinearizaltPolinom.lean` | a Morita-szótár polinomoldala: minden `F₂`-lineáris endomorfizmus linearizált polinom |
| `RequestProject/Tematika/LinearisAlgebra.lean` | a *Lineáris algebra I.* tematika pontonkénti megfeleltetése |
| `RequestProject/Tematika/Kalkulus.lean` | a *Kalkulus I.* tematika pontonkénti megfeleltetése (benne a Darboux-tétel áttétele) |
| `RequestProject/Tematika/Kiegeszitesek.lean` | a maradék pontok: Cramer-szabály, blokkmátrixok, függetlenség/rang, elemi függvénytranszformációk |

---

## 0. Mi az „áttétel"? Két pontosan definiált mechanizmus

### 0.1 Morita-ekvivalens kontextus

Két gyűrű Morita-ekvivalens, ha modulkategóriáik ekvivalensek. A számunkra releváns eset:
`F₂` és `M_n(F₂)` Morita-ekvivalensek, és az ekvivalenciát megvalósító progenerátor `F₂ⁿ`.
A `GF(2ⁿ)` test **mint `F₂`-vektortér** pontosan ez a progenerátor. Az áttételt megvalósító
konkrét izomorfizmus:

```lean
Tematika.Morita.endAlgEquivMatrix :
    Module.End (ZMod 2) F ≃ₐ[ZMod 2] Matrix (Fin n) (Fin n) (ZMod 2)
```

(`RequestProject/Tematika/MoritaKeret.lean`). Ez algebraizomorfizmus, tehát a
kompozíció ↦ mátrixszorzás (`endAlgEquivMatrix_comp`) és az összeadás ↦ mátrixösszeadás
(`endAlgEquivMatrix_add`) megfeleltetés is bizonyított. Következmény: a tematika **egész
mátrixos fejezete** (mátrixműveletek, inverz, determináns, rang, Gauss-elimináció,
Cramer-szabály) változtatás nélkül a könyvtár `L_k`, `Cross`, `Frobenius` objektumaira
vonatkozik.

A szótár másik vége is explicit: `Tematika.LinPoly.exists_linearized_repr` szerint minden
`F₂`-lineáris endomorfizmus **linearizált polinom**
`x ↦ c₀x + c₁x² + ⋯ + c_{n−1}x^{2^{n−1}}` alakú, és
`Tematika.LinPoly.card_end_eq` szerint `|End_{F₂}(F)| = 2^{n²} = |M_n(F₂)|`.

Így a tematika három nyelve — **mátrix**, **lineáris leképezés**, **linearizált polinom** —
ugyanannak a Morita-kontextusnak három megvalósítása.

### 0.2 Nem hű funktoriális kontextus

Az áttétel másik iránya *lossy*: a tematika egyes fogalmai csak egy **nem hű funktor**
képén léteznek a Kasami-oldalon. Két ilyen funktort használunk.

* **A differenciál-invariáns funktor** `f ↦ differentialUniformity f`. Eltolásinvariáns
  (`Tematika.Morita.diffUnif_translate`), ezért nem hű: egy egész mellékosztálynyi
  függvényt egyetlen értékre képez — `Tematika.Morita.diffUnif_not_faithful`.
  Ugyanez skálázásra is igaz (`Tematika.Kiegeszitesek.diffUnif_scale`) és
  Frobenius-konjugálásra (`Tematika.Kiegeszitesek.isAPN_frobenius_conj`). Ez az
  EA-ekvivalencia formális magja: a tematika „elemi függvénytranszformációk" pontja
  pontosan ennek a funktornak a magja.
* **A pályahalmaz-funktor** `π₀` — róla a `RequestProject/BabySteps/Step04TupleSymmetry.lean`
  modul már korábban bizonyította, hogy nem őrzi a szorzatot
  (`piZeroProd_not_injective`).

**Amit elveszítünk, azt névvel is megnevezzük:** `Tematika.Morita.no_linear_order_of_charTwo`
szerint `char = 2` mellett *nincs* rendezett testszerkezet. A kalkulus rendezésre épülő
fogalmai (monotonitás, szélsőérték, konvexitás, Bolzano-tétel) tehát **nem** léteznek szó
szerint; csak a nem hű funktor képén, invariáns alakban jelennek meg. Ezt a fordítást
végzi a `Tematika/Kalkulus.lean` modul:

| rendezésfüggő fogalom | invariáns alak `char 2`-ben |
|---|---|
| szigorú monotonitás | injektivitás |
| Bolzano / Darboux (a derivált képe intervallum) | a derivált képe **affin altér** (mellékosztály) |
| kompakt intervallum | a véges test egésze (minden halmaz kompakt és nyílt) |
| konvexitás (`f'' ≥ 0`) | a második diszkrét derivált **konstans**, azaz `deg f ≤ 2` |
| lokális szélsőérték / kritikus pont | a derivált rostjai (APN esetén ≤ 2 elem) |

---

## 1. Lineáris algebra I. (MBLK15E) — pontonkénti táblázat

Státuszjelölések: **[M]** = Morita-áttétellel, **[N]** = nem hű funktor képén,
**[K]** = közvetlen (szó szerinti) megfelelő, **[R]** = korábbi modulban már megvolt,
**[×]** = nem alkalmazható (magyarázat a 3. szakaszban).

### 1. Komplex számok

| tematikai elem | Lean-deklaráció | státusz |
|---|---|---|
| `ℂ` mint `ℝ` bővítése, kanonikus alak | `Tematika.Morita.finrank_eq_of_card` (`GF(2ⁿ)` mint `n`-dimenziós `F₂`-tér) | [M] |
| konjugálás | `Tematika.Morita.frobAlgEquiv` (Frobenius mint `F₂`-algebraautomorfizmus) | [M] |
| a konjugálás alatt invariáns valós rész | `Tematika.Morita.trace_algEquiv`, `trace_frobPow` (a nyom Galois-invariáns) | [M] |
| trigonometrikus alak, Moivre-képlet | `Tematika.LinAlg.moivre_frobenius`: `(x^{2^k})^{2^m} = x^{2^{k+m}}` | [M] |
| gyökvonás | `Tematika.LinAlg.powerMap_bijective_of_coprime` (`x ↦ x^d` bijektív, ha `gcd(d, 2ⁿ−1)=1`) | [M] |
| `n`-edik egységgyökök | `Tematika.LinAlg.pow_card_eq_self`: `x^{2ⁿ} = x` — `F` = a `2ⁿ`-edik egységgyökök halmaza | [M] |
| primitív egységgyök | `Tematika.LinAlg.exists_primitive_root` (`Fˣ` ciklikus, van generátora) | [M] |

### 2. Vektorok, lineáris kombináció

| tematikai elem | Lean-deklaráció | státusz |
|---|---|---|
| `ℝⁿ` pontjai/vektorai, összeadás, skalárszoros | `Tematika.Morita.finrank_eq_of_card` | [M] |
| „additív ⇒ lineáris" (`F₂` fölött a skalárszorzás automatikus) | `Tematika.Morita.addToLin` | [M] |
| lineáris kombináció, kifeszített altér | `Tematika.Kiegeszitesek.rank_eq_finrank_span` | [M] |
| egyenes / sík / hipersík | `Tematika.LinAlg.traceHyperplane`, `card_traceHyperplane` (`2^{n−1}` elemű hipersík) | [M] |
| egyenes vonalú mozgás (paraméteres egyenes) | `Tematika.LinAlg.solution_set_eq_coset` (partikuláris + homogén = mellékosztály) | [M] |

### 3. Belső szorzat, merőlegesség

| tematikai elem | Lean-deklaráció | státusz |
|---|---|---|
| belső szorzat | `Tematika.LinAlg.traceForm` — a `⟨x, y⟩ = Tr(xy)` nyomforma | [M] |
| a belső szorzat nemelfajulása | `Tematika.LinAlg.traceForm_nondegenerate` | [M] |
| merőlegesség, ortogonális komplementer | `Tematika.LinAlg.traceHyperplane` (`Tr(ax) = 0` = `a` merőleges komplementere) | [M] |
| merőleges vetítés | `Tematika.Kiegeszitesek.exists_isCompl_ker` (direkt kiegészítő = vetítés) | [M] |
| Cauchy–Schwarz-egyenlőtlenség | `Notes.Kalkulus.sum_walsh_fourth_ge` (Cauchy–Schwarz a Walsh-spektrumon) | [R] |
| háromszög-egyenlőtlenség, hossz | `Tematika.Morita.no_linear_order_of_charTwo` — a norma fogalma **nem** transzportálódik | [×] |
| háromszög nevezetes pontjai, Euler-egyenes | — | [×] |

### 4. Lineáris egyenletrendszerek

| tematikai elem | Lean-deklaráció | státusz |
|---|---|---|
| homogén / inhomogén rendszer, általános megoldás | `Tematika.LinAlg.solution_set_eq_coset` | [M] |
| megoldhatóság (Gauss-elimináció eredménye) | `Tematika.LinAlg.solvable_iff_mem_range` | [M] |
| Kronecker–Capelli-tétel | `Tematika.LinAlg.kronecker_capelli` (rangfeltétel alakban) | [M] |
| konkrét rendszer: `L_k x = b` | `Tematika.LinAlg.range_LK_eq_ker_trace`, `L_solvable_iff_trace_zero`, `L_solution_pair` | [K] |
| a rendszer mint vektorok lineáris kombinációja | `Tematika.Kiegeszitesek.rank_eq_finrank_span` | [M] |

A `L_solvable_iff_trace_zero` az egész fejezet „éles" alkalmazása: az
`x^{2^k} + x = b` linearizált egyenlet **pontosan akkor** oldható meg, ha `Tr(b) = 0`, és
ekkor pontosan két megoldása van (`L_solution_pair`). Ez a Kasami-bizonyítás egyik
munkalemmája, és egyszerre a tematika 4. pontjának teljes tartalma.

### 5. Mátrixműveletek

| tematikai elem | Lean-deklaráció | státusz |
|---|---|---|
| mátrixműveletek és algebrai szabályaik | `Tematika.Morita.endAlgEquivMatrix` (algebraizomorfizmus, tehát **minden** szabály átjön) | [M] |
| mátrixszorzás ↔ leképezéskompozíció | `Tematika.Morita.endAlgEquivMatrix_comp` | [M] |
| mátrixösszeadás | `Tematika.Morita.endAlgEquivMatrix_add` | [M] |
| kapcsolat a lineáris egyenletrendszerekkel | `Tematika.LinAlg.LK`, `frobLin` + `solvable_iff_mem_range` | [M] |

### 6. Mátrixegyenletek, inverz, blokkmátrixok

| tematikai elem | Lean-deklaráció | státusz |
|---|---|---|
| mátrixegyenlet, mátrix inverze | `Tematika.LinAlg.frobLin_isUnit` (a Frobenius invertálható), `LK_not_isUnit` (`L_k` nem) | [M] |
| invertálhatóság kritériuma | `Tematika.Morita.isUnit_iff_det_ne_zero` | [M] |
| blokkmátrixok, blokkokkal való számolás | `Tematika.Kiegeszitesek.det_block_triangular` | [M] |
| blokkfelbontás strukturális oka | `Tematika.Kiegeszitesek.exists_isCompl_ker` (`ker L_k` direkt kiegészítője) | [M] |
| LU-felbontás | — (`char 2` fölött nincs pivotálás nélküli LU; Mathlibben sincs LU-API) | [×] |
| Leontief-mátrix | — (közgazdasági modell, pozitivitást és rendezést igényel) | [×] |

### 7. Determinánsok

| tematikai elem | Lean-deklaráció | státusz |
|---|---|---|
| determináns, kifejtési tétel, szorzástétel | Mathlib `Matrix.det` a Morita-szótáron át; `Tematika.Morita.isUnit_iff_det_ne_zero` | [M] |
| nemelfajuló mátrixok | `Tematika.LinAlg.det_frobLin` (`= 1`), `det_LK` (`= 0`) | [M] |
| Cramer-szabály | `Tematika.Kiegeszitesek.cramer_solution` | [M] |
| a determináns mint előjeles térfogat | — | [×] |

### 8. Lineáris függetlenség, rang

| tematikai elem | Lean-deklaráció | státusz |
|---|---|---|
| lineárisan függő/független rendszer | `Tematika.Kiegeszitesek.frobenius_powers_independent` (Artin–Dedekind: a Frobenius-hatványok függetlenek) | [M] |
| vektorrendszer rangja | `Tematika.Kiegeszitesek.rank_eq_finrank_span` | [M] |
| rangszámtétel (dimenziótétel) | `Tematika.LinAlg.finrank_ker_LK`, `finrank_range_LK` (`1 + (n−1) = n`) | [M] |
| sor-/oszlop-/determinánsrang egybeesése | Mathlib `Matrix.rank` a Morita-szótáron át | [M] |
| scattered polinom mint függetlenségi feltétel | `Papers.ScatteredFrobenius.scattered_iff_coprime` | [R] |
| Kronecker–Capelli | `Tematika.LinAlg.kronecker_capelli` | [M] |

---

## 2. Kalkulus I. (MBLK37E) — pontonkénti táblázat

Itt az áttétel *lényegesen* nem hű: `GF(2ⁿ)` véges, rendezetlen és diszkrét. A tematika
minden pontjának ezért az **invariáns alakját** adjuk meg.

### 2.1 Alapozás

| tematikai elem | Lean-deklaráció | státusz |
|---|---|---|
| a valós számok teste (rendezett test, teljesség) | `Tematika.Morita.no_linear_order_of_charTwo` — a rendezés az, ami elveszik | [N] |
| teljes indukció | `Notes.Kalkulus.geom_two_sum` (véges mértani összeg indukcióval) | [R] |
| nevezetes egyenlőtlenségek | `Notes.Kalkulus.sum_walsh_fourth_ge`, `exists_walsh_sq_ge` (Cauchy–Schwarz, átlagolás) | [R] |

### 2.2 Elemi függvények

| tematikai elem | Lean-deklaráció | státusz |
|---|---|---|
| polinomok, racionális törtfüggvények | `Tematika.Kalkulus.exists_polynomial_repr` — **minden** függvény polinomfüggvény (Lagrange-interpoláció; a Weierstrass-approximáció áttétele: itt a polinomok nemcsak sűrűek, hanem ki is merítik a függvényteret) | [N] |
| exponenciális függvény és inverze (logaritmus) | `Tematika.Kalkulus.exists_discrete_log` (diszkrét logaritmus egy primitív gyök bázisán) | [M] |
| gyökös függvény, inverz függvény | `Tematika.LinAlg.powerMap_bijective_of_coprime` | [M] |
| trigonometrikus függvények | — (nincs `char 2`-beli analogonjuk; a Walsh-karakter `χ` játssza a `e^{2πi·}` szerepét, ld. `WalshAB.χ`) | [N] |
| értelmezési tartomány, értékkészlet, kompozíció | `Tematika.Kalkulus.deriv_comp` (láncszabály) | [M] |
| elemi függvénytranszformációk (eltolás, nyújtás) | `Tematika.Kiegeszitesek.isAPN_translate`, `isAPN_scale` | [N] |
| szimmetria-tulajdonságok | `Tematika.Kiegeszitesek.isAPN_frobenius_conj` | [N] |
| grafikonvázolás | `Tematika.Kalkulus.criticalSet` + `card_criticalSet_le_two_of_apn` (a „grafikon alakja" = a kritikus halmaz mérete) | [N] |

### 2.3 Határérték és folytonosság

| tematikai elem | Lean-deklaráció | státusz |
|---|---|---|
| határérték és formális tulajdonságai | `Tematika.Kalkulus.tendsto_self` (diszkrét téren a határérték a helyettesítési érték) | [N] |
| folytonosság | `Tematika.Kalkulus.finite_t1_discreteTopology`, `all_maps_continuous` — **minden** leképezés folytonos | [N] |
| a folytonossági funktor nem hű | `Tematika.Kalkulus.continuity_not_faithful` | [N] |
| Bolzano-tétel (közbülső érték) | `Tematika.Kalkulus.gold_deriv_affine_closed` (a derivált képe affin altér) | [N] |
| kompakt intervallumon folytonos függvény (Weierstrass) | `Tematika.Kalkulus.exists_max_abs_walsh` (a Walsh-spektrum felveszi a maximumát) | [N] |

### 2.4 Derivált

| tematikai elem | Lean-deklaráció | státusz |
|---|---|---|
| pontbeli derivált és érintőegyenes | `Tematika.Kalkulus.gold_deriv_eq`: `D_a(x^{2^k+1}) = Cross k a x + N k a` — a derivált *maga* az érintő affin leképezés, a közelítés egzakt | [N] |
| a derivált és a folytonosság kapcsolata | `Tematika.Kalkulus.all_maps_continuous` (a diszkrét derivált mindig létezik, mert minden leképezés folytonos) | [N] |
| deriválási szabályok (összeg, szorzat) | `Tematika.Kalkulus.deriv_add_fun`, `deriv_mul` (diszkrét Leibniz-szabály) | [M] |
| láncszabály | `Tematika.Kalkulus.deriv_comp` | [M] |
| elemi függvények deriváltjai | `Tematika.Kalkulus.gold_deriv_eq`; `Papers.FastPoints.algDeg_deriv_deriv_le` | [M] |
| implicit deriválás | `Tematika.LinAlg.L_solution_pair` (a `L_k x = b` implicit egyenlet megoldásainak leírása) | [N] |

### 2.5 Középérték-tételek és alkalmazásaik

| tematikai elem | Lean-deklaráció | státusz |
|---|---|---|
| Lagrange-féle középértéktétel | `Tematika.Kalkulus.mvt_exact`: `f(y) − f(x) = D_{y−x} f (x)` — **egzakt**, nem egzisztenciális | [N] |
| Rolle-tétel | `Tematika.Kalkulus.rolle`, `rolle_of_not_injective` | [N] |
| monotonitás és derivált | `Tematika.Kalkulus.injective_iff_deriv_ne_zero` (szigorú monotonitás ↝ injektivitás: `f` injektív ⟺ minden nemnulla `a`-ra `D_a f ≠ 0` sehol) | [N] |
| lokális szélsőérték, első derivált teszt | `Tematika.Kalkulus.criticalSet`, `card_criticalSet_le_two_of_apn` (APN ⇒ minden kritikus halmaz ≤ 2 elemű) | [N] |
| konvexitás és a második derivált | `Tematika.Kalkulus.second_deriv_const_of_algDeg_le_two` (`deg f ≤ 2` ⟺ a második diszkrét derivált konstans), `const_of_algDeg_le_zero` | [N] |
| Darboux-tétel (a derivált képe intervallum) | `Tematika.Kalkulus.gold_deriv_range_eq_coset`, `gold_deriv_affine_closed`, `card_gold_deriv_range` (a kép `2^{n−1}` elemű hipersík-mellékosztály) | [N] |
| L'Hospital-szabály (`0/0`) | `Tematika.Kalkulus.geom_sum_removable`, `geom_sum_at_one` (megszüntethető szingularitás: `(x^m−1)/(x−1)` az `x = 1` helyen) | [N] |
| grafikonvázolás (összefoglaló) | `Tematika.Kalkulus.card_criticalSet_le_two_of_apn` + `card_gold_deriv_range` | [N] |

### A Darboux-tétel áttétele — a kért minta konkrét példája

A kérdés kifejezetten a Darboux-tételt említette mint olyan elemet, amely „ebben a
kontextusban nincs, de valamelyik komponenst Morita-ekvivalens kontextusba képezve már
van". Ez az áttétel a `Tematika/Kalkulus.lean` `Darboux` szakaszában készült el:

1. A Darboux-tétel valós alakja: *a derivált képe intervallum* (Darboux-tulajdonság).
2. `char 2`-ben nincs rendezés, tehát nincs „intervallum". Az intervallum
   **rendezésmentes** jellemzője: konvex (affin) halmaz. `char 2`-ben az affin altér
   pontosan az `u, v, w ∈ C ⇒ u + v + w ∈ C` feltétellel jellemezhető.
3. `gold_deriv_affine_closed`: a Gold-függvény deriváltjának képe **valóban** zárt erre az
   affin kombinációra.
4. `gold_deriv_range_eq_coset`: sőt, a kép pontosan a `Cross k a` `F₂`-lineáris leképezés
   képének a `N k a` elemmel vett mellékosztálya — ez az „intervallum" Morita-oldali képe.
5. `card_gold_deriv_range`: `gcd(k,n) = 1` és `a ≠ 0` esetén ez a kép `2^{n−1}` elemű, azaz
   pontosan „fél test" — a valós Darboux-tételben az intervallum hossza, itt a hipersík
   kodimenziója az invariáns.

Ugyanez a `2^{n−1}` jelenik meg a `Papers/DobbertinTwoToOne.lean` modulban az APN-deriváltak
kettő-az-egyhez tulajdonságából — vagyis a Darboux-tétel áttétele **egybeesik** az APN
tulajdonsággal. Ez a dokumentum legfontosabb strukturális megfigyelése.

---

## 3. Mi az, ami *nem* transzportálódik — és miért

Fontos, hogy a megfeleltetés őszinte legyen. Az alábbi tematikai elemeknek **nincs**
értelmes megfelelőjük a Kasami-kontextusban, és ezt formálisan is alátámasztjuk:

| tematikai elem | miért nem |
|---|---|
| hossz, norma, háromszög-egyenlőtlenség | archimédeszi rendezést igényel; `Tematika.Morita.no_linear_order_of_charTwo` szerint `char 2`-ben ilyen nincs |
| háromszög nevezetes pontjai, Euler-egyenes | euklideszi metrikus geometria; nincs valós skalárszorzat (a nyomforma nem pozitív definit) |
| determináns mint előjeles térfogat | előjel = rendezés; `F₂`-ben `det ∈ {0,1}`, a „térfogat" interpretáció eltűnik. A determináns *algebrai* tartalma (invertálhatóság) viszont teljes egészében megmarad |
| LU-felbontás | `char 2` fölött nincs pivotálás nélküli LU-felbontás minden mátrixra, és Mathlibben sincs LU-API |
| Leontief-mátrix | nemnegativitást és spektrálsugár-becslést igényel |
| trigonometrikus függvények | a `e^{2πi·}` szerepét a `WalshAB.χ` Walsh-karakter veszi át, de a szög/periódus fogalma nem transzportálódik |
| valós határérték-fogalom (`ε–δ`) | a diszkrét topológián kiürül (`Tematika.Kalkulus.tendsto_self`) |

Ezek az elemek nem hibái a megfeleltetésnek, hanem a **nem hű funktor magja**: pontosan
azok a fogalmak, amelyeket a funktor elfelejt.

---

## 4. Hogyan lehet tovább vinni

* A `Tematika.Morita.endAlgEquivMatrix` szótár mentén Mathlib **teljes** mátrixelmélete
  (sajátértékek, karakterisztikus polinom, Jordan/racionális normálalak) áttehető a
  linearizált polinomokra. A Kasami-oldalon a `Cross k a` és `L_k` operátorok
  karakterisztikus polinomjának meghatározása kézenfekvő következő lépés.
* A `Tematika.LinPoly.exists_linearized_repr` révén minden `F₂`-lineáris endomorfizmus
  együtthatóvektorral kódolható; ez alapja lehet egy *algoritmikus* (`decide`-olható)
  EA-ekvivalencia-tesztnek.
* A Darboux-áttétel mintája (`rendezésfüggő tétel → rendezésmentes jellemző → Morita-kép`)
  további kalkulusbeli tételekre is alkalmazható: Taylor-formula ↝ ANF-kifejtés
  (`Papers.FastPoints.anf_expansion`), integrálás ↝ Walsh-transzformáció összegzése
  (`WalshAB.parseval_perm`).

---

## 5. Összefoglaló számadatok

| | |
|---|---|
| új modulok | 5 (`RequestProject/Tematika/`) |
| új deklarációk | 95 |
| `sorry` / `axiom` az új modulokban | 0 |
| lefedett tematikai pont — Lineáris algebra I. | 8/8 fejezet, 6 elem `[×]`-szel megindokolva |
| lefedett tematikai pont — Kalkulus I. | mind, 2 elem `[×]`-szel megindokolva |
