# Kompetencia-lefedettségi mátrix — Kalkulus I és Lineáris algebra I

**Mire való ez a dokumentum?** A validáció (SZTE TVSZ 3. sz. melléklet **3.8. pont**) útján benyújtott
kreditelismerési kérelem *kulcsmelléklete*: tantárgyanként, **tematikai pontonként** megmutatja,

* mi a tanegység minimumkövetelménye (tételsor / tematika szerinti pont),
* melyik **gépileg ellenőrzött saját bizonyítás** fedi le (`RequestProject/…`),
* és melyik **Mathlib-hozzájárulás** (`mathlib-prs/NN-….patch`) igazolja ugyanezt a kompetenciát
  *külső, önkéntes, nyilvánosan bírált munkakörnyezetben*.

A szabályzati háttér és az eljárásrend a [`KREDITELISMERES.md`](KREDITELISMERES.md) fájlban van;
a hozzájárulások technikai leírása a [`MATHLIB-PR-JAVASLATOK.md`](MATHLIB-PR-JAVASLATOK.md) fájlban.
Ez a fájl a kettőt köti össze.

> **2026‑08‑29‑i kiegészítés.** A Kalkulus I esetében a *tételsor* (K‑1…K‑18) mellett a Neptun
> **tárgytematika** („Tantárgy tartalma”, `KalkulusIelőadás-3.pdf`) szerinti, elemenkénti nézet is
> elkészült: [`KALKULUS-TEMATIKA-PR-TABLAZAT.md`](KALKULUS-TEMATIKA-PR-TABLAZAT.md) (T‑1…T‑20).
> Az ott hiányzó pontokat a `RequestProject/Kreditelismeres/KalkulusTematika.lean` modul fedi le.

> **2026‑08‑30‑i kiegészítés.** A tematika-táblázat kapott egy **(C) oszlopot** a ténylegesen
> beküldött, nyilvános Mathlib pull requestekkel (**✅ = merge-elve a `master`-ben**, **⬜ = még nem**),
> és egy részletes **2/b. szakaszt** mind a 18 PR-ral. Összesen **6 PR merge-elve**, köztük a
> **Darboux-PR** ([#42810](https://github.com/leanprover-community/mathlib4/pull/42810), K‑16 /
> T‑16: monotonitás és derivált) és a konvexitási hibajavítás
> ([#42579](https://github.com/leanprover-community/mathlib4/pull/42579), K‑17 / T‑18).
> A forrásáttekintő: [`pr-attekintes/`](pr-attekintes/).

> **Megjegyzés.** Ez munkaanyag, nem hivatalos állásfoglalás. A tényleges elbírálás a
> TTIK Kreditátviteli Bizottságának hatásköre.

---

## 1. Miért „formális” kontextus egy Mathlib-hozzájárulás?

A 3.8. pont *nem felsőoktatásban megszerzett kompetenciákról, informális tudásról, tanulási
eredményekről vagy munkatapasztalatról* beszél. A Mathlib-be végzett önkéntes közreműködés
a „nem felsőoktatási” kategóriába esik, de **szervezettségében és számonkérésében** közel áll
egy formális képzéshez — és éppen ez az, amit a 4.2. pont mérlegelni enged:

| 4.2. szerinti szempont | Mi felel meg neki a Mathlib-munkában? |
|---|---|
| az ismeretek **alkalmazásának gyakorlása** | minden patch egy konkrét, meglévő tétel megértését és átírását igényli; nem reprodukció, hanem alkalmazás |
| **gyakorlati és elméleti** ismeretek aránya | a bizonyítás elméleti (a matematikai lépés), a `lake build` gyakorlati (fordítás, CI, verziókövetés) |
| **ráfordított munkaidő** | git-commitok és PR-időbélyegek alapján dokumentálható |
| **számonkérési rendszer** | (i) a Lean 4 típusellenőrzője — hibatűrés nélküli gépi ellenőrzés; (ii) a Mathlib CI (fordítás + linterek); (iii) **maintaineri code review** — szakértői, külső bírálat |
| **elévülés** | a hozzájárulások frissek, a pinned commit dátuma `2026-02-16` |

Ehhez jön a 4.4. pont: ugyanaz a kompetencia **több tárgynál** is felhasználható, tehát a
formalizációs kompetencia párhuzamosan hivatkozható a Kalkulus I és a Lineáris algebra I
kérelemben is (természetesen külön-külön kérelemben, tárgyanként egy tárgyelemmel).

**Amit a hozzájárulás önmagában nem igazol:** a teljes tematika ismeretét. Ezért kettős a
bizonyítás szerkezete: **(A)** a tematika minden pontjára saját, `sorry`-mentes Lean-bizonyítás,
**(B)** a pontok egy részére ezen felül külső bírálaton átment Mathlib-hozzájárulás.

---

## 2. A minimumkövetelmények forrása

* **Kalkulus I:** a repóban lévő `kalkulus-tetelsor-2025.pdf` — 18 tételsor-pont. A K‑1…K‑18
  kódok ennek a sorszámozását követik. (A tételsorban **nem szerepel** a Riemann-integrál.)
* **Lineáris algebra I:** a `LineárisalgebraI.-6.pdf` és `-7.pdf` (MBLK15E). Ezek a fájlok
  **képalapúak** (nem tartalmaznak kinyerhető szöveget), ezért a tematikai blokkokat
  (L‑1…L‑8) a jegyzet fejezetbeosztása szerint rögzítettük; a beadás előtt érdemes a
  **hivatalos tantárgyi adatlap** tanulási-eredmény pontjaira átszámozni.

| Kód | Kalkulus I tételsor-pont (rövidítve) |
|---|---|
| K‑1 | korlátosság, szuprémum, infimum, teljességi axióma, racionális/irracionális számok |
| K‑2 | nevezetes egyenlőtlenségek (Cauchy–Schwarz, Bernoulli) |
| K‑3 | függvénytulajdonságok: monotonitás, korlátosság, szimmetria, injektivitás, bijektivitás |
| K‑4 | hatvány- és exponenciális függvények |
| K‑5 | függvénytranszformációk, inverz, logaritmus, arkuszfüggvények |
| K‑6 | határérték, féloldali határérték, a határérték egyértelműsége |
| K‑7 | műveletek határértékekkel, összetett függvény határértéke, kibővített számegyenes |
| K‑8 | határérték és egyenlőtlenségek, rendőrelv |
| K‑9 | folytonosság, műveletek, összetett és inverz függvény, szakadási helyek |
| K‑10 | az `e` szám; monoton korlátos függvény határértéke |
| K‑11 | Bolzano–Darboux-tétel, kompakt intervallumon folytonos függvények |
| K‑12 | differenciálhányados, ekvivalens definíció, differenciálhatóság ⇒ folytonosság |
| K‑13 | differenciálási szabályok, féloldali derivált, inverz differenciálhatósága |
| K‑14 | szélsőérték szükséges feltétele, Rolle tétele |
| K‑15 | Lagrange- és Cauchy-féle középértéktétel, konstans függvény jellemzése |
| K‑16 | monotonitás és derivált, lokális szélsőérték elegendő feltétele |
| K‑17 | konvexitás, L'Hospital-szabály |
| K‑18 | Taylor-polinom, Taylor tétele, hibabecslés |

| Kód | Lineáris algebra I tematikai blokk |
|---|---|
| L‑1 | komplex számok: kanonikus és trigonometrikus alak, Moivre, gyökvonás, egységgyökök |
| L‑2 | vektorok és pontok `ℝⁿ`-ben, lineáris kombináció, egyenes, sík |
| L‑3 | belső szorzat, hossz, háromszög-egyenlőtlenség, merőlegesség, vetítés |
| L‑4 | lineáris egyenletrendszerek, elemi átalakítások, Gauss-elimináció |
| L‑5 | mátrixműveletek, mátrixegyenletek, lineáris leképezés mátrixa, blokkmátrixok |
| L‑6 | determinánsok: kifejtés, szorzástétel, Cramer-szabály, karakterisztikus polinom |
| L‑7 | mátrix inverze, nemelfajuló mátrixok, ortogonális/unitér mátrixok |
| L‑8 | lineáris függetlenség, rang, rangszámtétel, Kronecker–Capelli |

---

## 3. Kalkulus I — pontonkénti lefedettség

Rövidítések: **(A)** = saját, gépileg ellenőrzött bizonyítás; **(B)** = Mathlib-hozzájárulás.
A Lean-deklarációk a `RequestProject/Kreditelismeres/KalkulusHatarertek.lean` (K‑1…K‑11) és
`…/KalkulusDifferencial.lean` (K‑12…K‑18) fájlokban vannak.

| Pont | (A) saját bizonyíték (kiemelt deklarációk) | (B) Mathlib-patch | Lefedve |
|---|---|---|---|
| K‑1 | `exists_isLUB_of_bddAbove`, `isLUB_unique`, `irrational_sqrt_two'`, `rat_dense`, `irrational_dense` | `17` (`sInf_eq_top'` — hiányzó duális állítás a teljes hálókban) | igen |
| K‑2 | `cauchy_schwarz_sum`, `bernoulli_ineq`, `am_gm_two` | `10`, `11` (Hölder-egyenlőtlenség, `posLog` becslés) | igen |
| K‑3 | `strictMono_cube'`, `bijective_cube`, `cos_even_sin_odd`, `exists_unique_even_odd_decomp` | — | igen |
| K‑4 | `exp_strictMono'`, `log_mul_eq` | `03`, `08`, `13`, `23` (rpow-definíció, `(xy)^z`, log-becslések, aszimptotika) | igen |
| K‑5 | `log_exp_inverse`, `arcsin_left_inverse` | `02` (`arccos_cos`), `04`, `12` | igen |
| K‑6 | `LimitAt` (saját ε–δ definíció), `limitAt_unique`, `limitAt_iff_tendsto`, `limitAt_iff_left_right` | — | igen |
| K‑7 | `limitAt_const`, `limitAt_id`, `limitAt_add`, `limitAt_mul`, `limitAt_div` | — | igen |
| K‑8 | `limitAt_le_of_le`, `limitAt_squeeze`, `limit_x_mul_sin_inv` | — | igen |
| K‑9 | `ContinuousAtEps`, `continuousAtEps_iff`, `continuousAtEps_comp`, `sign_jump_discontinuity` | — | igen |
| K‑10 | `tendsto_of_monotone_bddAbove`, `one_add_inv_pow_monotone`, `one_add_inv_pow_lt_four`, `tendsto_one_add_inv_pow_exp_one` | — | igen |
| K‑11 | Bolzano–Darboux és Weierstrass (`KalkulusHatarertek.lean`, 11. tétel szakasz) | `14` (**hibás állítás javítása** a Mathlib Darboux-fájljában) | igen |
| K‑12 | `hasDerivAt_iff_limitAt_slope`, `hasDerivAt_iff_littleO`, `continuousAt_of_hasDerivAt`, `abs_continuous_not_differentiable` | — | igen |
| K‑13 | `deriv_add_rule`, `deriv_mul_rule`, `deriv_div_rule`, `deriv_comp_rule`, `deriv_inverse_rule` | `24` (az inverz- és implicitfüggvény-tétel fájljainak takarítása) | igen |
| K‑14 | `fermat_deriv_eq_zero`, `rolle` | — | igen |
| K‑15 | `lagrange_mvt`, `cauchy_mvt`, `const_of_deriv_eq_zero`, `sub_const_of_deriv_eq` | — | igen |
| K‑16 | `monotoneOn_of_deriv_nonneg'`, `strictMonoOn_of_deriv_pos'`, `isLocalMin_of_deriv_sign`, `isLocalMin_of_deriv2_pos` | — | igen |
| K‑17 | `convexOn_of_deriv2_nonneg'`, `convexOn_chord`, `lhospital_zero_right`, `limit_sin_div_x` | `01` (`HasDerivAt.lhopital_zero_right_on_Ioo`) | igen |
| K‑18 | `taylorPoly`, `taylor_lagrange`, `taylor_sin_error`, `taylor_exp_error` | — | igen |

**Számszerű összegzés (Kalkulus I).** 18 tematikai pontból **18-hoz** van saját, `sorry`-mentes,
gépileg ellenőrzött bizonyíték → **100 %**; ebből **9 ponthoz** (K‑1, K‑2, K‑4, K‑5, K‑11, K‑13,
K‑17 és részben K‑18 környéke) tartozik **külső Mathlib-hozzájárulás** is → **50 %** kettős fedés.
A 4.1. b) pont szerinti 75 %-os küszöb az (A) oszlop alapján teljesül.

---

## 4. Lineáris algebra I — blokkonkénti lefedettség

A Lean-deklarációk a `RequestProject/Kreditelismeres/LinAlgKomplexVektor.lean` (L‑1…L‑3) és
`…/LinAlgMatrixDeterminans.lean` (L‑4…L‑8) fájlokban vannak.

| Blokk | (A) saját bizonyíték (kiemelt deklarációk) | (B) Mathlib-patch | Lefedve |
|---|---|---|---|
| L‑1 | `complex_canonical`, `complex_trig_form`, `moivre`, `complex_nth_roots_card`, `sum_nth_roots_of_unity`, `primitive_root_iff` | `04`, `09`, `12` | igen |
| L‑2 | `lineThrough`, `mem_lineThrough_iff`, `collinear_iff_dependent`, `planeThrough` | `22` (alterek képe koprodukció mentén) | igen |
| L‑3 | `dotProd`, `cauchy_schwarz_dot`, `norm2_triangle`, `pythagoras`, `orthogonal_projection_line`, `projection_minimizes` | `23` (pozitív operátorok fájljának takarítása) | igen |
| L‑4 | `homogeneous_solutions_subspace`, `general_solution`, `swap_rows_solutions`, `scale_row_solutions`, `add_row_solutions`, `cramer_rule` | — | igen |
| L‑5 | `matrix_algebra`, `transpose_mul_eq`, `block_mul_eq`, `matrix_equation_unique` | `07`, `16`, `21`, `22` | igen |
| L‑6 | `det_expand_row_zero`, `det_mul'`, `det_transpose'`, `det_upper_triangular` | `05`, `18` (`LinearEquiv.det_coe_symm`), `20` | igen |
| L‑7 | `inverse_unique`, `inverse_mul`, `invertible_iff_det_ne_zero`, `unique_solution_of_det_ne_zero` | `06`, `15` | igen |
| L‑8 | `card_le_of_linearIndependent`, `row_rank_eq_col_rank`, `rank_le_min`, `rank_nullity_matrix`, `kronecker_capelli` | `19` (`natCast_le_rank_iff` deduplikáció), `23` | igen |

**Számszerű összegzés (Lineáris algebra I).** 8 tematikai blokkból **8-hoz** van saját,
`sorry`-mentes bizonyíték → **100 %**; ebből **7 blokkhoz** tartozik Mathlib-hozzájárulás is
→ **87,5 %** kettős fedés.

---

## 5. Hozzájárulás → kompetencia (mit igazol konkrétan)

| # | Patch | Mit tesz | Milyen kompetenciát igazol | Kód |
|---|---|---|---|---|
| 01 | `01-lhopital-flexible-linter` | maintainer-TODO + linter-kivétel megszüntetése | a L'Hospital-szabály feltételrendszerének pontos kezelése | K‑17 |
| 02 | `02-arccos-cos-flexible-linter` | bizonyítás újraírása | arkuszfüggvények értelmezési tartománya | K‑5 |
| 03 | `03-rpow-flexible-linter` | két bizonyítás esetszétválasztásra írása | hatványfüggvény `exp`/`log` definíciója | K‑4 |
| 04 | `04-cos-eq-cos-iff-flexible-linter` | linter-kivétel + felesleges argumentum törlése | trigonometrikus egyenletek megoldáshalmaza | K‑5, L‑1 |
| 05 | `05-charpoly-inv-flexible-linter` | linter-kivétel megszüntetése | karakterisztikus polinom, inverz mátrix | L‑6 |
| 06 | `06-trace-units-conj-docprime` | elavult kivétel + hiányzó dokumentáció | nyom, konjugálás, invertálható mátrixok | L‑7 |
| 07 | `07-toMatrix-dualTensorHom-flexible-linter` | kivétel + két felesleges argumentum | lineáris leképezés mátrixa | L‑5 |
| 08 | `08-obsolete-flexible-exceptions` | **tiszta törlés** | hatványfüggvény monotonitása | K‑4 |
| 09 | `09-complex-samerayiff-linters` | két linter-kivétel megszüntetése | komplex szám argumentuma, azonos irány | L‑1 |
| 10 | `10-poslog-sum-flexible-linter` | TODO + kivétel | logaritmus, összegbecslés | K‑4, K‑2 |
| 11 | `11-holder-ennreal-flexible-linter` | TODO + kivétel | Hölder-egyenlőtlenség | K‑2 |
| 12 | `12-arg-periodic-dedup` | TODO + golfolás általános tétellel (−5 sor) | egységkör, periodicitás | L‑1, K‑5 |
| 13 | `13-rpow-log-duplicates` | **6 duplikált lemma törlése** | hatvány/logaritmus egyenlőtlenségek | K‑4 |
| 14 | `14-darboux-docstring-mismatch` | **hibás állítás javítása** | Darboux-tulajdonság, közbülsőérték | K‑11, K‑13 |
| 15 | `15-unitarygroup-coe-duplicates` | 3 duplikált `simp`-lemma elavultnak jelölése | unitér mátrixok | L‑7 |
| 16 | `16-tolin-primed-duplicates` | 4 duplikátum + hívási helyek átírása | mátrix ↔ lineáris leképezés | L‑5 |
| 17 | `17-sInf-eq-top-dual` | hiányzó duális állítás pótlása | szuprémum/infimum dualitás | K‑1 |
| 18 | `18-lineareq-det-coe-symm-golf` | linter-kivétel megszüntetése, `simp` helyett termbizonyítás | `det(f⁻¹) = (det f)⁻¹` | L‑6 |
| 19 | `19-natcast-le-rank-iff-duplicate` | **duplikált rang-lemma** elavultnak jelölése | rang és lineáris függetlenség kapcsolata | L‑8 |
| 20 | `20-free-of-det-ne-one-duplicate` | **szó szerint duplikált bizonyítás** törlése | determináns és bázis létezése | L‑6 |
| 21 | `21-todual-eq-repr-duplicate` | duplikált lemma + hívási helyek | bázis, koordináták, duális bázis | L‑5 |
| 22 | `22-map-coprod-prod-duplicate` | duplikált lemma + hívási hely | alterek képe, direkt összeg | L‑2, L‑5 |
| 23 | `23-expired-deprecations-linalg-analysis` | **tiszta törlés**: 4 lejárt elavult alias | generált altér, hatványaszimptotika, pozitív operátor | L‑8, K‑4, L‑3 |
| 24 | `24-expired-deprecations-calculus` | **tiszta törlés**: 30 lejárt elavult alias (−102 sor) | inverz- és implicitfüggvény-tétel | K‑13 |
| 25 | `25-stale-integral-ofreal-todo` | **tiszta törlés**: már teljesített TODO | integrál és valós→komplex beágyazás | (tematikán kívüli) |

---

## 6. Őszinte hiányelemzés

1. **Kézi számolási rutin.** A formalizáció nem igazolja jól a papíron végzett
   függvényvizsgálatot, határérték- és deriválási rutint. Pótlás: a `kalkulus_gyakorlo.pdf`
   feladatainak saját kezű megoldásai, illetve a formalizált tételekhez csatolt konkrét
   numerikus példák.
2. **Gauss-elimináció mint algoritmus.** A megoldáshalmaz invarianciája elemi
   sorátalakításokra formalizálva van (`swap_rows_solutions`, `scale_row_solutions`,
   `add_row_solutions`), de a lépésenkénti kézi számolás nem.
3. **Vizsgahelyzet.** A validáció nem helyettesíti a szóbeli számonkérést; a Bizottság a 8. pont
   szerint az érdemjegyet maga állapítja meg.
4. **A PR-ok státusza.** A `mathlib-prs/` fájlok **benyújtásra kész** diffek: mindegyik lefordul
   a pinned commiton, de a *merged* státusz csak a tényleges benyújtás után hivatkozható.
   A kérelemben ezt pontosan így kell feltüntetni (nyitott / merged, dátummal).

---

## 7. Ellenőrzőlista a melléklethez

- [ ] Hivatalos tantárgyi adatlap beszerezve; a K‑/L‑kódok átszámozva az adatlap tanulási
      eredményeire.
- [ ] A 3. és 4. fejezet táblázatához csatolva a `lake build` napló és a `rg -n "sorry"` üres
      találata.
- [ ] Minden benyújtott PR-hoz: URL, státusz, dátum, a `mathlib-prs/*.patch` fájl.
- [ ] A lefedettségi százalék kiírva a kérelem indoklásába (4.1. b) pont).
- [ ] A 6. fejezet hiányai mellé pótlási terv.
