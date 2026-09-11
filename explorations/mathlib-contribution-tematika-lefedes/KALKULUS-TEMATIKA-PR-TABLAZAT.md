# Kalkulus I (MBLK37E) — a **tárgytematika „Tantárgy tartalma”** pontjai
## tematikai elem ↔ saját Lean-bizonyíték ↔ Mathlib-hozzájárulás ↔ kreditátviteli teendő

**Forrás:** `KalkulusIelőadás-3.pdf` (Neptun *Tárgytematika*, 2025/26/1, Kalkulus I előadás,
MBLK37E, Bolyai Intézet / TTIK‑MatTan, tárgyfelelős: Dr. Pusztai Béla Gábor, kollokvium,
14/0/0 féléves óraszám).

Ez a dokumentum **a tematika „Tantárgy tartalma” mezőjét** bontja elemeire (T‑1 … T‑20), és
minden elemhez megadja:

1. **(A)** melyik saját, gépileg ellenőrzött Lean-bizonyítás fedi le,
2. **(B)** melyik Mathlib-hozzájárulás (kész patch a `mathlib-prs/` mappában) tartozik hozzá,
   vagy — ha nincs ilyen — melyik **konkrét, ellenőrzött PR-jelölt** vehető célba,
3. **(C)** melyik **ténylegesen beküldött, nyilvános Mathlib pull request** tartozik hozzá —
   **✅ = már merge-elve** a `master` ágba, **⬜ = még nincs** (nyitott, lezárt vagy be sem küldött);
   a részletes lista a **2/b. szakaszban**, a forrás a `pr-attekintes/` melléklet,
4. **miért „high-leverage”** az adott hozzájárulás (mit *bizonyít* a bíráló bizottság felé),
5. **mit kell tenni**, hogy az adott pont a kreditelismerésben (validáció) elfogadható legyen.

A szabályzati hátteret és az eljárásrendet a [`KREDITELISMERES.md`](KREDITELISMERES.md), a
tételsor-alapú (K‑1…K‑18) lefedettséget a [`KOMPETENCIA-LEFEDETTSEG.md`](KOMPETENCIA-LEFEDETTSEG.md),
a hozzájárulások technikai leírását a [`MATHLIB-PR-JAVASLATOK.md`](MATHLIB-PR-JAVASLATOK.md) és a
[`mathlib-prs/MASTER-2026-08-STATUS.md`](mathlib-prs/MASTER-2026-08-STATUS.md) tartalmazza.
Ez a fájl a **tematika (nem a tételsor)** szerinti nézet.

> **Őszinteség-záradék.** Két különböző dolgot két külön oszlop tartalmaz. A **(C)** oszlop és a
> **2/b. szakasz** valódi, számmal hivatkozható pull requesteket sorol (✅ = a `master`-ben van,
> merge-commit megadva; ⬜ = még nincs). Ezzel szemben a `mathlib-prs/` alatti diffek **benyújtásra kész**, lefordított
> patchek — **nem** merged PR-ok, ezért **PR-számot nem lehet hozzájuk írni**. Minden
> „PR‑jelölt" sor a projekt rögzített Mathlib-bázisán (`8f9d9cff6bd728b17a24e163c9402775d9e6a365`,
> Lean 4.28.0) **ellenőrzött találat** (fájl + sorszám megadva), de a benyújtás előtt a mai
> `master`-en újra kell ellenőrizni: a `MASTER-2026-08-STATUS.md` szerint a 25 korábbi
> javaslatból 12 időközben elavult, mert az upstream megoldotta.

---

## 1. A „Tantárgy tartalma” szó szerint, elemekre bontva

> „A valós számtest. Teljes indukció. Nevezetes egyenlőtlenségek. Polinomok, racionális
> törtfüggvények, gyökös, trigonometrikus, exponenciális függvények és inverzeik. Értelmezési
> tartomány, értékkészlet, inverz függvény, összetétel. Grafikonok vázolása, szimmetria
> tulajdonságok, monotonitás. Elemi függvénytranszformációk. Függvények határértéke. A határérték
> formális tulajdonságai, műveletek. Elemi határérték-számítási technikák. Folytonosság fogalma,
> formális tulajdonságai. Folytonos függvények tulajdonsága: középérték-tétel, kompakt
> intervallumon folytonos függvények. Pontbeli derivált és érintőegyenes. Kapcsolat a
> folytonossággal, deriválási szabályok. Elemi függvények deriváltja. Láncszabály, implicit
> deriválás. Középérték-tételek. Monotonitás és derivált kapcsolata. Lokális szélsőérték és
> derivált (első és második derivált teszt), intervallumon vett szélsőértékek. Konvexitás fogalma,
> kapcsolata a második deriválttal. Függvények grafikonjának vázolása. L'Hospital szabályok és
> alkalmazásaik.”

| Kód | Tematikai elem | Tételsor-megfelelő |
|---|---|---|
| T‑1 | A valós számtest | K‑1 |
| T‑2 | Teljes indukció | (tételsoron kívül, gyakorlat) |
| T‑3 | Nevezetes egyenlőtlenségek | K‑2 |
| T‑4 | Polinomok, racionális törtfüggvények, gyökös, trigonometrikus, exponenciális függvények és inverzeik | K‑4, K‑5 |
| T‑5 | Értelmezési tartomány, értékkészlet, inverz függvény, összetétel | K‑3, K‑5 |
| T‑6 | Grafikonok vázolása, szimmetria, monotonitás | K‑3 |
| T‑7 | Elemi függvénytranszformációk | K‑5 |
| T‑8 | Függvények határértéke | K‑6 |
| T‑9 | A határérték formális tulajdonságai, műveletek | K‑7 |
| T‑10 | Elemi határérték-számítási technikák | K‑8, K‑10 |
| T‑11 | Folytonosság fogalma, formális tulajdonságai | K‑9 |
| T‑12 | Folytonos függvények: középérték-tétel, kompakt intervallumon folytonos függvények | K‑11 |
| T‑13 | Pontbeli derivált és érintőegyenes; kapcsolat a folytonossággal, deriválási szabályok | K‑12, K‑13 |
| T‑14 | Elemi függvények deriváltja; láncszabály, implicit deriválás | K‑13 |
| T‑15 | Középérték-tételek | K‑14, K‑15 |
| T‑16 | Monotonitás és derivált kapcsolata | K‑16 |
| T‑17 | Lokális szélsőérték és derivált (első/második derivált teszt), intervallumon vett szélsőértékek | K‑16 |
| T‑18 | Konvexitás fogalma, kapcsolata a második deriválttal | K‑17 |
| T‑19 | Függvények grafikonjának vázolása | (összefoglaló) |
| T‑20 | L'Hospital szabályok és alkalmazásaik | K‑17 |

---

## 1/b. Nyilvános repozitórium és a tankönyv-formalizációk

**Repozitórium:** <https://github.com/attilavjda/szte-mathematics-bsc> — ide kerül a
dosszié anyaga, és itt jelenik meg két további, nyílt forráskódú hozzájárulás is:

| Tankönyv | Könyvtár | Tartalom |
|---|---|---|
| Szabó László: *Bevezetés a lineáris algebrába* | `linearis-algebra/` | a tankönyv definícióinak és tételeinek Lean 4 (Mathlib) formalizációja |
| Leindler László: *Analízis* | `kalkulus/` | a tankönyv definícióinak és tételeinek Lean 4 (Mathlib) formalizációja |

*(2026‑08‑30-i állapot: a repóban a `README` volt közzétéve, a két könyvtár feltöltése
folyamatban van.)* Ugyanezek az adatok szerepelnek az `Oklevel/` alatti oklevél-változatokon is.

---

## 2. Fő táblázat — (A) saját bizonyíték és (B) Mathlib-hozzájárulás pontonként

Rövidítések a Lean-modulokra:
* **H** = `RequestProject/Kreditelismeres/KalkulusHatarertek.lean`
* **D** = `RequestProject/Kreditelismeres/KalkulusDifferencial.lean`
* **T** = `RequestProject/Kreditelismeres/KalkulusTematika.lean` *(ez a tematikához készült új modul)*
* **P** = `RequestProject/Portfolio/Kalkulus.lean` (gyakorlófeladatok formalizálva)

| Kód | (A) saját, `sorry`-mentes bizonyíték | (B) Mathlib-hozzájárulás / PR-jelölt | (B) státusz | (C) beküldött PR (✅ = merge-elve, ⬜ = nincs / nyitott) |
|---|---|---|---|---|
| T‑1 | **T:** `isLUB_sqrt_two`, `archimedean_real`; **H:** `exists_isLUB_of_bddAbove`, `isLUB_unique`, `irrational_sqrt_two'`, `rat_dense`, `irrational_dense` | `mathlib-prs/17-sInf-eq-top-dual.patch` (hiányzó duális a teljes hálókban) | patch kész; a mai masteren **elavult** (`@[to_dual]` generálja) → új jelölt: `Mathlib/Order/CompleteLattice/Basic.lean:115` TODO, `Mathlib/Data/Real/Sqrt.lean:112` TODO | ⬜ [#42339](https://github.com/leanprover-community/mathlib4/pull/42339) *(nyitott)* — diagonális `iSup`/`iInf` |
| T‑2 | **T:** `sum_odd_eq_sq` (szokásos indukció), `exists_prime_dvd_of_two_le` (erős indukció); **P:** `ex_1_13`, `ex_1_14a`–`c`, `ex_1_15a`–`d` | — (a Mathlib indukciós API-ja hiánytalan; nincs értelmes „javítanivaló”) | **nincs jelölt**; itt az (A) oszlop és a kézzel megoldott példatár a bizonyíték | ✅ [#42592](https://github.com/leanprover-community/mathlib4/pull/42592) · ✅ [#42763](https://github.com/leanprover-community/mathlib4/pull/42763) · ✅ [#42907](https://github.com/leanprover-community/mathlib4/pull/42907) · ⬜ [#42823](https://github.com/leanprover-community/mathlib4/pull/42823) *(nyitott)* |
| T‑3 | **T:** `abs_sum_le_sum_abs'`, `am_gm_three`; **H:** `cauchy_schwarz_sum`, `bernoulli_ineq`, `am_gm_two` | `11-holder-ennreal-flexible-linter.patch` (Hölder), `10-poslog-sum-flexible-linter.patch` | mindkettő kész; a masteren elavult → élő jelölt a bázison: `Mathlib/Analysis/MeanInequalities.lean:872` (`linter.flexible` kivétel) | ⬜ nincs beküldve (a fordított háromszög-egyenlőtlenség deduplikálása patch-ként kész) |
| T‑4 | **T:** `polynomial_continuous`, `rational_continuousAt`, `sqrt_inverse_on_nonneg`, `arctan_tan_inverse`; **H:** `exp_strictMono'`, `log_mul_eq`, `log_exp_inverse`; **P:** `ex_2_19` (gyökök száma ≤ fokszám) | `03-rpow-flexible-linter.patch`, `13-rpow-log-duplicates.patch`, `08-obsolete-flexible-exceptions.patch`, `master-2026-08/29-ruleofsigns-flexible.patch` (Descartes-féle előjelszabály) | `13` és `29` **érvényes** a mai masteren; `03`, `08` elavult. További jelöltek: `Pow/Real.lean:110`, `Pow/Real.lean:471`, `Pow/NNReal.lean:824`, `Log/PosLog.lean:161` | ⬜ [#42533](https://github.com/leanprover-community/mathlib4/pull/42533) *(nyitott)* — `log`/`rpow` duplikátumok |
| T‑5 | **T:** `range_sq`, `exists_inverse_iff_bijective`, `comp_injective_surjective`; **H:** `arcsin_left_inverse`, `bijective_cube`; **P:** `ex_2_11`, `ex_2_18` | `02-arccos-cos-flexible-linter.patch`, `master-2026-08/12-arg-periodic-dedup.patch` | `12` **érvényes**; `02` elavult → jelölt: `Trigonometric/Inverse.lean:293–294` (TODO + kivétel) | ⬜ nincs beküldve |
| T‑6 | **T:** `sq_symmetry_monotonicity`, `sin_periodic_odd`, `strictMono_injective'`; **H:** `cos_even_sin_odd`, `exists_unique_even_odd_decomp`, `strictMono_cube'` | jelölt: `Trigonometric/Complex.lean:84` (`linter.flexible` kivétel, „used to be field_simp”) | jelölt a bázison ellenőrizve | ⬜ nincs beküldve |
| T‑7 | **T:** `graph`, `graph_translate`, `graph_scale_shift`, `graph_reflect_y` | — (a grafikontranszformáció nem Mathlib-téma) | **nincs jelölt**; javasolt helyette a `Function.Periodic` / `Even`/`Odd` API kiegészítése | ⬜ nincs beküldve |
| T‑8 | **H:** `LimitAt`, `RightLimitAt`, `LeftLimitAt`, `limitAt_unique`, `limitAt_iff_tendsto`, `limitAt_iff_left_right` | jelölt: `Mathlib/Topology/Order/LeftRight.lean:67` TODO (féloldali szűrők `NeBot` instanciái szorzattereken) | jelölt a bázison ellenőrizve | ⬜ [#42499](https://github.com/leanprover-community/mathlib4/pull/42499) *(nyitott, gyenge kapcsolat)* |
| T‑9 | **H:** `limitAt_const`, `limitAt_id`, `limitAt_add`, `limitAt_mul`, `limitAt_div` | — | **nincs jelölt** (az alapműveleti API teljes) | ⬜ [#42499](https://github.com/leanprover-community/mathlib4/pull/42499) *(nyitott, gyenge kapcsolat)* |
| T‑10 | **H:** `limitAt_le_of_le`, `limitAt_squeeze`, `limit_x_mul_sin_inv`, `tendsto_of_monotone_bddAbove`, `one_add_inv_pow_monotone`, `tendsto_one_add_inv_pow_exp_one`; **D:** `limit_sin_div_x` | jelölt (**feat**): `Mathlib/Analysis/SpecialFunctions/Log/Monotone.lean:33` — a fájl TODO-ja szerint az állítás **élesíthető** (`exp (-1) ≤ x`-re) | jelölt a bázison ellenőrizve; ez „tartalmi”, nem kozmetikai hozzájárulás | ⬜ nincs beküldve |
| T‑11 | **H:** `ContinuousAtEps`, `continuousAtEps_iff`, `continuousAtEps_iff_limitAt`, `continuousAtEps_comp`, `continuousAtEps_add_mul`, `sign_jump_discontinuity` | jelölt: `Mathlib/Topology/Piecewise.lean:95` (`linter.flexible` kivétel — darabonként definiált függvények folytonossága) | jelölt a bázison ellenőrizve | ⬜ nincs beküldve |
| T‑12 | **H:** `bolzano`, `darboux`, `weierstrass`, `heine_uniform_continuity`; **P:** `ex_3_14`, `ex_3_15` | `14-darboux-docstring-mismatch.patch` (**hibás állítás javítása**) | **érvényes** a mai masteren is (újragenerálva) | ✅ [#42810](https://github.com/leanprover-community/mathlib4/pull/42810) — a `Darboux.lean` javítása *(közvetett)* |
| T‑13 | **T:** `tangentLine`, `hasDerivAt_iff_tangentLine`, `tangent_slope_unique`; **D:** `hasDerivAt_iff_limitAt_slope`, `hasDerivAt_iff_littleO`, `continuousAt_of_hasDerivAt`, `abs_continuous_not_differentiable`, `deriv_add_rule`, `deriv_mul_rule`, `deriv_div_rule`, `deriv_comp_rule`, `deriv_inverse_rule` | `14-darboux-docstring-mismatch.patch`, `24-expired-deprecations-calculus.patch` | `14` érvényes; `24` elavult (upstream automatizmus törli a lejárt aliasokat) | ✅ [#42810](https://github.com/leanprover-community/mathlib4/pull/42810) · ⬜ [#42583](https://github.com/leanprover-community/mathlib4/pull/42583) *(nyitott)* |
| T‑14 | **T:** `implicit_deriv_circle`; **D:** `deriv_comp_rule` (láncszabály), `deriv_inverse_rule` | jelöltek: `Analysis/Calculus/ContDiff/FaaDiBruno.lean:291` és `:340` (a magasabbrendű láncszabály két `linter.flexible` kivétele), `Analysis/Calculus/Implicit.lean:33` TODO-szakasz | jelöltek a bázison ellenőrizve | ⬜ nincs beküldve |
| T‑15 | **D:** `fermat_deriv_eq_zero`, `rolle`, `lagrange_mvt`, `cauchy_mvt`, `const_of_deriv_eq_zero`, `sub_const_of_deriv_eq` | jelölt: `Analysis/Calculus/MeanValue.lean:585` TODO (`IsLocallyConstantOn` bevezetése után átírandó állítás) | jelölt a bázison ellenőrizve | ⬜ nincs beküldve |
| T‑16 | **D:** `monotoneOn_of_deriv_nonneg'`, `strictMonoOn_of_deriv_pos'`; **T:** `cubic_strictMonoOn_Ici_one`, `cubic_strictAntiOn_Icc` | — | **nincs jelölt** | ✅ [#42810](https://github.com/leanprover-community/mathlib4/pull/42810) — **a derivált Darboux-tulajdonsága**, erős kapcsolat |
| T‑17 | **D:** `isLocalMin_of_deriv_sign` (első derivált teszt), `isLocalMin_of_deriv2_pos` (második derivált teszt); **T:** `cubic_local_extrema`; **P:** `ex_4_8_18` (intervallumon vett szélsőérték) | — | **nincs jelölt** | ⬜ nincs beküldve |
| T‑18 | **D:** `convexOn_of_deriv2_nonneg'`, `convexOn_chord`; **T:** `cubic_convexOn_Ici_zero`, `cubic_concaveOn_Iic_zero`, `cubic_inflection_zero`; **P:** `ex_4_13` (középponti konvexitás + folytonosság ⇒ konvexitás) | jelölt (**feat**): az `ex_4_13` állítás upstreamelése — a rögzített bázison az `Mathlib/Analysis/Convex/` alatt **nincs** középponti (midpoint) konvexitásról szóló tétel (ellenőrizve) | a legnagyobb tartalmi értékű jelölt ebben a tárgyban | ✅ [#42579](https://github.com/leanprover-community/mathlib4/pull/42579) — `Monotone.convex_lt`/`convex_gt` **hibás állítás** javítása, erős kapcsolat |
| T‑19 | **T:** `cubic`, `hasDerivAt_cubic`, `deriv_cubic`, `deriv2_cubic`, `cubic_strictMonoOn_Ici_one`, `cubic_strictAntiOn_Icc`, `cubic_local_extrema`, `cubic_inflection_zero`; **P:** `ex_4_10e` | — (teljes függvényvizsgálat nem Mathlib-műfaj) | **nincs jelölt**; itt az (A) oszlop a bizonyíték | ⬜ nincs beküldve |
| T‑20 | **D:** `lhospital_zero_right`, `limit_sin_div_x` | `01-lhopital-flexible-linter.patch` | patch kész; a mai masteren **elavult** (az upstream megszüntette a kivételt) → a bázison a `Analysis/Calculus/LHopital.lean:53–54` TODO+kivétel a hivatkozási pont | ⬜ nincs beküldve |

**Számszerű mérleg (tematika szerint).** 20 elemből **20-hoz** van saját, `sorry`-mentes,
gépileg ellenőrzött bizonyíték → **100 %**. Mathlib-hozzájárulás vagy ellenőrzött PR-jelölt
**14 elemhez** kapcsolható → **70 %**; ebből **kész, benyújtható patch** 7 elemhez tartozik → **35 %**
(T‑1, T‑3, T‑4, T‑5, T‑12, T‑13, T‑20).

**A (C) oszlop mérlege.** A szerzőnek összesen **18 nyilvános Mathlib PR-ja** van, ebből **6 merge-elve**
(✅), 9 nyitott és 3 merge nélkül lezárt (⬜). A 6 merge-eltből **5 kapcsolható** valamelyik Kalkulus I
tematikaelemhez (a [#42493](https://github.com/leanprover-community/mathlib4/pull/42493) csoportelméleti,
azon kívül esik), a nyitottakból szintén 5. Tematikaelem szinten: **✅ merge-elt PR fedi** a **T‑2, T‑12,
T‑13, T‑16, T‑18** pontokat (5 elem = 25 %), **⬜ nyitott PR** kapcsolódik a **T‑1, T‑4, T‑8, T‑9, T‑13**
pontokhoz. A legerősebb kettő: a **Darboux-PR** ([#42810](https://github.com/leanprover-community/mathlib4/pull/42810))
a T‑16-hoz, és a [#42579](https://github.com/leanprover-community/mathlib4/pull/42579) (hibás állítás
javítása) a T‑18-hoz.

---

## 2/b. A ténylegesen beküldött Mathlib PR-ok (a `pr-attekintes/` melléklet alapján)

Ez a szakasz **nem** patch-jelölteket sorol, hanem a szerző (`attilavjda`) **valódi, nyilvános
GitHub pull requestjeit**, mindegyiket a hozzá tartozó tematikaelemmel. A státusz a
2026‑08‑30‑i lekérdezésből származik; a merge-elteket a `master` git-történetében is
ellenőriztem (a Mathlibben `bors` merge-el, ezért a GitHub API `merged` mezője `false`,
a cím `[Merged by Bors]` előtaggal és a `master`-beli commit a bizonyíték).

### Merge-elt PR-ok — ✅

| ✔ | PR | Merge (master-commit) | Cím | Tematikaelem | Kapcsolat |
|---|---|---|---|---|---|
| ✅ | [#42810](https://github.com/leanprover-community/mathlib4/pull/42810) | 2026‑08‑18 (`e72c1e277`) | `fix(Analysis)`: two lemmas are copies of the one above them — **a Darboux-PR** (`Analysis/Calculus/Darboux.lean`, `Complex/UpperHalfPlane/Metric.lean`) | **T‑16** (monotonitás és derivált — a derivált Darboux-tulajdonsága), T‑12, T‑13 | **erős** |
| ✅ | [#42579](https://github.com/leanprover-community/mathlib4/pull/42579) | 2026‑08‑13 (`8fecc3d4d`) | `fix(Analysis/Convex/Basic)`: `Monotone.convex_lt`/`convex_gt` state the wrong set | **T‑18** (konvexitás) | **erős** — tartalmi hibajavítás |
| ✅ | [#42592](https://github.com/leanprover-community/mathlib4/pull/42592) | 2026‑08‑10 (`4a3cbc9c7`) | `chore(Algebra/BigOperators)`: generate `sum_Ico_reflect`/`sum_range_reflect` with `to_additive` | **T‑2** (teljes indukció, véges összegek: Gauss-összeg, binomiális azonosságok) | erős |
| ✅ | [#42763](https://github.com/leanprover-community/mathlib4/pull/42763) | 2026‑08‑15 (`bec97d68e`) | `chore(Algebra/BigOperators)`: add `to_additive` for expectation and antidiagonal lemmas | **T‑2** | közepes |
| ✅ | [#42907](https://github.com/leanprover-community/mathlib4/pull/42907) | 2026‑08‑18 (`4ac22c7ef`) | `chore(…/NatAntidiagonal)`: remove unused variable | **T‑2** | gyenge |
| ✅ | [#42493](https://github.com/leanprover-community/mathlib4/pull/42493) | 2026‑08‑10 (`3cf9c0a79`) | `chore(GroupTheory/Complement)`: deduplicate `IsComplement.card_mul` | *(Kalkulus I tematikán kívül; a Számítástudomány alapjai / algebra blokkhoz sorolható)* | — |

### Nyitott PR-ok — ⬜ (2026‑08‑30)

| ✔ | PR | Cím | Tematikaelem |
|---|---|---|---|
| ⬜ | [#42583](https://github.com/leanprover-community/mathlib4/pull/42583) | `chore(Analysis/Calculus/FDeriv/Prod)`: deprecate `differentiable*_finCons'` duplicates | **T‑13** (differenciálhatóság, deriválási szabályok) |
| ⬜ | [#42533](https://github.com/leanprover-community/mathlib4/pull/42533) | `chore(…/Pow/Real)`: deprecate six misnamed duplicate `log`/`rpow` lemmas | **T‑4** (elemi függvények) |
| ⬜ | [#42339](https://github.com/leanprover-community/mathlib4/pull/42339) | `feat`: add diagonal `iSup`/`iInf` lemmas | **T‑1** (szuprémum, teljességi axióma) |
| ⬜ | [#42499](https://github.com/leanprover-community/mathlib4/pull/42499) | `doc(Data/ENat,ENNReal)`: fix swapped docstring on `mul_iInf_of_ne` | T‑8, T‑9 (határérték, kiterjesztett értékkészlet) — gyenge |
| ⬜ | [#42509](https://github.com/leanprover-community/mathlib4/pull/42509) | `chore(Analysis/Normed/Lp/PiLp)`: fix stale docstring cross-references | *(tematikán kívül)* |
| ⬜ | [#42505](https://github.com/leanprover-community/mathlib4/pull/42505) | `chore(Algebra/Tropical/Basic)`: deduplicate five pairs of lemmas | *(tematikán kívül)* |
| ⬜ | [#42764](https://github.com/leanprover-community/mathlib4/pull/42764) | `chore(GroupTheory)`: make `smul_eq_self_of_mem_zpowers` `to_additive` | *(tematikán kívül)* |
| ⬜ | [#42823](https://github.com/leanprover-community/mathlib4/pull/42823) | `chore`: let `to_additive` generate hand-written additive twins | T‑2 (véges összegek API-ja) — gyenge |
| ⬜ | [#42082](https://github.com/leanprover-community/mathlib4/pull/42082) | `feat(FieldTheory)`: reduce Frobenius powers modulo the extension degree | *(tematikán kívül; testelmélet)* |

### Merge nélkül lezárt PR-ok — ⬜

| ✔ | PR | Cím | Mi történt |
|---|---|---|---|
| ⬜ | [#41973](https://github.com/leanprover-community/mathlib4/pull/41973) | `refactor(Order/CompleteLattice)`: extract diagonal `iSup` lemma | lezárva; a téma a #42339-ben él tovább |
| ⬜ | [#42399](https://github.com/leanprover-community/mathlib4/pull/42399) | `feat(order)`: add `ciSup₂` diagonal lemmas | lezárva; a téma a #42339-ben él tovább |
| ⬜ | [#42746](https://github.com/leanprover-community/mathlib4/pull/42746) | `chore(Algebra/BigOperators)`: add `to_additive` for antidiagonal succ and `expect_inv_index` | összevonva a #42763-ba (az **merge-elve**) |

**Összesítés:** 18 PR — **6 merge-elve ✅**, 9 nyitott ⬜, 3 merge nélkül lezárva ⬜.

A `pr-attekintes/` mappa (a mellékelt archívumból átemelve) tartalmazza a részletes,
LaTeX-forrású áttekintőt (`pr_attekintes.pdf`) és a ma is tisztán illeszkedő hat patch-et
(`pr-attekintes/patches/`), amelyekből további PR-ok készíthetők — ezek a **(B)** oszlop
„beküldésre kész” tételei, tehát a (C) oszlopban még ⬜.

---

## 3. Miért „high-leverage”? — hozzájárulás-típusok és bizonyító erejük

A kreditelismerésnél nem a diff mérete számít, hanem hogy **mit bizonyít rólad**. Csökkenő
sorrendben:

| # | Hozzájárulás-típus | Mit bizonyít | Példa a dossziéból | Nehézség |
|---|---|---|---|---|
| 1 | **Hibás állítás / dokumentáció-eltérés javítása** | matematikai megértés: észrevetted, hogy az állítás **nem azt mondja**, amit a docstring | `14-darboux-docstring-mismatch` (T‑12, T‑13) | közepes |
| 2 | **Hiányzó tétel pótlása (feat)** | önálló bizonyítási képesség; ez a legközelebb a „vizsgateljesítményhez” | `ex_4_13` upstreamelése (T‑18); `Log/Monotone.lean:33` élesítése (T‑10) | magas |
| 3 | **Bizonyítás átírása linter-kivétel megszüntetéséhez** | a bizonyítás lépéseinek pontos ismerete (a `simp` helyére *tudni kell*, mit írj) | `01` (T‑20), `11` (T‑3), FaaDiBruno (T‑14) | közepes |
| 4 | **Deduplikáció** | a tétel*család* átlátása: felismered, hogy két állítás ugyanaz | `13-rpow-log-duplicates` (T‑4) | alacsony–közepes |
| 5 | **Tiszta törlés / karbantartás** | fegyelmezett munkavégzés, CI-ismeret; matematikailag keveset bizonyít | `08`, `23`, `24`, `25` | alacsony |

**Gyakorlati következtetés.** A bizottság felé egyetlen 2. típusú (feat) hozzájárulás többet ér,
mint tíz 5. típusú. Ezért a **legfontosabb egyetlen lépés**: az `ex_4_13`
(középponti konvexitás + folytonosság ⇒ konvexitás) állítás benyújtása a Mathlibbe a T‑18 ponthoz,
és a `Log/Monotone.lean:33` TODO-ban jelzett élesítés a T‑10 ponthoz.

Amit **minden** PR ad, típustól függetlenül (a TVSZ 3. sz. melléklet 4.2. pontja szerint
mérlegelhető „számonkérési rendszer”):

* **gépi ellenőrzés** — a Lean típusellenőrzője hézagmentességet követel;
* **CI** — a Mathlib teljes újrafordítása + linterek;
* **maintaineri code review** — külső, szakértői bírálat;
* **időbélyeges, nyilvános nyom** — a PR-oldal örökre hivatkozható URL.

---

## 4. Pontonként: mit kell tenni a kreditátvételhez

A hivatkozott pontszámok az SZTE TVSZ 3. sz. mellékletére (kreditátviteli szabályzat) utalnak,
ahogy a `KREDITELISMERES.md` részletezi: **3.8.** = validáció nem felsőoktatásban szerzett
kompetenciák alapján; **4.1. b)** = a kredit nem tagadható meg, ha a tanulási eredmények **75 %-a**
teljesül; **4.2.** = a bizottság mérlegelheti a gyakorlást, a munkaidőt és a számonkérési rendszert;
**4.4.** = ugyanaz a kompetencia több tárgynál is felhasználható; **4.5.** = előzetes döntés kérhető.

| Kód | Mit csatolj a kérelemhez (bizonyíték) | Mi a gyenge pont, és mivel pótold |
|---|---|---|
| T‑1 | `isLUB_sqrt_two` + `KalkulusHatarertek` szuprémum-szakasz; a teljességi axióma és `ℚ` hiányosságának formalizált szembeállítása | a *konstrukció* (Dedekind-szeletek/Cauchy-sorozatok) nincs formalizálva → hivatkozz a Mathlib `Real` konstrukciójára, és készíts 1 oldalas kézírásos vázlatot |
| T‑2 | `sum_odd_eq_sq`, `exists_prime_dvd_of_two_le` + a `Portfolio/Kalkulus.lean` 1.13–1.15 feladatai; **✅ #42592, #42763, #42907** (merge-elt PR-ok a véges összegek API-jára) | nincs külső bírálat → ezt a pontot a *kollokviumi rutin* pótolja: 5–10 kézzel megoldott indukciós feladat |
| T‑3 | `cauchy_schwarz_sum`, `bernoulli_ineq`, `am_gm_two`, `am_gm_three`, `abs_sum_le_sum_abs'` + a Hölder-patch | egyenlőség-esetek elemzése hiányzik → érdemes egy `am_gm` egyenlőségi feltételt is formalizálni |
| T‑4 | `polynomial_continuous`, `rational_continuousAt`, `sqrt_inverse_on_nonneg`, `arctan_tan_inverse` + `13`, `29` patch | parciális törtekre bontás (integrálás előkészítése) nincs → nem része ennek a tematikának, de érdemes jelezni |
| T‑5 | `range_sq`, `exists_inverse_iff_bijective`, `comp_injective_surjective`, `arcsin_left_inverse` | konkrét értelmezési tartomány-számítások → példatár-megoldások |
| T‑6 | `sq_symmetry_monotonicity`, `sin_periodic_odd`, `exists_unique_even_odd_decomp` | kézi grafikonvázolás → rajzos megoldások szkennelve |
| T‑7 | `graph_translate`, `graph_scale_shift`, `graph_reflect_y` | — (ez a pont formalizálva erősebb, mint a szokásos számonkérés) |
| T‑8–T‑10 | a saját ε–δ `LimitAt` definíció és a rá épülő teljes tételcsalád (`H` modul) | „elemi határérték-számítási technikák” = rutin → 10–15 kiszámolt határérték a példatárból |
| T‑11–T‑12 | `ContinuousAtEps` + `bolzano`, `darboux`, `weierstrass`, `heine_uniform_continuity`, `14` patch; **✅ #42810** (a `Darboux.lean` javítása a Mathlibben) | — (ez a legerősebben lefedett blokk) |
| T‑13–T‑14 | `hasDerivAt_iff_tangentLine`, `tangent_slope_unique`, az öt deriválási szabály, `implicit_deriv_circle` | „elemi függvények deriváltja” táblázatszerű ismerete → a Mathlib `deriv`-lemmákra hivatkozz tételesen |
| T‑15–T‑17 | `rolle`, `lagrange_mvt`, `cauchy_mvt`, `isLocalMin_of_deriv_sign`, `isLocalMin_of_deriv2_pos`, `cubic_local_extrema`; **✅ #42810** (T‑16: a derivált Darboux-tulajdonsága) | zárt intervallumon vett abszolút szélsőérték keresése rutinból → `ex_4_8_18` + kézi példák |
| T‑18 | `convexOn_of_deriv2_nonneg'`, `convexOn_chord`, `cubic_inflection_zero`, `ex_4_13`; **✅ #42579** (merge-elt *tartalmi* hibajavítás a konvexitásban) | ha az `ex_4_13` PR bemegy, ez lesz a dosszié **legerősebb** eleme |
| T‑19 | a teljes `cubic`-vizsgálat (`T` modul) | egyetlen függvény → érdemes még 2–3 típust végigvinni (racionális törtfüggvény aszimptotákkal, `x·e^x`) |
| T‑20 | `lhospital_zero_right`, `limit_sin_div_x`, `01` patch | a `∞/∞` eset és a kritikus alkalmazási hibák → egy ellenpélda formalizálása jó kiegészítés |

---

## 5. Kereső-receptek: hogyan találsz **magad** PR-jelöltet egy tematikai ponthoz

A recept lényege: a tematikai pontot **Mathlib-könyvtárra** fordítod, majd a könyvtárban
karbantartási jelzőket keresel. A Mathlib-forrás a projektben a `lake` csomagmappában van
(`.lake/packages/mathlib`), vagy külön `git clone`-nal.

**Tematikai pont → Mathlib-könyvtár:**

| Tematikai pont | Könyvtár |
|---|---|
| T‑1 valós számtest | `Mathlib/Data/Real`, `Mathlib/Order/Bounds`, `Mathlib/Order/CompleteLattice` |
| T‑3 egyenlőtlenségek | `Mathlib/Analysis/MeanInequalities*.lean` |
| T‑4, T‑5 elemi függvények | `Mathlib/Analysis/SpecialFunctions/{Pow,Log,Trigonometric}` |
| T‑8–T‑10 határérték | `Mathlib/Order/Filter`, `Mathlib/Topology/Order` |
| T‑11–T‑12 folytonosság | `Mathlib/Topology/{Piecewise,Order/Compact}.lean`, `Mathlib/Topology/Algebra/Order` |
| T‑13–T‑17 derivált | `Mathlib/Analysis/Calculus/{Deriv,MeanValue,ContDiff,Implicit}` |
| T‑18 konvexitás | `Mathlib/Analysis/Convex` |
| T‑20 L'Hospital | `Mathlib/Analysis/Calculus/LHopital.lean` |

**A négy legjobb keresés** (a mappát cseréld a fenti táblázat szerint):

```bash
# 1. Linter-kivételek: itt a bizonyítást érdemben át kell írni — a legjobb közepes nehézségű jelölt
rg -n "set_option linter.flexible false" Mathlib/Analysis/Calculus

# 2. Karbantartói TODO-k: az upstream maga kéri a munkát
rg -n "^-- TODO|^## TODO" Mathlib/Analysis/SpecialFunctions

# 3. Duplikátumok: azonos állítás két néven (a `Duplicate` szkriptek a repóban is megvannak)
rg -n "^theorem|^lemma" Mathlib/Analysis/Convex | sed 's/.*: *//' | sort | uniq -d

# 4. Hiányzó duálisok / szimmetriák: van `sSup`-változat, de nincs `sInf`-változat stb.
rg -n "sSup_eq_bot" Mathlib/Order   # majd keress rá az `sInf`-párjára
```

Ha egy találatot megnéztél, a benyújtás előtti ellenőrzés:

```bash
git apply --check mathlib-prs/<patch>          # illeszkedik-e a mai masterre
lake build Mathlib.<Az.Érintett.Modul>          # lefordul-e
lake exe lint  # vagy a CI linterek                (nem hoz-e be új figyelmeztetést)
```

A repóban lévő saját segédszkriptek ugyanezt automatizálják:
`mathlib-scan/DuplicateStatements.lean`, `mathlib-scan/MissingDuals.lean`,
`mathlib-scan/UnusedHypotheses.lean` (futtatás: `lake env lean mathlib-scan/<fájl>`).

> **Fontos tapasztalat** (`MASTER-2026-08-STATUS.md`): a Mathlib két automatizmusa
> (`remove_deprecated_decls.yml`, `rm_set_option.yml`) a *könnyű* kategóriákat (lejárt
> deprecationök, feleslegessé vált `set_option`-ok) folyamatosan felszámolja. **Kézi munkának a
> tartalmi javítások maradnak** — ami a kreditelismerés szempontjából jó hír: pont azok a
> hozzájárulások bizonyítanak sokat, amelyeket az automatizmus nem tud elvégezni.

---

## 6. Ellenőrizhetőség (amit a bizottság le tud futtatni)

```bash
lake build                                  # a teljes portfólió lefordul
rg -n "sorry|admit" RequestProject/         # üres találat
```

A tematikához készült modul: `RequestProject/Kreditelismeres/KalkulusTematika.lean`
(Lean 4.28.0, Mathlib `v4.28.0`, pinned commit `8f9d9cff6bd728b17a24e163c9402775d9e6a365`).
A benne szereplő tételek csak a standard axiómákra (`propext`, `Classical.choice`, `Quot.sound`)
támaszkodnak — `#print axioms <tételnév>` paranccsal ellenőrizhető.

---

## 7. Amit ez a dokumentum **nem** állít

* A **(B)** oszlopról nem állítja, hogy merged: a `mathlib-prs/` és a `pr-attekintes/patches/`
  alatti diffek benyújtásra kész patchek, PR-szám nélkül. A **(C)** oszlop viszont **valódi,
  nyilvános PR-okat** sorol; ott a ✅ azt jelenti, hogy a PR bekerült a Mathlib `master` ágába
  (a 2/b. szakasz megadja a merge-commitot is), a ⬜ pedig azt, hogy nyitott, lezárt vagy be
  sem küldött.
* Nem állítja, hogy a felsorolt PR-jelöltek a **mai** masteren is élnek: a fájl+sorszám találatok a
  rögzített `8f9d9cf` bázisra vonatkoznak, benyújtás előtt újra kell ellenőrizni.
* Nem hivatalos állásfoglalás: a kérelmet a TTIK Kreditátviteli Bizottsága bírálja el, és a
  8. pont szerint az érdemjegyet is ő állapítja meg.
