# Kalkulus I (MBLK37E) tematika → **Mathlib 4.34 (mai master) PR‑jelöltek**

**Mit tartalmaz ez a fájl?** A `KalkulusIelőadás-3.pdf` tárgytematika **„Tantárgy tartalma”**
mezőjének **minden egyes elemét külön szakaszban**, és mindegyikhez **kizárólag a hozzá tartozó
Mathlib‑hozzájárulást (PR‑jelöltet)** — semmi mást. A jelöltek a **mai `master`‑re** vonatkoznak,
és mindegyik olyan típusú, amit a maintainerek „near‑unambiguously improvement”‑nek tekintenek
(a diff **elvesz** valamit: duplikációt, hibát, költséget), *és* **matematikailag az adott
tematikai pontot fedi le**.

**A vizsgált bázis (fontos, mert a sorszámok ehhez tartoznak):**

| | |
|---|---|
| upstream | `leanprover-community/mathlib4` |
| commit | `58e016c6f6c829b5f25b1a87a88f495f40e70aa7` |
| commit dátuma | 2026‑08‑29 |
| toolchain | `leanprover/lean4:v4.34.0-rc2` (ez a „4.34”) |
| a scan napja | 2026‑08‑29 |

**Őszinteség‑záradék.** Ebben a fájlban **nincs egyetlen merged PR‑szám sem**: nem nyújtottam be
PR‑t a nevedben. Amit adok, az **benyújtásra kész, gépileg ellenőrzött patch** (a
[`mathlib-prs/master-4.34/`](mathlib-prs/master-4.34/) mappában), illetve **fájl+sorszámmal
dokumentált jelölt**. Az „✅ fordítás‑ellenőrzött” azt jelenti: a patch alkalmazása után az érintett
fájl(oka)t `lake env lean`‑nel lefordítottam a fenti master‑commit ellen, hibaüzenet nélkül.

> **Figyelem a jelölésre.** Ebben a fájlban a **✅ = „kész, fordítás‑ellenőrzött patch”**, *nem*
> merge‑elt PR. A **ténylegesen beküldött és merge‑elt** pull requestek (köztük a **Darboux‑PR**,
> [#42810](https://github.com/leanprover-community/mathlib4/pull/42810)) tematikaelemenként a
> [`KALKULUS-TEMATIKA-PR-TABLAZAT.md`](KALKULUS-TEMATIKA-PR-TABLAZAT.md) **(C) oszlopában** és
> **2/b. szakaszában** találhatók; a részletes áttekintő a [`pr-attekintes/`](pr-attekintes/)
> mappában van. Ott a ✅ jelentése: **a PR bekerült a Mathlib `master` ágába**.

---

## 0. A hozzájárulás‑típusok, amiket kerestem

| Jel | Típus | Miért fogadják el szinte vita nélkül |
|---|---|---|
| **A** | hibás docstring / félrevezető név / a docstringnek ellentmondó állítás javítása | tiszta hibajavítás, nincs ízlésvita |
| **B** | maintainer által írt `TODO` végrehajtása | valaki már eldöntötte, hogy kell; csak a munka hiányzik |
| **C** | deduplikáció (két lemma egy általánosra visszavezetve) | nettó sorcsökkenés, API nem vész el |
| **D** | szimmetria‑hézag pótlása (`to_additive`/`to_dual` iker, hiányzó `_iff`, hiányzó duális) | a könyvtár konzisztenciáját növeli |
| **E** | **tiszta törlés**: lejárt `deprecated` aliasok, nem használt hipotézisek, felesleges `to_additive` argumentumok | nulla hozzáadott sor |
| **F** | átnevezés + hívóhelyek átvezetése (deprecation propagation) | mechanikus, jól bírálható |

**Fontos figyelmeztetés az „E” típusról.** Az upstreamben fut egy
`.github/workflows/remove_deprecated_decls.yml` nevű ütemezett munkafolyamat (minden hó 15‑én,
alapértelmezetten a „6 hónapnál régebbi” deprecationöket törli). Ezért a **lejárt aliasok törlését
a bot is elvégezheti** — ezek a patchek gyors, biztos „első PR”‑ek, de a bíráló bizottság előtt
kisebb a bizonyító erejük, mint az **A/B/C/D** típusúaknak. A dosszié erejét az utóbbiak adják:
**T‑9** (TODO végrehajtása + átnevezés + felesleges `to_additive` argumentumok törlése),
**T‑16** (két hibás docstring), **T‑18** (14 sor duplikált bizonyítás → 7 sor),
**T‑6** (négy hiányzó szimmetria‑lemma), **T‑12** (TODO végrehajtása: két hipotézis egyre cserélve),
**T‑17** (nem létező tételre hivatkozó docstring), **T‑19** és **T‑20** (hiányzó duális, ill. hiányzó
peremváltozat pótlása).

---

## 1. A „Tantárgy tartalma” elemekre bontva (T‑1 … T‑20)

> „A valós számtest. Teljes indukció. Nevezetes egyenlőtlenségek. Polinomok, racionális
> törtfüggvények, gyökös, trigonometrikus, exponenciális függvények és inverzeik. Értelmezési
> tartomány, értékkészlet, inverz függvény, összetétel. Grafikonok vázolása, szimmetria
> tulajdonságok, monotonitás. Elemi függvénytranszformációk. Függvények határértéke. A határérték
> formális tulajdonságai, műveletek. Elemi határérték‑számítási technikák. Folytonosság fogalma,
> formális tulajdonságai. Folytonos függvények tulajdonsága: középérték‑tétel, kompakt
> intervallumon folytonos függvények. Pontbeli derivált és érintőegyenes. Kapcsolat a
> folytonossággal, deriválási szabályok. Elemi függvények deriváltja. Láncszabály, implicit
> deriválás. Középérték‑tételek. Monotonitás és derivált kapcsolata. Lokális szélsőérték és
> derivált (első és második derivált teszt), intervallumon vett szélsőértékek. Konvexitás fogalma,
> kapcsolata a második deriválttal. Függvények grafikonjának vázolása. L'Hospital szabályok és
> alkalmazásaik.”

---

## T‑1 · A valós számtest

*Matematikai tartalom: teljességi axióma, `sSup`/`sInf`, felső/alsó korlátok.*

| Jelölt | Típus | Hely a mai masteren | Mit tesz a diff | Bizonyíték | Státusz |
|---|---|---|---|---|---|
| **T1‑a** | **E** | `Mathlib/Order/CompleteLattice/Basic.lean:317` | törli a lejárt `sInf_upperBounds_eq_csSup` aliast (2026‑02‑01, > 6 hónap) | `rg -w sInf_upperBounds_eq_csSup` → **0 hívóhely** az egész repóban | ✅ `mathlib-prs/master-4.34/T01-delete-expired-sInf-upperBounds-alias.patch` (2 sor törlés, fordítás‑ellenőrzött) |
| **T1‑b** | **D** | `Mathlib/Topology/Order/OrderClosed.lean:404` | a fájl saját megjegyzése: *„we're missing some to_dual tags for conditionally complete lattices”* — a hiányzó `@[to_dual]` címkék pótlása (sup ↔ inf szimmetria) | maintainer‑komment a forrásban | jelölt (nincs patch) |
| **T1‑c** | **B** | `Mathlib/Data/Real/Pointwise.lean:21` | a fájl `TODO`‑ja: az `a • sSup s` állítások általánosítása feltételesen teljes rendezésre | maintainer `TODO` | jelölt (nincs patch) |

---

## T‑2 · Teljes indukció

*Matematikai tartalom: `Nat` indukció, erős indukció, succ/pred‑archimédeszi rendezések
(az indukció rendezéselméleti általánosítása).*

| Jelölt | Típus | Hely | Mit tesz a diff | Bizonyíték | Státusz |
|---|---|---|---|---|---|
| **T2‑a** | **E** | `Mathlib/Order/SuccPred/Archimedean.lean:153–157, 196` | törli az 5 lejárt aliast (`succ_max`, `succ_min`, `pred_max`, `pred_min`, `StrictMono.not_bddBelow_range_of_isSuccArchimedean`; mind 2026‑02‑05) | mind az 5 névre **0 hívóhely** | ✅ `T02-delete-expired-succpred-aliases.patch` (10 sor törlés, fordítás‑ellenőrzött) |
| **T2‑b** | **D** | `Mathlib/Order/SuccPred/Basic.lean:632` | maintainer `TODO`: *„auto-generate all of these through `to_dual`”* — a kézzel írt pred‑ikrek helyettesítése generálttal (ez pontosan a `to_additive`/`to_dual` hídmunka) | maintainer `TODO` | jelölt (nincs patch) |

---

## T‑3 · Nevezetes egyenlőtlenségek

*Matematikai tartalom: Hölder, Minkowski, számtani–mértani közép, Cauchy–Schwarz.*

| Jelölt | Típus | Hely | Mit tesz a diff | Bizonyíték | Státusz |
|---|---|---|---|---|---|
| **T3‑a** | **E** | `Mathlib/Analysis/MeanInequalities.lean:741, 1015` | törli a lejárt `inner_le_Lp_mul_Lq_tsum'` és `inner_le_Lp_mul_Lq_of_nonneg'` aliasokat (2026‑02‑12) | mindkettőre **0 hívóhely** | ✅ `T03-delete-expired-holder-aliases.patch` (5 sor törlés, fordítás‑ellenőrzött) |
| **T3‑b** | **B** | `Mathlib/Analysis/MeanInequalities.lean:100–104` | a fájl `TODO`‑ja: *„each inequality `A ≤ B` should come with a theorem `A = B ↔ _`”* — az egyenlőségi esetek (`StrictConvexOn`‑nal) pótlása | maintainer `TODO` | jelölt (nincs patch) — ez a legtartalmasabb ebben a pontban |
| **T3‑c** | **B** | `Mathlib/Data/Real/ConjExponents.lean:33` | a fájl `TODO`‑ja: *„Eradicate the `1 / p` spelling in lemmas”* — a konjugált kitevők egységes írásmódja | maintainer `TODO` | jelölt (nincs patch) |

---

## T‑4 · Polinomok, racionális törtfüggvények, gyökös, trigonometrikus, exponenciális függvények és inverzeik

| Jelölt | Típus | Hely | Mit tesz a diff | Bizonyíték | Státusz |
|---|---|---|---|---|---|
| **T4‑a** | **E** | `Mathlib/Analysis/Polynomial/Basic.lean:41, 101, 173, 192, 201, 252, 333` | törli a 7 lejárt aliast a polinomok végtelenbeli viselkedéséről (`eventually_no_roots`, `div_tendsto_zero_of_degree_lt`, …; 2026‑02‑05) | mind a 7 névre **0 hívóhely** | ✅ `T04-delete-expired-polynomial-aliases.patch` (18 sor törlés, fordítás‑ellenőrzött) |
| **T4‑b** | **E** | `…/SpecialFunctions/Trigonometric/Deriv.lean:754, 761` | törli a `Complex.LogDeriv_exp` és `Real.LogDeriv_exp` lejárt aliasokat (rossz nagybetűs írásmód, 2026‑02‑05) | mindkettőre **0 hívóhely** | ✅ `T04-delete-expired-logDeriv-exp-aliases.patch` (4 sor törlés, fordítás‑ellenőrzött) |
| **T4‑c** | **B** | `…/SpecialFunctions/Pow/Real.lean:1114` | a fájl `TODO`‑ja: a `norm_num`‑szerű egyszerűsítés kiterjesztése `(-a) ^ (b/2)`, `(-a) ^ (b/3)` alakokra | maintainer `TODO` | jelölt (nincs patch) |

---

## T‑5 · Értelmezési tartomány, értékkészlet, inverz függvény, összetétel

| Jelölt | Típus | Hely | Mit tesz a diff | Bizonyíték | Státusz |
|---|---|---|---|---|---|
| **T5‑a** | **E** | `Mathlib/Logic/Function/Basic.lean:415, 421, 512` | törli a parciális inverzről szóló 3 elavult aliast (`isPartialInv_left`, `injective_of_isPartialInv`, `partialInv_of_injective`) | mindháromra **0 hívóhely** | ✅ `T05-delete-expired-partialInv-aliases.patch` (6 sor törlés, fordítás‑ellenőrzött) — **de a deprecation dátuma 2026‑03‑11, tehát a 6 hónapos küszöböt 2026‑09‑11‑én éri el; addig ne küldd be** |
| **T5‑b** | **E** | `Mathlib/Data/Set/Function.lean:400, 406, 410` | ugyanez a képhalmaz‑különbségről szóló 3 aliasra (`InjOn.image_diff`, …; 2026‑06‑03) | 0 hívóhely | jelölt; a küszöb 2026‑12‑03 |

---

## T‑6 · Grafikonok vázolása, szimmetria tulajdonságok, monotonitás

*Matematikai tartalom: páros/páratlan függvények, ezek zártsági tulajdonságai.*

| Jelölt | Típus | Hely | Mit tesz a diff | Bizonyíték | Státusz |
|---|---|---|---|---|---|
| **T6‑a** | **D** | `Mathlib/Algebra/Group/EvenFunction.lean` | pótolja a **hiányzó szimmetria‑lemmákat**: a fájlban van `Even.add` és `Odd.add`, de **nincs** `Even.neg`, `Odd.neg`, `Even.sub`, `Odd.sub` | `rg -w "Function.Even.sub"`, `rg -w "Function.Even.neg"` → **0 találat** | ✅ `T06-evenfunction-neg-sub-symmetry.patch` (4 új lemma, fordítás‑ellenőrzött) |

*(Ellenőriztem: az „páratlan ∘ páros = páros” eset **nem** hézag, azt a meglévő `Even.left_comp`
lefedi — ezért nem szerepel a patchben.)*

---

## T‑7 · Elemi függvénytranszformációk

*Matematikai tartalom: eltolás, nyújtás, tükrözés — Mathlibben `Function.Periodic` /
`Function.Antiperiodic` + `Function.Even/Odd`.*

| Jelölt | Típus | Hely | Mit tesz a diff | Bizonyíték | Státusz |
|---|---|---|---|---|---|
| **T7‑a** | **A** | `Mathlib/Algebra/Field/Periodic.lean:167` | **félrevezető név:** az `Antiperiodic.div_inv` állítása szó szerint a `Periodic.div_const` ikre (`f (x / a)`, periódus `c * a`), de más nevet visel; a patch átnevezi `Antiperiodic.div_const`‑re és `deprecated alias`‑t hagy | `rg -w div_inv Mathlib Archive Counterexamples MathlibTest` → **0 hívóhely** a deklaráción kívül; a párja `Periodic.div_const` ugyanabban a fájlban (`:72`) | ✅ `mathlib-prs/master-4.34/T07-rename-antiperiodic-div-inv-to-div-const.patch` (fordítás‑ellenőrzött) |
| **T7‑b** | **A + D** | `Mathlib/Algebra/Ring/Periodic.lean:104` | **félrevezető név:** a `Periodic.neg` **a periódust** negálja (`Periodic f c → Periodic f (-c)`), miközben a szomszédos lemmák neve `add_period` / `sub_period` (`:95`, `:107`). Javaslat: `Periodic.neg` → `Periodic.neg_period` (+ `deprecated alias`), és az így felszabaduló `neg` név a `Periodic.inv` (`Periodic f c → Periodic f⁻¹ c`) `to_additive`‑ikre | `rg -w "Periodic.neg"` → csak a deklaráció; `rg -w "Periodic.inv"` → **nincs ilyen lemma**, pedig `Periodic.mul` és `Periodic.div` létezik (`:57`, `:61`) | jelölt (nincs patch: előbb az átnevezésről érdemes Zulipon kérdezni, mert a `neg` név két jelentés között vándorol) |

---

## T‑8 · Függvények határértéke

*Matematikai tartalom: féloldali határértékek, intervallum‑környezetek.*

| Jelölt | Típus | Hely | Mit tesz a diff | Bizonyíték | Státusz |
|---|---|---|---|---|---|
| **T8‑a** | **E** | `Mathlib/Order/Interval/Set/LinearOrder.lean:169, 190, 204, 233, 258, 273, 288, 303` | törli a 8 lejárt, vesszős intervallum‑unió tételt (`Ioo_union_Ioi'`, `Ico_union_Ici'`, … 2026‑02‑22), amelyek helyét a `min`/`max`‑os általános alak vette át | mind a 8 névre **0 hívóhely** | ✅ `T08-delete-expired-interval-union-primed.patch` (32 sor törlés, fordítás‑ellenőrzött) |
| **T8‑b** | **B** | `Mathlib/Topology/Order/LeftRight.lean:60` | maintainer `TODO`: `NeBot (𝓝[<] x)` instanciák szorzat‑ és indexelt szorzat‑terekre | maintainer `TODO` | jelölt (nincs patch) |
| **T8‑c** | **B** | `Mathlib/Topology/Order/LeftRightLim.lean:30` | a fájl `TODO`‑ja: a monoton függvények bal/jobb határérték‑API‑jának `StrictMono`/`StrictAnti` változata | maintainer `TODO` | jelölt (nincs patch) |

---

## T‑9 · A határérték formális tulajdonságai, műveletek

*Matematikai tartalom: határértékek szorzata/összege, ezen belül a „véges · végtelenbe tartó”
esetek.*

| Jelölt | Típus | Hely | Mit tesz a diff | Bizonyíték | Státusz |
|---|---|---|---|---|---|
| **T9‑a** | **B + F + A + E** | `Mathlib/Topology/Order/LeftRightNhds.lean:402, 413, 421, 430` és `Mathlib/Topology/Algebra/Order/Field.lean:18, 43–45` | **végrehajtja a maintainer TODO‑ját**: átnevezi a `Filter.Tendsto.mul_atTop'`, `mul_atBot'`, `atTop_mul'`, `atBot_mul'` lemmákat a vesszőtlen alakra (a `to_additive` ikreik már így hívódnak: `add_atTop`, `atTop_add`), a belső hívóhelyeket átvezeti, `deprecated alias`‑okat hagy hátra, **törli a már teljesíthető TODO‑t**, és javítja a `Field.lean` modul‑docstringjét, amely eddig egy **nem létező** `Filter.Tendsto.mul_atTop`‑ra hivatkozott. Ráadásul a rename után a linter jelzi, hogy a 4 explicit `to_additive`‑argumentum (`add_atTop`, `add_atBot`, `atTop_add`, `atBot_add`) **feleslegessé vált** — a patch ezeket is törli | a TODO szövege a forrásban; `rg` szerint a vesszőtlen nevek eddig **nem léteztek**; a felesleges argumentumokat a `linter.translateGenerateName` jelezte a fordításkor | ✅ `T09-rename-tendsto-mul-atTop-discharge-todo.patch` (mindkét fájl fordítás‑ellenőrzött, figyelmeztetés nélkül) |

---

## T‑10 · Elemi határérték‑számítási technikák

*Matematikai tartalom: geometriai sor, `log`/`exp` monotonitási becslések, rendőrelv.*

| Jelölt | Típus | Hely | Mit tesz a diff | Bizonyíték | Státusz |
|---|---|---|---|---|---|
| **T10‑a** | **E** | `Mathlib/Analysis/SpecificLimits/Basic.lean:398` és `…/SpecialFunctions/Log/Monotone.lean:39–41` | törli a `tsum_geometric_nnreal` aliast (2026‑03‑18) és a `log_mul_self_monotoneOn` elavult tételt (2026‑04‑07), amelyeket a `NNReal.tsum_geometric`, ill. a `Real.mul_log_strictMonoOn` váltott ki | mindkettőre **0 hívóhely** | ✅ `T10-delete-expired-limit-aliases.patch` (6 sor törlés, fordítás‑ellenőrzött) — **küszöb: 2026‑09‑18, ill. 2026‑10‑07** |

---

## T‑11 · Folytonosság fogalma, formális tulajdonságai

| Jelölt | Típus | Hely | Mit tesz a diff | Bizonyíték | Státusz |
|---|---|---|---|---|---|
| **T11‑a** | **E + A** | `Mathlib/Topology/ContinuousOn.lean:894, 908` | törli a két lejárt, **elgépelt** nevű aliast (`continouousOn_union_iff_of_isClosed`, `continouousOn_union_iff_of_isOpen` — figyeld a fölösleges „ou”‑t; 2026‑02‑20) | mindkettőre **0 hívóhely** | ✅ `T11-delete-expired-continuousOn-typo-aliases.patch` (6 sor törlés, fordítás‑ellenőrzött) |

---

## T‑12 · Folytonos függvények tulajdonságai: középérték‑tétel, kompakt intervallumon folytonos függvények

| Jelölt | Típus | Hely | Mit tesz a diff | Bizonyíték | Státusz |
|---|---|---|---|---|---|
| **T12‑a** | **B + C** | `Mathlib/Topology/Order/Compact.lean:60` és `:65` | két egymást kiegészítő maintainer `TODO`: *„make it the definition”* (`CompactIccSpace.mk'` legyen maga a definíció) és *„drop one `'`”* (a `CompactIccSpace.mk''` átnevezése) — együtt egy deduplikáló + névtisztító PR | maintainer `TODO`‑k | jelölt (nincs patch) |
| **T12‑b** | **B + E** | `Mathlib/Topology/Order/Compact.lean:444` | **maintainer `TODO` végrehajtása:** *„we could assume `t ∈ 𝓝ˢ s` (a.k.a. `s ⊆ interior t`) instead of `s ⊆ t` and `IsOpen s`”*. A patch az `IsCompact.exists_isLocalMin_mem_open` / `…_isLocalMax_mem_open` **két hipotézisét egyre cseréli** (`hst : s ⊆ t` + `hs : IsOpen s` → `hst : t ∈ 𝓝ˢ s`), a név `…_mem_of_nhdsSet` lesz (a régi név `_open` tagja már nem igaz), törli a `TODO`‑t, és átvezeti az egyetlen hívóhelyet | maintainer `TODO`; `rg -w exists_isLocalMin_mem_open` → **1 hívóhely** (`Mathlib/Topology/MetricSpace/ProperSpace/Lemmas.lean:60`), az is átvezetve | ✅ `mathlib-prs/master-4.34/T12-generalize-exists-isLocalExtr-nhdsSet-discharge-todo.patch` (`lake build Mathlib.Topology.MetricSpace.ProperSpace.Lemmas` — 1265 job, hiba és linter‑figyelmeztetés nélkül) |

---

## T‑13 · Pontbeli derivált és érintőegyenes; kapcsolat a folytonossággal, deriválási szabályok

| Jelölt | Típus | Hely | Mit tesz a diff | Bizonyíték | Státusz |
|---|---|---|---|---|---|
| **T13‑a** | **E** | `Mathlib/Analysis/Calculus/Deriv/Basic.lean:319–322` | törli a lejárt `HasDerivAtFilter.isBigO_sub_rev` tételt, amelyet a `HasDerivAtFilter.isTheta_sub` váltott ki (2026‑02‑04) | **0 hívóhely** | ✅ `T13-delete-expired-isBigO-sub-rev.patch` (5 sor törlés, fordítás‑ellenőrzött) |

---

## T‑14 · Elemi függvények deriváltja; láncszabály, implicit deriválás

| Jelölt | Típus | Hely | Mit tesz a diff | Bizonyíték | Státusz |
|---|---|---|---|---|---|
| **T14‑a** | **E** | `Mathlib/Analysis/Calculus/Deriv/Comp.lean:78, 168` | törli a láncszabály két lejárt `_of_eq` változatát (`HasDerivAtFilter.scomp_of_eq`, `HasDerivAtFilter.comp_hasFDerivAtFilter_of_eq`; 2026‑02‑17) | mindkettőre **0 hívóhely** | ✅ `T14-delete-expired-deriv-comp-of-eq.patch` (15 sor törlés, fordítás‑ellenőrzött) |
| **T14‑b** | **B** | `Mathlib/Analysis/Calculus/Implicit.lean:34` | a fájl `TODO`‑szakasza az implicitfüggvény‑tétel hiányzó változatairól | maintainer `TODO` | jelölt (nincs patch) |
| **T14‑c** | **B** | `Mathlib/Analysis/Calculus/Deriv/Polynomial.lean:23` | a fájl `TODO`‑ja a polinomderiválás API‑járól | maintainer `TODO` | jelölt (nincs patch) |

---

## T‑15 · Középérték‑tételek

| Jelölt | Típus | Hely | Mit tesz a diff | Bizonyíték | Státusz |
|---|---|---|---|---|---|
| **T15‑a** | **E** | `Mathlib/Analysis/Complex/MeanValue.lean:80, 120` | törli a körátlag‑középértéktétel két lejárt aliasát (2026‑02‑11) | mindkettőre **0 hívóhely** | ✅ `T15-delete-expired-circleAverage-aliases.patch` (6 sor törlés, fordítás‑ellenőrzött) |
| **T15‑b** | **A + F** | `Mathlib/Analysis/Calculus/MeanValue.lean:46, 558, 565, 618, 751, 767` | **mathlib3‑ból ittmaradt `snake_case` nevek** a „nulla derivált ⇒ konstans” tételcsaládban: `is_const_of_fderivWithin_eq_zero`, `is_const_of_fderiv_eq_zero`, `IsOpen.is_const_of_fderiv_eq_zero`, `is_const_of_deriv_eq_zero`, `IsOpen.is_const_of_deriv_eq_zero`. A Mathlib‑konvenció szerint `isConst_…` a helyes; a PR: átnevezés + `deprecated alias` + a 3 külső hívóhely átvezetése (`Mathlib/NumberTheory/ZetaValues.lean:170`, `Mathlib/Analysis/Complex/Liouville.lean:94`, és a fájlon belüli hívások) | `rg -n "\bis_const" Mathlib` → 5 deklaráció + 3 külső hívóhely | jelölt (nincs patch) |
| **T15‑c** | **B** | `Mathlib/Analysis/Calculus/MeanValue.lean:585` | maintainer `TODO`: az állítás átírása, ha lesz `IsLocallyConstantOn` | maintainer `TODO` | jelölt (nincs patch) |

---

## T‑16 · Monotonitás és derivált kapcsolata

| Jelölt | Típus | Hely | Mit tesz a diff | Bizonyíték | Státusz |
|---|---|---|---|---|---|
| **T16‑a** | **A** | `Mathlib/Analysis/Calculus/Deriv/MeanValue.lean:462–464` és `471–472` | **két hibás docstring:** a `strictAntiOn_of_hasDerivWithinAt_neg` és a `strictAnti_of_hasDerivAt_neg` dokumentációja szó szerint azt állítja, hogy *„If `f'` is strictly positive, then `f` is a strictly monotone function”*, holott az állítás `f' < 0` ⇒ **szigorúan csökkenő**. A patch a docstringeket az állításhoz igazítja (copy‑paste hiba a szomszédos `strictMono…` lemmákból) | a docstring és a `theorem` állítása közvetlenül ellentmond egymásnak | ✅ `T16-strictAnti-docstring-fix.patch` (fordítás‑ellenőrzött) |

---

## T‑17 · Lokális szélsőérték és derivált (első és második derivált teszt), intervallumon vett szélsőértékek

| Jelölt | Típus | Hely | Mit tesz a diff | Bizonyíték | Státusz |
|---|---|---|---|---|---|
| **T17‑a** | **A** | `Mathlib/Analysis/Calculus/DerivativeTest.lean:35` | a modul „Main results” listája az `isLocalMin_of_deriv_Ioo`‑t *„The dual of `first_derivative_max`”*‑ként írja le, de **`first_derivative_max` nevű deklaráció nem létezik** a Mathlibben (a név csak ebben a kommentben fordul elő). A patch a tényleges duálisra (`isLocalMax_of_deriv_Ioo`) javítja | `rg -n "first_derivative_max" .` → **egyetlen találat: maga a komment** | ✅ `T17-derivativetest-stale-docref.patch` (fordítás‑ellenőrzött) |
| **T17‑b** | **A** | ugyanott, `:26–41` | ugyanennek a modulnak a „Main results” listája a fájlban lévő **20 `isMaxOn_*_of_deriv` / `isMinOn_*_of_deriv` lemmát meg sem említi** (Ioo/Ioc/Ico/Icc/Ioi/Ici/Iio/Iic/univ változatok) — a lista kiegészítése tiszta dokumentációjavítás | a fájl deklarációlistája vs. a docstring | jelölt (nincs patch) |

*Megjegyzés (negatív eredmény, hogy ne pazarolj rá időt): megvizsgáltam, hogy a 10 `isMinOn_*`
lemma levezethető‑e a `isMaxOn_*` párjából `f ↦ -f` helyettesítéssel — **igen, működik** (a
`-f`‑re alkalmazott max‑változat + `IsMaxOn.neg`, fordítással ellenőriztem egy mintán), **de
nem rövidít**: a jelenlegi bizonyítások is 3 sorosak. Ezért ez **nem** ajánlott PR, mert nem
csökkenti a sorszámot.*

---

## T‑18 · Konvexitás fogalma, kapcsolata a második deriválttal

| Jelölt | Típus | Hely | Mit tesz a diff | Bizonyíték | Státusz |
|---|---|---|---|---|---|
| **T18‑a** | **C** | `Mathlib/Analysis/Convex/Deriv.lean:246–259` | **deduplikáció:** a `concaveOn_of_hasDerivWithinAt2_nonpos` bizonyítása szó szerinti másolata a `convexOn_of_hasDerivWithinAt2_nonneg`‑ének (14 sor). A patch a konkáv változatot a konvexre vezeti vissza `f ↦ -f` helyettesítéssel (`ConvexOn.neg`): **14 sor → 7 sor**, az API változatlan | a két bizonyítás karakterre azonos, csak `convex`↔`concave`, `nonneg`↔`nonpos` | ✅ `T18-dedup-concaveOn-hasDerivWithinAt2.patch` (fordítás‑ellenőrzött) |
| **T18‑b** | **B** | `Mathlib/Analysis/Convex/SpecificFunctions/Deriv.lean:27` | a fájl `TODO`‑ja: a második deriválttal bizonyított konvexitási lemmák egy részének elemi bizonyításra cserélése | maintainer `TODO` | jelölt (nincs patch) |

---

## T‑19 · Függvények grafikonjának vázolása

*Matematikai tartalom: teljes függvényvizsgálat — monotonitás, szélsőérték, konvexitás,
**inflexiós pont**.*

| Jelölt | Típus | Hely | Mit tesz a diff | Bizonyíték | Státusz |
|---|---|---|---|---|---|
| **T19‑a** | (hiányzó fogalom) | az egész könyvtár | **A Mathlibben nincs „inflexiós pont” fogalom**: az `IsLocalMin`/`IsLocalMax` megvan, de az inflexiós ponthoz nincs sem definíció, sem tétel. A természetes hozzájárulás egy `IsInflectionPoint` definíció + a második derivált előjelváltásához kötő tétel | `rg -ni "inflection" Mathlib` → **0 találat** | jelölt; **nem** „törlős” típusú, ezért nehezebben bírálható — előbb Zulip‑egyeztetés ajánlott |
| **T19‑b** | **D** | `Mathlib/Analysis/Convex/Deriv.lean:950` | **szimmetria‑hézag:** a `ConvexOn` névtérben megvan a három „kritikus pont ⇒ szélsőérték” lemma (`isMinOn_of_leftDeriv_nonpos_of_rightDeriv_nonneg`, `isMinOn_of_rightDeriv_eq_zero`, `isMinOn_of_leftDeriv_eq_zero`), a `ConcaveOn` duálisai viszont **teljesen hiányoznak**; a patch pótolja mindhármat, mindegyiket a meglévő konvex változatból `hf.neg`‑gel (ugyanaz a minta, mint a szomszédos `ConcaveOn.antitoneOn_deriv`‑nél) | `rg -w isMaxOn Mathlib/Analysis/Convex/Deriv.lean` → **0 találat** a teljes fájlban | ✅ `mathlib-prs/master-4.34/T19-concaveOn-isMaxOn-deriv-duals.patch` (fordítás‑ellenőrzött) |
| **T19‑c** | **A** | lásd **T17‑b** | a `DerivativeTest.lean` „Main results” listájának kiegészítése (ez fedi le a grafikonvázoláshoz használt szélsőérték‑lemmákat) | — | jelölt |

---

## T‑20 · L'Hospital‑szabályok és alkalmazásaik

| Jelölt | Típus | Hely | Mit tesz a diff | Bizonyíték | Státusz |
|---|---|---|---|---|---|
| **T20‑a** | **D** | `Mathlib/Analysis/Calculus/LHopital.lean:215` | **szimmetria‑hézag:** a `HasDerivAt` névtérben mind a négy peremváltozat megvan (`right_on_Ioo`, `right_on_Ico`, `left_on_Ioo`, `left_on_Ioc`), a `deriv` névtérből viszont **hiányzik a `lhopital_zero_left_on_Ioc`** (a `right_on_Ico` tükrös párja); a patch pótolja, szó szerint a `right_on_Ico` bizonyításának mintájára | `rg -n "^theorem" Mathlib/Analysis/Calculus/LHopital.lean`: `HasDerivAt` = 6 intervallumos tétel, `deriv` = 5 | ✅ `mathlib-prs/master-4.34/T20-deriv-lhopital-zero-left-on-Ioc-symmetry.patch` (fordítás‑ellenőrzött) |
| **T20‑b** | **D** | `Mathlib/Analysis/Calculus/LHopital.lean` (a fájl mind a 26 tétele) | **szimmetria‑hézag:** a Mathlibben **csak a `0/0` alak** van meg (minden tétel neve `lhopital_zero_…`), a **`∞/∞` alak teljesen hiányzik**. A pótlása a tematika „L'Hospital‑szabályok” pontjának azt a felét fedi le, amit a könyvtár ma nem tud | `rg -n "lhopital" Mathlib` → egyetlen fájl, minden tétel `…_zero_…` | jelölt; ez **feat** (nem törlés), tehát nagyobb munka, de matematikailag ez a legértékesebb hiány ebben a pontban |

---

## 2. Összesítő

| | darab |
|---|---|
| tematikai elem | 20 |
| olyan elem, amelyhez van **legalább egy** konkrét, mai masteren ellenőrzött PR‑jelölt | **20** |
| olyan elem, amelyhez van **kész, fordítás‑ellenőrzött patch** | **20** (mind) |
| patch nélküli (csak dokumentált jelölt) | **0** |
| kész patch összesen | **21 fájl** a `mathlib-prs/master-4.34/` mappában |
| ezekből tiszta törlés (0 hozzáadott sor) | **12** |

Patch‑lista (a fájlnév eleje mutatja, melyik tematikai ponthoz tartozik):

```
T01-delete-expired-sInf-upperBounds-alias.patch
T02-delete-expired-succpred-aliases.patch
T03-delete-expired-holder-aliases.patch
T04-delete-expired-polynomial-aliases.patch
T04-delete-expired-logDeriv-exp-aliases.patch
T05-delete-expired-partialInv-aliases.patch      (2026-09-11 után küldhető)
T06-evenfunction-neg-sub-symmetry.patch
T07-rename-antiperiodic-div-inv-to-div-const.patch
T08-delete-expired-interval-union-primed.patch
T09-rename-tendsto-mul-atTop-discharge-todo.patch
T10-delete-expired-limit-aliases.patch           (2026-09-18 / 2026-10-07 után küldhető)
T11-delete-expired-continuousOn-typo-aliases.patch
T12-generalize-exists-isLocalExtr-nhdsSet-discharge-todo.patch
T13-delete-expired-isBigO-sub-rev.patch
T14-delete-expired-deriv-comp-of-eq.patch
T15-delete-expired-circleAverage-aliases.patch
T16-strictAnti-docstring-fix.patch
T17-derivativetest-stale-docref.patch
T18-dedup-concaveOn-hasDerivWithinAt2.patch
T19-concaveOn-isMaxOn-deriv-duals.patch
T20-deriv-lhopital-zero-left-on-Ioc-symmetry.patch
```

## 3. Hogyan használd (reprodukálás és benyújtás)

```bash
git clone https://github.com/leanprover-community/mathlib4.git && cd mathlib4
git checkout 58e016c6f6c829b5f25b1a87a88f495f40e70aa7   # vagy: git pull origin master
lake exe cache get
git apply /útvonal/mathlib-prs/master-4.34/T16-strictAnti-docstring-fix.patch
lake build Mathlib.Analysis.Calculus.Deriv.MeanValue        # a patchhez tartozó modul
```

Benyújtás előtt mindig:

1. `git pull origin master`, majd a patch újraalkalmazása (a sorszámok elcsúszhatnak);
2. a **teljes** build (`lake build`) — a törlős patcheknél ez ellenőrzi, hogy tényleg nincs
   hívóhely (én a hívóhelyeket `rg`‑vel ellenőriztem, a *módosított* fájlokat pedig lefordítottam,
   de az egész Mathlib fordítását nem futtattam le mind a 21 patchre);
3. egy PR = egy téma, a PR címe konvenció szerint `chore: …` (törlés/deprecation), `fix: …`
   (docstring), `refactor: …` (dedup), `feat: …` (új lemma);
4. a törlős patcheknél érdemes megnézni, hogy a havi
   `remove_deprecated_decls.yml` bot nem előzött‑e meg.
