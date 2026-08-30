# Mathlib PR-javaslatok — bizonyítékcsomag a Kalkulus I és Lineáris algebra I kreditelismerési kérelemhez

Ez a dokumentum nyolc **konkrét, lefordított és ellenőrzött** Mathlib-javítást ír le,
amelyeket be lehet nyújtani a [leanprover-community/mathlib4](https://github.com/leanprover-community/mathlib4)
projektbe. Mindegyikhez tartozik egy kész `.patch` fájl a `mathlib-prs/` könyvtárban.

**Alapverzió (pinned commit):** `8f9d9cff6bd728b17a24e163c9402775d9e6a365` (2026-02-16)
**Toolchain:** Lean 4.28.0

> Fontos: a PR benyújtása előtt a patcheket a Mathlib **aktuális `master`** ágára kell újraalkalmazni,
> és a sorszámok/kontextus eltérhet. A `git apply -3` általában elvégzi az illesztést.

> **2026-08-29-i frissítés.** Az itt leírt 25 javaslatot végigellenőriztem a Mathlib **mai
> master**-ágán (`bbcd196`, Lean `v4.34.0-rc2`): 11 változatlanul érvényes, 2 átdolgozva érvényes,
> 12 időközben elavult (az upstream megoldotta), és készült **4 új** javaslat.
> A részletes állapotjelentés: [`mathlib-prs/MASTER-2026-08-STATUS.md`](mathlib-prs/MASTER-2026-08-STATUS.md),
> a mai masterre illeszkedő, lefordított patchek: `mathlib-prs/master-2026-08/`.
> **Benyújtás előtt ezt a könyvtárat használd, ne az eredeti, v4.28.0-hoz készült diffeket.**

---

## 0. Hogyan bizonyítanak ezek a hozzájárulások tanulási eredményt?

A kreditelismerési kérelemben nem korábbi kurzus, hanem **informális úton megszerzett tudás**
kerül hivatkozásra. Egy ilyen kérelemnél az elbírálás mindig **tanulási eredmény alapú**:
azt kell hihetővé és ellenőrizhetővé tenni, hogy a tárgy tematikájának egyes pontjaihoz
tartozó ismereteket és készségeket a hallgató ténylegesen birtokolja.

Egy összevont Mathlib-hozzájárulás ehhez négy dolgot ad, amit egy házi feladat nem:

1. **Külső, független bírálat.** A PR-t a Mathlib maintainerei nézik át és hagyják jóvá.
   A `merged` státusz olyan harmadik féltől származó igazolás, amely nem a hallgató saját állítása.
2. **Nyilvános, időbélyeggel ellátott, visszakereshető nyom.** A GitHub PR-oldal, a review-beszélgetés
   és a commit örökre hivatkozható URL — ez a melléklet „dokumentált" volta.
3. **Tárgyhoz köthető tartalom.** Minden alábbi PR olyan Mathlib-fájlt érint, amely a
   Kalkulus I tételsor vagy a Lineáris algebra I tematika egy konkrét pontjához tartozik
   (lásd az egyes PR-oknál a *Tematikai megfeleltetés* sort).
4. **Igazolt formális pontosság.** Egy Lean-bizonyítás átírása csak akkor fordul le, ha a
   matematikai érvelés hézagmentes. A `lake build` kimenete objektív ellenőrzés.

**Amit ez önmagában nem pótol.** A hozzájárulások a *mélységet* és a *hitelességet* igazolják,
de nem fedik le automatikusan a teljes tematikát. Ezért a dossziét célszerű két lábon állítani:

- **(A) tematikai lefedettség**: a repository `RequestProject/Kreditelismeres/` könyvtárában
  található Lean-fájlok, amelyek a Kalkulus I tételsor 1–17. pontját saját, ellenőrzött
  bizonyításokkal tartalmazzák (ε–δ határértékelmélet, Bolzano, Weierstrass, Heine,
  differenciálási szabályok, Rolle, Lagrange, Cauchy, monotonitás, konvexitás, L'Hospital),
  valamint a Lineáris algebra I tematika állításvázlatai;
- **(B) külső validáció**: az alábbi Mathlib PR-ok.

Az (A) mutatja meg, hogy *minden* tematikai pont ismert; a (B) mutatja meg, hogy a tudás
**külső, szakmai közösség által is elfogadott** szinten van.

### Javasolt megfogalmazás a kérelem indoklásába (minta)

> A Kalkulus I és Lineáris algebra I tárgyak tanulási eredményeit informális úton,
> a Lean 4 tételbizonyító rendszer és a Mathlib matematikai könyvtár keretében végzett
> önálló munkával sajátítottam el. A kérelemhez mellékelem
> (1) a tárgyak tematikájának pontjait lefedő, gépileg ellenőrzött formális bizonyításaimat, és
> (2) a Mathlib könyvtárba benyújtott, a tematikához közvetlenül kapcsolódó
> hozzájárulásaimat (lásd a mellékelt táblázatot a PR-hivatkozásokkal).
> A formális bizonyítás természeténél fogva nem enged meg hézagot: a mellékelt állítások
> mindegyike a Lean fordítója által ellenőrzött.

### Mit érdemes csatolni PR-onként

| Melléklet | Miért |
|---|---|
| PR URL + cím | azonosítás |
| státusz (`open` / `merged`) és dátum | időbeliség |
| a diff (a `mathlib-prs/*.patch` fájl) | tartalom |
| a `lake build` parancs és kimenete | ellenőrizhetőség |
| 2–4 mondat: melyik tematikai pont és miért | tanulási eredmény kötése |

---

## 1. A nyolc előkészített hozzájárulás

Rövidítés: **K‑n** = Kalkulus I tételsor n. pontja; **L‑x** = Lineáris algebra I tematika blokk.

| # | Patch | Érintett deklaráció | Kategória | Tematikai megfeleltetés |
|---|---|---|---|---|
| 1 | `01-lhopital-flexible-linter.patch` | `HasDerivAt.lhopital_zero_right_on_Ioo` | maintainer-TODO + linter-kivétel megszüntetése | K‑17 (L'Hospital-szabály) |
| 2 | `02-arccos-cos-flexible-linter.patch` | `Real.arccos_cos` | maintainer-TODO + linter-kivétel megszüntetése | K‑5 (arkuszfüggvények) |
| 3 | `03-rpow-flexible-linter.patch` | `Real.rpow_def_of_nonpos`, `Real.mul_rpow` | maintainer-TODO + linter-kivétel megszüntetése | K‑4 (hatvány-, exponenciális függvény) |
| 4 | `04-cos-eq-cos-iff-flexible-linter.patch` | `Complex.cos_eq_cos_iff` | linter-kivétel megszüntetése + felesleges `simp`-argumentum törlése | L‑1 (komplex számok, trigonometrikus alak) |
| 5 | `05-charpoly-inv-flexible-linter.patch` | `Matrix.charpoly_inv` | linter-kivétel megszüntetése | L‑6 (determinánsok, karakterisztikus polinom) |
| 6 | `06-trace-units-conj-docprime.patch` | `Matrix.trace_units_conj'` | elavult linter-kivétel + hiányzó dokumentáció | L‑5 (mátrixműveletek, inverz, konjugálás) |
| 7 | `07-toMatrix-dualTensorHom-flexible-linter.patch` | `toMatrix_dualTensorHom` | linter-kivétel + két felesleges `simp`-argumentum törlése | L‑5 (lineáris leképezés mátrixa) |
| 8 | `08-obsolete-flexible-exceptions.patch` | `ENNReal.rpow_le_rpow_of_exponent_ge`, `CliffordAlgebra.induction` | **tiszta törlés**: elavult linter-kivételek | K‑4 / L‑8 |

Minden patch **igazoltan lefordul**; az ellenőrző parancsok alább, PR-onként.

---

### PR 1 — `fix: non-terminal simp in HasDerivAt.lhopital_zero_right_on_Ioo`

- **Fájl:** `Mathlib/Analysis/Calculus/LHopital.lean` (a `8f9d9cf` commitban az 53. sor környéke)
- **Mi a baj:** a fájl egy maintainer-TODO-t hordoz — *"TODO: fix non-terminal simp (acting on
  three goals, with different simp sets)"* — és emiatt `set_option linter.flexible false in`
  kikapcsolja a `flexible` lintert az egész tételre.
- **A javítás:** a záró `refine … ?_ ?_ ?_` + `all_goals (… simp; linarith)` blokk helyett egyetlen
  lezáró termre cseréltem. A három részcél (`a ≤ c x`, `c x ≤ id x`, `c x ∈ Ioi a`) közvetlenül
  adódik a `cmp x hx : a < c x ∧ c x < x` konjunkció két tagjából.
- **Törölt sorok:** a TODO-komment és a `set_option` sor.
- **Ellenőrzés:**
  ```
  lake build Mathlib.Analysis.Calculus.LHopital
  ```
  → `Build completed successfully`, flexible-figyelmeztetés nélkül.
- **Kockázat:** alacsony. Az állítás betűre változatlan; csak a bizonyítás belseje módosul.
- **Tematikai megfeleltetés (K‑17):** a L'Hospital-szabály a Kalkulus I tételsor 17. pontja.
  A javítás megértéséhez pontosan azt kell látni, miért teljesülnek a szabály feltételei a
  jobb oldali környezeten — ez a tétel bizonyításának lényegi lépése.

### PR 2 — `fix: non-terminal simp in Real.arccos_cos`

- **Fájl:** `Mathlib/Analysis/SpecialFunctions/Trigonometric/Inverse.lean` (~294. sor)
- **Mi a baj:** ugyanaz a TODO és `set_option linter.flexible false in`; a bizonyítás
  `rw [...] <;> simp [sub_eq_add_neg] <;> linarith` alakú.
- **A javítás:**
  ```lean
  theorem arccos_cos {x : ℝ} (hx₁ : 0 ≤ x) (hx₂ : x ≤ π) : arccos (cos x) = x := by
    rw [arccos, ← sin_pi_div_two_sub, arcsin_sin (by linarith) (by linarith)]
    ring
  ```
  Az `arcsin_sin` mellékfeltételeit (`-π/2 ≤ π/2 - x ≤ π/2`) helyben, `linarith`-tal adjuk meg,
  így a `simp` teljesen elhagyható.
- **Ellenőrzés:** `lake build Mathlib.Analysis.SpecialFunctions.Trigonometric.Inverse` → sikeres.
- **Tematikai megfeleltetés (K‑5):** az arkuszfüggvények értelmezése és a
  `arccos (cos x) = x` azonosság érvényességi tartománya.

### PR 3 — `fix: non-terminal simp in Real.rpow_def_of_nonpos and Real.mul_rpow`

- **Fájl:** `Mathlib/Analysis/SpecialFunctions/Pow/Real.lean` (~110. és ~471. sor)
- **Mi a baj:** két TODO + két `set_option linter.flexible false in`.
- **A javítás:**
  - `rpow_def_of_nonpos`: a `split_ifs with h <;> simp [rpow_def, *]; exact …` helyett
    a három ág külön, lezárt bizonyítást kap.
  - `mul_rpow`: az `iterate 2 rw [...]; split_ifs <;> simp_all` + `all_goals positivity`
    helyett a bizonyítás a matematikai esetszétválasztást követi:
    `x = 0`, `y = 0`, illetve `0 < x, 0 < y`; az utolsó ág egyetlen `rw`-lánc
    (`rpow_def_of_pos`, `log_mul`, `add_mul`, `exp_add`).
- **Ellenőrzés:** `lake build Mathlib.Analysis.SpecialFunctions.Pow.Real` → sikeres.
- **Tematikai megfeleltetés (K‑4):** a hatványfüggvény definíciója `exp` és `log` segítségével,
  és az `(xy)^z = x^z y^z` azonosság — pontosan a tételsor 4. pontja.

### PR 4 — `fix: non-terminal simp in Complex.cos_eq_cos_iff`

- **Fájl:** `Mathlib/Analysis/SpecialFunctions/Trigonometric/Complex.lean` (~84. sor)
- **Mi a baj:** `set_option linter.flexible false in -- Non-terminal simp, used to be field_simp`.
- **A javítás:** `apply or_congr <;> simp [...]` helyett `refine or_congr ?_ ?_`, majd
  a két ág külön kezelése. Az első ágban a `sin z = 0 ↔ ∃ k : ℤ, z = k * π` átírás után
  a két irány `linear_combination`-nel zárul (a két irány más együtthatót igényel,
  ezért nem lehet őket `<;>`-vel összevonni). A második ág egyetlen lezáró `simp`.
  **Bónusz:** a `sub_eq_iff_eq_add` simp-argumentum feleslegesnek bizonyult, ez is törlődik.
- **Ellenőrzés:** `lake build Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex` → sikeres.
- **Tematikai megfeleltetés (L‑1):** komplex számok trigonometrikus alakja, a
  `cos x = cos y` megoldáshalmaza `2kπ ± x` alakban — az egységgyökök tárgyalásának alapja.

### PR 5 — `fix: non-terminal simp in Matrix.charpoly_inv`

- **Fájl:** `Mathlib/LinearAlgebra/Matrix/Charpoly/Coeff.lean` (~310. sor)
- **Mi a baj:** `set_option linter.flexible false in -- simp followed by ac_rfl`.
- **A javítás:** a `simp [charpolyRev, smul_eq_diagonal_mul]; ac_rfl` helyett
  `simp [charpolyRev, smul_eq_diagonal_mul, mul_assoc, mul_left_comm]` — a `simp`
  maga végzi el az asszociatív/kommutatív átrendezést, így terminális lesz.
- **Ellenőrzés:** `lake build Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff` → sikeres.
- **Tematikai megfeleltetés (L‑6):** determinánsok, szorzástétel, inverz mátrix determinánsa.

### PR 6 — `chore: document Matrix.trace_units_conj' and drop docPrime exception`

- **Fájl:** `Mathlib/LinearAlgebra/Matrix/Trace.lean` (~193–201. sor)
- **Mi a baj:** `set_option linter.docPrime false in` kikapcsolja a `docPrime` lintert
  a `trace_units_conj'` tételen, mert a vesszős névhez nem tartozik dokumentáció.
- **A javítás:** a kivétel törlése és rendes dokumentációs komment megadása
  (a `trace_units_conj` bal oldali inverzes változata).
- **Ellenőrzés:** `lake build Mathlib.LinearAlgebra.Matrix.Trace` → sikeres.
- **Megjegyzés:** a `docPrime` linter jelenleg nincs a `mathlibStandardSet`-ben
  (l. mathlib4#20560), tehát a kivétel amúgy is hatástalan; a dokumentáció pótlása
  teszi a törlést jövőbiztossá. Ezt érdemes a PR leírásában is jelezni.
- **Tematikai megfeleltetés (L‑5):** mátrixműveletek, invertálható mátrixok, konjugálás,
  nyom (trace) invarianciája.

### PR 7 — `fix: non-terminal simp in toMatrix_dualTensorHom`

- **Fájl:** `Mathlib/LinearAlgebra/Contraction.lean` (~115. sor)
- **Mi a baj:** TODO + `set_option linter.flexible false in`; a `by_cases … <;> simp [...]`
  után `rw … at hij` következik, ami pont a linter által kifogásolt minta.
- **A javítás:** a `by_cases` két ága külön bulletbe kerül; a negatív ágban a
  `rw [and_iff_not_or_not, Classical.not_not] at hij` a `simp` **elé** kerül,
  így mindkét `simp` terminális.
  **Bónusz:** így a `Finsupp.single_eq_pi_single` simp-argumentum feleslegessé válik, törölhető.
- **Ellenőrzés:** `lake build Mathlib.LinearAlgebra.Contraction` → sikeres.
  Kontrollteszt: az eredeti bizonyítás a `set_option` nélkül valóban figyelmeztetést ad
  (`'simp [...]' is a flexible tactic modifying '⊢'`), az átírt nem — tehát a javítás valódi.
- **Tematikai megfeleltetés (L‑5):** lineáris leképezés mátrixa bázispárban;
  a bázisbeli mátrix elemei (egyetlen 1-es, máshol 0).

### PR 8 — `chore: remove obsolete flexible linter exceptions` *(tiszta törlés)*

- **Fájlok:**
  - `Mathlib/Analysis/SpecialFunctions/Pow/NNReal.lean` (~823. sor,
    `ENNReal.rpow_le_rpow_of_exponent_ge`)
  - `Mathlib/LinearAlgebra/CliffordAlgebra/Basic.lean` (~175. sor, `CliffordAlgebra.induction`)
- **Mi a baj:** mindkét helyen van egy TODO-komment és egy `set_option linter.flexible false in`,
  amelyre **már nincs szükség**: a bizonyítások időközben úgy változtak, hogy a linter
  bekapcsolva sem panaszkodik.
- **A javítás:** a négy sor törlése. A diff csak töröl, semmit nem ad hozzá.
- **Ellenőrzés:**
  ```
  lake build Mathlib.Analysis.SpecialFunctions.Pow.NNReal
  lake build Mathlib.LinearAlgebra.CliffordAlgebra.Basic
  ```
  → mindkettő sikeres, flexible-figyelmeztetés nélkül.
- **Módszertani megjegyzés a PR leírásához:** a jelölteket úgy kerestem meg, hogy a
  `Mathlib/Analysis/` és `Mathlib/LinearAlgebra/` alatti **összes** `set_option linter.flexible false`
  sort töröltem, modulonként fordítottam, és csak azokat tartottam meg, ahol nem jött vissza
  figyelmeztetés. A többi (SobolevInequality, Complex/Arg, FourierTransformDeriv,
  MeanInequalities, PosPart/Basic, FaaDiBruno, Log/PosLog) **még szükséges** — ezeket
  változatlanul hagytam. Ez a lista egyben a következő PR-ok merítési bázisa is.
- **Tematikai megfeleltetés:** K‑4 (hatványfüggvény monotonitása kitevő szerint) / L‑8.

---

## 2. 7 napos benyújtási ütemterv

A Mathlib-ba való első PR-hoz szükséges egyszeri lépések (0. nap): GitHub-fiók,
`leanprover` Zulip regisztráció, `mathlib4` fork, a
[CONTRIBUTING.md](https://github.com/leanprover-community/mathlib4/blob/master/CONTRIBUTING.md)
elolvasása, valamint kérés a `#mathlib4 > PR reviews` streamen írási jogra (`mathlib4` push access)
vagy PR nyitása forkból.

| Nap | Teendő |
|---|---|
| 1 | Fork + friss `master`, `lake exe cache get`. PR 8 (tiszta törlés) benyújtása — ez a legkockázatmentesebb, jó „első PR". Egyúttal PR 2 (arccos) benyújtása. |
| 2 | PR 1 (L'Hospital) és PR 3 (rpow) benyújtása. Mindkettő `fix:` prefixszel. |
| 3 | PR 4 (cos_eq_cos_iff) és PR 7 (toMatrix_dualTensorHom). |
| 4 | PR 5 (charpoly_inv) és PR 6 (trace docstring). Az addig érkezett review-kra válasz. |
| 5 | Review-k átvezetése, `git push --force-with-lease` a saját ágakra. A CI-hibák javítása. |
| 6 | A kreditelismerési dosszié összeállítása: PR-táblázat URL-ekkel és státuszokkal, a `mathlib-prs/` diffek, a `RequestProject/Kreditelismeres/` Lean-fájlok, ez a dokumentum és a `KREDITELISMERES.md`. |
| 7 | Beadás a Modulo-rendszerben. A még nyitott (nem merged) PR-ok is csatolhatók — a benyújtás ténye és a review-beszélgetés önmagában is dokumentált szakmai aktivitás. |

**Reális elvárás:** hét nap alatt a merge nem garantált; a Mathlib review-ciklusa
gyakran ennél hosszabb. Ezért a dosszié úgy legyen felépítve, hogy a **benyújtott**
PR-ok is teljes értékű mellékletek legyenek, és a később megérkező merge-öket
utólag lehessen pótlólag beküldeni.

---

## 3. Hogyan lehet további jelölteket keresni? (kereső-receptek)

A `mathlib-prs/` patchek mind ugyanazzal a néhány kereséssel születtek. Ezek
újrafuttathatók a friss `master`-en; mindegyik olyan helyet talál, ahol a
karbantartók maguk jelezték, hogy javításra vár.

### 3.1 Karbantartói TODO-k a tárgyhoz tartozó könyvtárakban

```bash
rg -n "TODO" Mathlib/Analysis/Calculus/ Mathlib/Analysis/SpecialFunctions/ \
             Mathlib/LinearAlgebra/
```

### 3.2 Linter-kivételek (a legjobb „tiszta törlés" jelöltek)

```bash
rg -n "set_option linter\.[a-zA-Z.]* false" Mathlib/Analysis/ Mathlib/LinearAlgebra/
```

Ellenőrzési recept egy jelöltre:

```bash
# 1) töröld a `set_option linter.X false in` sort
# 2) fordítsd le a modult
lake build Mathlib.<Modul.Neve>
# 3) ha nincs figyelmeztetés → a kivétel elavult, a törlés maga a PR
# 4) ha van → a figyelmeztetés megmondja, melyik taktikát kell terminálissá tenni
```

Hasznos tudni: a `linter.flexible` alapértelmezésben `false`, **de** benne van a
`linter.mathlibStandardSet` halmazban (`Mathlib/Init.lean`), amit a Mathlib `lakefile.lean`-je
bekapcsol — tehát a repón belüli `lake build` során aktív. A `linter.docPrime` viszont
**nincs** benne (mathlib4#20560), így az arra vonatkozó kivételek eleve hatástalanok.

### 3.3 Felesleges `simp`-argumentumok

A `linter.unusedSimpArgs` alapból aktív, és a fordítás közben kiírja a fölösleges argumentumot
és a javasolt törlést. Óvatosan: a `-- see …/issues/29041` kommenttel ellátott kivételek
**ismert téves riasztások** — ott a jelzett argumentum valójában szükséges
(kipróbáltam a `Mathlib/Analysis/SpecialFunctions/Log/Deriv.lean` esetén: a törlés után a
bizonyítás nem fordul). Ezeket kerüld.

### 3.4 Elavult (deprecated) nevek továbbvezetése

```bash
rg -n "@\[deprecated" Mathlib/ | head -50
# majd: hol használják még a régi nevet?
rg -n "\bregi_nev\b" Mathlib/
```

### 3.5 Nem használt importok

```bash
lake exe shake --fix Mathlib.<Modul.Neve>
```

### 3.6 GitHub-oldali keresések

- `is:issue is:open label:"good first issue" repo:leanprover-community/mathlib4`
- `is:issue is:open label:"help wanted" repo:leanprover-community/mathlib4`
- `is:issue is:open label:t-analysis` / `label:t-linear-algebra` — ezek pont a két tárgy területei
- a `scripts/technical-debt-metrics.sh` fájl felsorolja, milyen „technikai adósság"-számlálókat
  követ a projekt; minden számláló csökkentése önmagában elfogadott hozzájárulás

### 3.7 Szűrés a két tárgy tematikájára

Kalkulus I szempontjából releváns modulok:
`Analysis/SpecialFunctions/{Pow,Log,Exp,Trigonometric}`, `Analysis/Calculus/{MeanValue,Taylor,LHopital,Deriv,Monotone}`,
`Order/Filter`, `Topology/Algebra/Order` (Bolzano, Weierstrass, Heine).

Lineáris algebra I szempontjából:
`Analysis/SpecialFunctions/Complex/*` (komplex szám, argumentum, egységgyökök),
`LinearAlgebra/Matrix/{Trace,Determinant,Rank,Charpoly,Adjugate,NonsingularInverse,Block}`,
`LinearAlgebra/{Basis,Dimension,Contraction,Ray}`, `Analysis/InnerProductSpace/Basic`
(skaláris szorzat, Cauchy–Schwarz, ortogonális vetítés).

### 3.8 Még nyitott, nagyobb falatok (ha marad idő)

- `Mathlib/LinearAlgebra/Matrix/Rank.lean:356` — TODO: a `rank_transpose` / `rank_conjTranspose`
  bizonyítása szükségtelen feltevéseket tesz `R`-re; Gauss-eliminációval általánosítható.
  Ez **közvetlenül a Lineáris algebra I rangtétel / Kronecker–Capelli blokkja.** Nagyobb munka,
  de a legerősebben tárgyhoz kötött jelölt.
- `Mathlib/LinearAlgebra/Matrix/Rank.lean:381`, `:462` — további TODO-k (általánosítás, `cRank`).
- `Mathlib/LinearAlgebra/Matrix/SchurComplement.lean:416`,
  `Mathlib/LinearAlgebra/Matrix/Charpoly/Eigs.lean:42`,
  `Mathlib/Analysis/Calculus/Taylor.lean:40` — TODO-szekciók (K‑18 Taylor-tétel).

---

## 4. A patchek alkalmazása

```bash
git clone https://github.com/<sajat-fork>/mathlib4.git
cd mathlib4
lake exe cache get
git checkout -b fix-lhopital-flexible
git apply -3 /utvonal/mathlib-prs/01-lhopital-flexible-linter.patch
lake build Mathlib.Analysis.Calculus.LHopital
git commit -am "fix: non-terminal simp in HasDerivAt.lhopital_zero_right_on_Ioo"
git push origin fix-lhopital-flexible
```

**PR-onként külön ág** — a Mathlib nem szereti a több független javítást egy PR-ban.
A címprefix `fix:` (működést/technikai adósságot javító) vagy `chore:` (tisztán karbantartó).

---

# Második kör — további kilenc előkészített hozzájárulás (09–17)

Ugyanaz a módszertan, mint fent: minden patch a `mathlib-prs/` könyvtárban van, mindegyik
**tisztán alkalmazható** a `8f9d9cff6bd728b17a24e163c9402775d9e6a365` alapkommitra
(`git apply --check` mind a 17 patchre `OK`), és mindegyik érintett modul **külön-külön**
és **együtt is** lefordul, új figyelmeztetés nélkül.

Ez a kör szándékosan a „a diff elvesz valamit" kategóriákra koncentrál:
**duplikáció megszüntetése**, **hibás állítás/dokumentáció javítása**, **maintainer-TODO lezárása**,
**linter-kivételek törlése**, és egyetlen **szimmetriahiány** pótlása.

| # | Patch | Érintett deklaráció(k) | Kategória | Tematikai megfeleltetés |
|---|---|---|---|---|
| 9 | `09-complex-samerayiff-linters.patch` | `Complex.sameRay_iff` | **két** linter-kivétel törlése | L‑1 (komplex számok, argumentum) |
| 10 | `10-poslog-sum-flexible-linter.patch` | `Real.posLog_sum` | maintainer-TODO + linter-kivétel | K‑4 (logaritmus), K‑2 (becslések) |
| 11 | `11-holder-ennreal-flexible-linter.patch` | `ENNReal.inner_le_Lp_mul_Lq` | maintainer-TODO + linter-kivétel | K‑2 (Hölder-egyenlőtlenség) |
| 12 | `12-arg-periodic-dedup.patch` | `Complex.image_exp_Ioc_eq_sphere`, `Complex.norm_eq_one_iff'` | maintainer-TODO + golfolás általános tétellel | L‑1 (egységkör, trigonometrikus alak) |
| 13 | `13-rpow-log-duplicates.patch` | 6 db duplikált `Real.*` lemma | **deduplikáció** + félrevezető név | K‑4 (hatvány, logaritmus) |
| 14 | `14-darboux-docstring-mismatch.patch` | `exists_hasDerivWithinAt_eq_of_le_of_ge` | **hibás állítás javítása** (a dokumentáció mást mondott) | K‑13 (Darboux-tulajdonság) |
| 15 | `15-unitarygroup-coe-duplicates.patch` | `Matrix.UnitaryGroup.{inv,mul,one}_apply` | **deduplikáció** (3 duplikált `simp`-lemma) | L‑7 (ortogonális/unitér mátrixok) |
| 16 | `16-tolin-primed-duplicates.patch` | `LinearMap.toMatrix*_apply'` (4 db) | **deduplikáció** + hívási helyek átírása | L‑5 (lineáris leképezés mátrixa) |
| 17 | `17-sInf-eq-top-dual.patch` | `sInf_eq_top'` (új) | **szimmetriahiány** pótlása | K‑1 (szuprémum/infimum) |

---

## PR 9 — `fix: remove two linter exceptions in Complex.sameRay_iff`

- **Fájl:** `Mathlib/Analysis/Complex/Arg.lean` (~33. sor)
- **Mi a baj:** a tétel előtt **két** linter-kikapcsolás áll (`linter.flexible` és
  `linter.unusedSimpArgs`, utóbbi a #29041 issue-ra hivatkozó megjegyzéssel), mert a bizonyítás
  egy nem lezáró `simp [field, hx]` után `rw`-vel dolgozik tovább.
- **A javítás:** a `(‖x‖ : ℂ) ≠ 0` tényt egy `have`-ben előre kimondjuk, a `simp only` lezárja a
  normalizálást, a maradék pedig egyetlen `rw [div_mul_eq_mul_div, div_eq_iff hx', mul_comm …, eq_comm]`.
  Mindkét `set_option` sor és a hozzájuk tartozó megjegyzés törölhető.
- **Ellenőrzés:** `lake build Mathlib.Analysis.Complex.Arg` → tiszta, figyelmeztetés nélkül.
- **Kockázat:** alacsony; az állítás betű szerint változatlan.
- **Tematika (L‑1):** a `SameRay ℝ x y ↔ arg x = arg y` állítás pontosan az „azonos irányú komplex
  számok = azonos argumentum" tétel, a komplex számok trigonometrikus alakjának blokkjából.

## PR 10 — `fix: non-terminal simp in Real.posLog_sum`

- **Fájl:** `Mathlib/Analysis/SpecialFunctions/Log/PosLog.lean` (~160. sor)
- **Mi a baj:** maintainer-TODO („non-terminal simp followed by positivity") + `linter.flexible false`.
- **A javítás:** a `monotoneOn_posLog` halmazbeli feltételeit (`_ ∈ Set.Ici 0`) nem `simp`/`positivity`
  hívja elő, hanem az explicit `Set.mem_Ici.2 (Finset.sum_nonneg fun _ _ ↦ abs_nonneg _)` term.
  A TODO és a `set_option` sor törölhető.
- **Ellenőrzés:** `lake build Mathlib.Analysis.SpecialFunctions.Log.PosLog`.
- **Tematika (K‑4, K‑2):** a `log⁺` becslése véges összegre — a logaritmus tulajdonságai és
  háromszög-egyenlőtlenség-típusú becslés.

## PR 11 — `fix: non-terminal simp in ENNReal.inner_le_Lp_mul_Lq`

- **Fájl:** `Mathlib/Analysis/MeanInequalities.lean` (~871. sor)
- **Mi a baj:** TODO („fix the non-terminal simp on the last line") + `linter.flexible false` a
  **Hölder-egyenlőtlenség** `ℝ≥0∞`-változatán.
- **A javítás:** a `simp [ENNReal.coe_rpow_of_nonneg, …] at this` lépést a `simp?` által kiadott
  konkrét `simp only [coe_finset_sum, coe_mul, one_div, inv_nonneg, …] at this` váltja fel, így a
  rákövetkező `convert` már nem „lebegő" simp-normálalakra épül. A TODO és a `set_option` törölhető.
- **Ellenőrzés:** `lake build Mathlib.Analysis.MeanInequalities`.
- **Tematika (K‑2):** Hölder- és Cauchy–Schwarz-típusú egyenlőtlenségek.

## PR 12 — `chore: prove image_exp_Ioc_eq_sphere from Periodic.image_Ioc`

- **Fájl:** `Mathlib/Analysis/SpecialFunctions/Complex/Arg.lean` (~326. sor)
- **Mi a baj:** maintainer-TODO: *„Replace the next two lemmas by general facts about periodic
  functions"*. A `norm_eq_one_iff'` bizonyítása kézzel bűvészkedik a `toIocMod`-dal.
- **A javítás:** a két lemma sorrendjét megcseréljük; `image_exp_Ioc_eq_sphere` most a
  `Function.Periodic.image_Ioc` + `Complex.range_exp_mul_I` következménye (a `θ ↦ exp (θ * I)`
  valós függvény `2π`-periodicitása egyetlen `simpa`), a `norm_eq_one_iff'` pedig kétsoros
  következmény. A TODO törölhető, a diff **nettó −5 sor**.
- **Ellenőrzés:** `lake build Mathlib.Analysis.SpecialFunctions.Complex.Arg`.
- **Tematika (L‑1):** `|z| = 1 ↔ z = e^{iθ}, θ ∈ (−π, π]` — az egységkör paraméterezése,
  az egységgyökök és a trigonometrikus alak alapja.

## PR 13 — `chore: deprecate six duplicate rpow/log lemmas`

- **Fájl:** `Mathlib/Analysis/SpecialFunctions/Pow/Real.lean` (783–875. sor környéke)
- **Mi a baj:** a fájlban **hat lemma szó szerint kétszer szerepel**, két néven:

  | megmaradó (helyes) név | törölt (félrevezető) név | állítás |
  |---|---|---|
  | `le_rpow_of_log_le` | `rpow_le_of_le_log` | `log x ≤ z * log y → x ≤ y ^ z` |
  | `le_pow_of_log_le` | `pow_le_of_le_log` | ugyanez `n : ℕ`-re |
  | `le_zpow_of_log_le` | `zpow_le_of_le_log` | ugyanez `n : ℤ`-re |
  | `lt_rpow_of_log_lt` | `rpow_lt_of_lt_log` | `log x < z * log y → x < y ^ z` |
  | `lt_pow_of_log_lt` | `pow_lt_of_lt_log` | ugyanez `n : ℕ`-re |
  | `lt_zpow_of_log_lt` | `zpow_lt_of_lt_log` | ugyanez `n : ℤ`-re |

  A törölt nevek a Mathlib elnevezési konvenciója szerint **hamisak**: az `rpow_le_…` alak azt
  ígéri, hogy a konklúzió `y ^ z ≤ x`, holott az `x ≤ y ^ z`.
- **A javítás:** a duplikált bizonyítások törlése, helyettük `@[deprecated] alias`.
  A Mathlibben **egyetlen hívási hely sincs** a törölt neveken (a `Nat.pow_le_of_le_log` más
  névtér és más állítás, érintetlen). Nettó **−18 / +6 sor**.
- **Ellenőrzés:** `lake build Mathlib.Analysis.SpecialFunctions.Pow.Real`.
- **Tematika (K‑4):** exponenciális és logaritmusfüggvény, hatványozás valós kitevővel.

## PR 14 — `fix: statement of exists_hasDerivWithinAt_eq_of_le_of_ge did not match its docstring`

- **Fájl:** `Mathlib/Analysis/Calculus/Darboux.lean` (~130. sor)
- **Mi a baj:** a lemma dokumentációja azt állítja: *„if `a ≤ b` and `f' b ≤ m ≤ f' a`, then
  `f' c = m` for some `c ∈ [a, b]`"* — a **kimondott** feltételek viszont `f' a ≤ m` és `m ≤ f' b`,
  azaz betű szerint azonosak a fölötte álló `exists_hasDerivWithinAt_eq_of_ge_of_le` lemmáéval.
  A fájl `<`-es változatai (`…_of_gt_of_lt` / `…_of_lt_of_gt`) helyesen duálisak, tehát ez
  másolási hiba: a Darboux-tétel „csökkenő" irányú esete valójában hiányzott a könyvtárból.
- **A javítás:** az állítás javítása a dokumentációhoz (és a duálishoz): `hma : m ≤ f' a`,
  `hmb : f' b ≤ m`; a bizonyítás ugyanaz az `OrdConnected.out`, felcserélt végpontokkal.
  Hívási hely nincs, tehát a javítás semmit nem tör el.
- **Ellenőrzés:** `lake build Mathlib.Analysis.Calculus.Darboux`.
- **Tematika (K‑13):** Darboux tétele — a derivált Darboux-tulajdonsága (Bolzano-tétel deriváltra).

## PR 15 — `chore: deduplicate Matrix.UnitaryGroup coercion simp lemmas`

- **Fájl:** `Mathlib/LinearAlgebra/UnitaryGroup.lean` (~143–151. sor)
- **Mi a baj:** három `@[simp]` lemmapár **azonos állítású**
  (`inv_val`/`inv_apply`, `mul_val`/`mul_apply`, `one_val`/`one_apply`): a `↑` és a `⇑`
  ugyanarra a beágyazásra elaborálódik, tehát a `simp` halmazban ugyanaz a szabály kétszer szerepel.
  Ráadásul a `mul_apply` és a `one_apply` a `Matrix` névtér `Matrix.mul_apply` / `Matrix.one_apply`
  lemmáit árnyékolja — a fájlon belül emiatt mindenhol ki kell írni a teljes nevet.
- **A javítás:** a `_val` alakok maradnak, az `_apply` alakok `@[deprecated] alias`-szá válnak.
  A Mathlibben nincs hívási hely. Ellenőriztem, hogy a három pár típusa **kifejezésszinten azonos**.
- **Ellenőrzés:** `lake build Mathlib.LinearAlgebra.UnitaryGroup`.
- **Tematika (L‑7):** unitér/ortogonális mátrixok csoportja.

## PR 16 — `chore: deprecate primed duplicates in LinearAlgebra.Matrix.ToLin`

- **Fájl:** `Mathlib/LinearAlgebra/Matrix/ToLin.lean` (626., 630., 832., 836. sor),
  hívási helyek: `Mathlib/LinearAlgebra/Determinant.lean` (404., 408.), `ToLin.lean` (923.)
- **Mi a baj:** négy vesszős lemma (`LinearMap.toMatrix_apply'`, `toMatrix_transpose_apply'`,
  `toMatrixAlgEquiv_apply'`, `toMatrixAlgEquiv_transpose_apply'`) **szó szerint ugyanazt mondja**,
  mint a vessző nélküli párja, és a bizonyításuk is csak annyi, hogy meghívják azt.
- **A javítás:** a négy lemma helyére `@[deprecated] alias` kerül, a három hívási hely átáll a
  vessző nélküli névre (**deprecation-propagáció**). Nettó **−14 / +8 sor**.
- **Ellenőrzés:** `lake build Mathlib.LinearAlgebra.Matrix.ToLin Mathlib.LinearAlgebra.Determinant`.
- **Tematika (L‑5):** lineáris leképezés mátrixa adott bázispárban, `[f]_{B,C}` mátrixelemei.

## PR 17 — `feat: add sInf_eq_top', the dual of sSup_eq_bot'`

- **Fájl:** `Mathlib/Order/CompleteLattice/Basic.lean` (~154. sor)
- **Mi a baj:** a fájlban minden szuprémumos állításnak megvan az infimumos duálisa
  (`sSup_eq_bot`↔`sInf_eq_top`, `eq_singleton_bot_of_sSup_eq_bot_of_nonempty`↔
  `eq_singleton_top_of_sInf_eq_top_of_nonempty`), **kivéve** a `sSup_eq_bot'`-t.
- **A javítás:** `sInf_eq_top' : sInf s = ⊤ ↔ s = ∅ ∨ s = {⊤}`, a fájl stílusát követve
  egyetlen sorban a rendezés-duálisból: `@sSup_eq_bot' αᵒᵈ _ _`.
- **Ellenőrzés:** `lake build Mathlib.Order.CompleteLattice.Basic`.
- **Tematika (K‑1):** felső/alsó határ, szuprémum és infimum — a teljességi axióma környéke.

---

## Módszertan: hogyan találtam meg ezeket (reprodukálható)

1. **Duplikátumkeresés a lefordított környezetben.** Egy `run_cmd` szkript végigmegy a
   `Environment.constants` táblán, és a **tételek típusát** (kifejezésként, nem szövegként)
   hasheli; minden olyan csoport gyanús, ahol két különböző név ugyanahhoz a típushoz tartozik.
   Az `Analysis` + `LinearAlgebra` + `Order.Filter` fákra ez 254 találatot ad; ezek nagy része
   szándékos `alias` vagy már `@[deprecated]`, a maradékból jött a 13., 15. és 16. PR
   (és így bukkant elő a 14. PR *hibás állítása* is: két lemma volt azonos, holott nem lett volna szabad).
2. **Nem használt hipotézisek keresése.** Ugyanilyen szkript minden tételnél megnézi, hogy egy
   explicit kötés előfordul-e a típus maradékában *és* a bizonyítás termjében. A vizsgált
   `Analysis` / `LinearAlgebra` fákban **nem volt találat** — a Mathlib `unusedVariables` lintere
   ezt már kiszűri; ezt a kategóriát tehát lezártnak tekintem (ez is eredmény: nem érdemes ott keresni).
3. **Szimmetriahiányok.** Névtranszformációs szkript (`sSup`↔`sInf`, `iSup`↔`iInf`) + a duális név
   létezésének ellenőrzése az `Order`/`Analysis`/`Topology.Order` fákban. A találatok túlnyomó része
   álpozitív (a duális más néven létezik: `csSup_Iic` ↔ `csInf_Ici`, `IsGreatest.csSup_mem` ↔
   `IsLeast.csInf_mem` stb.); ami maradt, az a 17. PR.
4. **Maintainer-TODO-k és linter-kivételek.** `rg -n "linter.flexible false|-- TODO"` a két tárgy
   moduljaira; ebből jött a 10., 11. és 12. PR.

Amit **megvizsgáltam, de elvetettem** (a teljesség és az őszinteség kedvéért):

- **Nem használt importok gyomlálása.** A `linter.minImports` javaslatai ebben a verzióban nem
  tiszta törlések (a „unneeded import" listához „missing imports" lista is tartozik, és a javasolt
  csere néha értelmetlen, pl. `import Lean.Parser.Command`), a nyers törlés több fájlt is eltört.
  Import-PR-t csak teljes Mathlib-fordítással szabad benyújtani; ez itt nem volt ellenőrizhető.
- **`Matrix.trace_units_conj` TODO (6607-es issue).** A típusannotáció **még mindig szükséges**:
  ellenőriztem, hogy nélküle az elaborátor a `Units` szorzást próbálja (`HMul (Matrix m m R)ˣ …`),
  és a fájl nem fordul. A TODO tehát nem zárható le, csak a Lean elaborátorának javításával.
- **`linearIndependent_of_subsingleton` átnevezési TODO.** A TODO által javasolt
  `LinearIndependent.of_subsingleton` név **már foglalt** (más állításra, `[Subsingleton ι]`
  feltétellel), tehát a TODO elavult; az átnevezés új névvitát nyitna, ezt maintainer-döntés nélkül
  nem érdemes PR-ba tenni.
- **Régi `@[deprecated]` jelölések törlése.** A legrégebbi deprecation a két tárgy fáiban
  `2025-08` — a Mathlib fél évnél régebbieket takarít, ezt a kört a projekt már elvégezte.

---

# Harmadik kör — nyolc további előkészített hozzájárulás (18–25)

Ez a kör kifejezetten a **Kalkulus I tételsor** és a **Lineáris algebra I tematika**
minimumkövetelményeihez kötődő modulokra koncentrál; a tematikai megfeleltetést a
[`KOMPETENCIA-LEFEDETTSEG.md`](KOMPETENCIA-LEFEDETTSEG.md) mátrix tartalmazza.
Mindegyik patch külön-külön lefordítva, **figyelmeztetés nélkül**.

| # | Patch | Érintett deklaráció(k) | Kategória | Tematika |
|---|---|---|---|---|
| 18 | `18-lineareq-det-coe-symm-golf.patch` | `LinearEquiv.det_coe_symm` | linter-kivétel megszüntetése + termbizonyítás | L‑6 |
| 19 | `19-natcast-le-rank-iff-duplicate.patch` | `natCast_le_rank_iff` | **deduplikáció** | L‑8 |
| 20 | `20-free-of-det-ne-one-duplicate.patch` | `LinearMap.free_of_det_ne_one` | **deduplikáció** (szó szerint másolt bizonyítás) | L‑6 |
| 21 | `21-todual-eq-repr-duplicate.patch` | `Module.Basis.toDual_eq_repr` | **deduplikáció** + hívási helyek | L‑5 |
| 22 | `22-map-coprod-prod-duplicate.patch` | `LinearMap.map_coprod_prod` | **deduplikáció** + hívási hely | L‑2, L‑5 |
| 23 | `23-expired-deprecations-linalg-analysis.patch` | 4 lejárt `@[deprecated] alias` | **tiszta törlés** | L‑8, K‑4, L‑3 |
| 24 | `24-expired-deprecations-calculus.patch` | 30 lejárt `@[deprecated] alias` (−102 sor) | **tiszta törlés** | K‑13 |
| 25 | `25-stale-integral-ofreal-todo.patch` | teljesített maintainer-TODO | **tiszta törlés** | (integrálszámítás) |

### PR 18 — `chore: golf LinearEquiv.det_coe_symm`

- **Fájl:** `Mathlib/LinearAlgebra/Determinant.lean` (~498. sor)
- **Mi a baj:** a tételt egy `set_option linter.unusedSimpArgs false in` sor és egy
  issue-hivatkozás előzi meg, a bizonyítás `simp [field, IsUnit.ne_zero f.isUnit_det']`.
- **A javítás:** a fájlban közvetlenül fölötte szerepel `LinearEquiv.det_symm_mul_det`
  (`det f.symm * det f = 1`), amiből az állítás egyetlen termmel adódik:
  ```lean
  theorem LinearEquiv.det_coe_symm {𝕜 : Type*} [Field 𝕜] [Module 𝕜 M] (f : M ≃ₗ[𝕜] M) :
      LinearMap.det (f.symm : M →ₗ[𝕜] M) = (LinearMap.det (f : M →ₗ[𝕜] M))⁻¹ :=
    eq_inv_of_mul_eq_one_left f.det_symm_mul_det
  ```
- **Mérleg:** −4 / +2 sor; a linter-kivétel és a hozzá tartozó komment eltűnik.
- **Ellenőrzés:** `lake build Mathlib.LinearAlgebra.Determinant` → sikeres, 0 figyelmeztetés.
- **Tematika (L‑6):** `det(f⁻¹) = (det f)⁻¹` — a determináns szorzástételének következménye.

### PR 19 — `chore: deprecate natCast_le_rank_iff in favour of Module.le_rank_iff`

- **Fájl:** `Mathlib/LinearAlgebra/Dimension/Finite.lean` (~213. sor)
- **Mi a baj:** a `natCast_le_rank_iff` állítás **típusra azonos** a
  `Module.le_rank_iff` állítással (`Mathlib/LinearAlgebra/Dimension/Basic.lean`, ~129. sor):
  `n ≤ Module.rank R M ↔ ∃ f : Fin n → M, LinearIndependent R f`, ugyanazzal a
  `[Nontrivial R]` feltétellel — csak más bizonyítással, egy importált fájlban.
  A duplikátumot a környezetet végigolvasó típus-hasheléses szkript találta.
- **A javítás:** a lemma helyére `@[deprecated] alias` kerül. Hívási hely a Mathlibben nincs
  (`rg -n "natCast_le_rank_iff\b"` csak a definíciót adja).
- **Ellenőrzés:** `lake build Mathlib.LinearAlgebra.Dimension.Finite` → sikeres, 0 figyelmeztetés.
- **Tematika (L‑8):** rang és lineáris függetlenség: „a rang legalább `n`” pontosan azt jelenti,
  hogy van `n` darab lineárisan független vektor.

### PR 20 — `chore: deprecate LinearMap.free_of_det_ne_one (duplicate)`

- **Fájl:** `Mathlib/LinearAlgebra/Determinant.lean` (188. és 326. sor)
- **Mi a baj:** a `Module.Free.of_det_ne_one` (188.) és a `LinearMap.free_of_det_ne_one` (326.)
  **ugyanaz az állítás, betűre ugyanazzal a bizonyítással** — copy-paste maradvány
  ugyanabban a fájlban.
- **A javítás:** a második törölve, helyette `@[deprecated] alias`. A Mathlibben csak az első
  névre van hivatkozás (`Mathlib/LinearAlgebra/Transvection.lean`).
- **Tematika (L‑6):** ha egy lineáris leképezés determinánsa nem 1, a modulus szabad —
  a determináns értelmezhetőségének feltétele.

### PR 21 — `chore: deprecate Basis.toDual_eq_repr (duplicate of toDual_apply_left)`

- **Fájl:** `Mathlib/LinearAlgebra/Dual/Basis.lean` (74. és 91. sor)
- **Mi a baj:** `toDual_eq_repr` egyetlen sorban `toDual_apply_left`-re hivatkozik, és
  típusra azonos vele; a fájl ezután hol az egyiket, hol a másikat használja.
- **A javítás:** `@[deprecated] alias`, és a két belső hívási hely (`toDual_eq_equivFun`,
  `toDual_injective`) átírása `toDual_apply_left`-re.
- **Tematika (L‑5):** bázis, koordinátafüggvények, duális bázis.

### PR 22 — `chore: deprecate LinearMap.map_coprod_prod (duplicate)`

- **Fájl:** `Mathlib/LinearAlgebra/Prod.lean` (240. és 430. sor)
- **Mi a baj:** `map_coprod_prod` szó szerint `coprod_map_prod f g p q`; a `@[simp]` jelölés
  az utóbbin van, tehát az előbbi tisztán redundáns.
- **A javítás:** `@[deprecated] alias` + a `prod_eq_sup_map` bizonyításában a hivatkozás cseréje.
- **Tematika (L‑2, L‑5):** alterek képe lineáris leképezés mellett, direkt összeg.

### PR 23 — `chore: remove deprecations from 2025-08 (LinearAlgebra, Analysis)`

- **Fájlok:** `Mathlib/LinearAlgebra/Span/Defs.lean` (2 alias),
  `Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.lean` (1),
  `Mathlib/Analysis/InnerProductSpace/Positive.lean` (1)
- **Mi a baj:** négy `@[deprecated] alias` 2025‑08‑19/20/24 óta; a Mathlib a fél évnél régebbi
  elavult neveket takarítja. Egyik névre sincs hivatkozás a könyvtárban.
- **A javítás:** tiszta törlés (a `IsPositive.of_isStarProjection` aliashoz tartozó
  árva docstringgel együtt).
- **Ellenőrzés:** a három modul fordítása sikeres, 0 figyelmeztetés.
- **Megjegyzés:** ez **korrigálja** a második kör „elvetett irányok” listájának utolsó pontját:
  a 2025‑08-as deprecationök *nem* voltak kitakarítva.

### PR 24 — `chore: remove PartialHomeomorph deprecations from 2025-08-29 (Analysis.Calculus)`

- **Fájlok:** `Mathlib/Analysis/Calculus/Implicit.lean` (18 alias),
  `…/InverseFunctionTheorem/{FDeriv,ContDiff,ApproximatesLinearOn}.lean` (4–4 alias)
- **Mi a baj:** a `PartialHomeomorph → OpenPartialHomeomorph` átnevezés 2025‑08‑29-i
  elavult nevei; **egyikre sincs hivatkozás** a Mathlibben.
- **A javítás:** 30 alias törlése, összesen **−102 sor**, semmilyen új sor.
- **Ellenőrzés:** mind a négy modul fordítása sikeres, 0 figyelmeztetés.
- **Tematika (K‑13):** az inverz függvény differenciálhatósága — a tételsor 13. pontja.
- **Megjegyzés a benyújtáshoz:** ugyanennek az átnevezésnek vannak elavult nevei a
  `Topology` és `Geometry` fákban is; a PR leírásában érdemes jelezni, hogy a jelen diff
  szándékosan csak az `Analysis/Calculus` alfát takarítja, és a többi külön PR-ban jöhet.

### PR 25 — `chore: remove stale TODO in IntervalIntegral.Basic`

- **Fájl:** `Mathlib/MeasureTheory/Integral/IntervalIntegral/Basic.lean` (~812. sor)
- **Mi a baj:** a `-- TODO: add \`Complex.ofReal\` version of \`_root_.integral_ofReal\`` komment
  már teljesítve van: a Bochner-integrálra `integral_complex_ofReal`
  (`Mathlib/MeasureTheory/Integral/Bochner/ContinuousLinearMap.lean`), az intervallum-integrálra
  pedig a TODO alatti `intervalIntegral.integral_ofReal` a keresett `ℂ`-változat.
- **A javítás:** a komment törlése (tiszta törlés, egyetlen sor).

---

## A harmadik kör módszertana és elvetett irányai

1. **Duplikátumkeresés újrafuttatva** (`mathlib-scan/DuplicateStatements.lean`, 253 csoport), majd
   szkriptes szűrés: kiestek az `alias`-ok, a már elavultak, a `.eq_1` egyenlőség-lemmák és a
   szándékos `fun_`/`'` változatok. A maradékból jött a 19., 20., 21. és 22. patch.
2. **Lejárt deprecationök.** `rg 'deprecated \(since := "2025-0[1-8]'` a két tárgy fáiban, majd
   névre keresés a teljes könyvtárban (nulla hivatkozás), végül modulonkénti fordítás.
   Ebből jött a 23. és 24. patch — és a korábbi kör téves lezárásának korrekciója.
3. **`unusedSimpArgs` linter-kivételek — megvizsgálva, elvetve.** A két tárgy fáiban öt ilyen
   kivétel van (`Analysis/Calculus/{Taylor,Monotone}.lean`, `Analysis/PSeries.lean`,
   `Analysis/SpecialFunctions/Log/Deriv.lean` ×2), mindegyik a
   [29041-es issue](https://github.com/leanprover-community/mathlib4/issues/29041)
   hivatkozásával. Kipróbáltam: a kivételek eltávolítása után a linter nyolc `simp`-argumentumot
   jelöl feleslegesnek, **de mind a nyolc valóban kell** — a `simp [field, …]` hívásokban ezek a
   `field` simprocok mellékfeltételeit zárják le, amit a linter nem lát. Az argumentumok törlésével
   mind a négy modul **elszáll** (`unsolved goals`), tehát a kivételek jogosak, a linter itt
   hamis pozitívot ad. Ezt a kategóriát ezért lezártam; a 18. patch az egyetlen kivétel, ahol a
   tétel *más úton* (termbizonyítással) bizonyítható, így a kivétel érdemben megszűnik.
4. **`fderiv_pow` / `fderiv_fun_pow`, `differentiable_finCons(')` stb.** Típusra azonos párok,
   de a Mathlib szándékos `fun_`/vesszős konvenciója; nem duplikátum, nem nyúltam hozzá.

## Együttes ellenőrzés

Mind a **25** patch egyszerre alkalmazva a pinned commitra (`git apply mathlib-prs/*.patch`,
konfliktus nélkül), majd az érintett 29 modul fordítása:

```
lake build <29 modul>
→ Build completed successfully (2693 jobs).
```

**0 hiba, 0 figyelmeztetés.** A teljes napló: `mathlib-prs/BUILD-LOG-all-25-patches.txt`.
