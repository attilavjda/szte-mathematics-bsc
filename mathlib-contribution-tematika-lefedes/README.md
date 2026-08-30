This project was edited by [Aristotle](https://aristotle.harmonic.fun).

To cite Aristotle:
- Tag @Aristotle-Harmonic on GitHub PRs/issues
- Add as co-author to commits:
```
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```

# `mathlib-scan/` — a hozzájárulás-jelöltek keresésére használt szkriptek

Ezek önálló Lean-fájlok: a teljes `Mathlib` környezetet importálják, és `run_cmd`-ben
metaprogramozással vizsgálják a lefordított környezetet. Nem részei a projekt build-céljainak
(nincsenek benne a `RequestProject` könyvtárban), a `lake env lean <fájl>` paranccsal futtathatók
egy olyan munkakörnyezetben, ahol a Mathlib már le van fordítva:

```bash
lake env lean mathlib-scan/DuplicateStatements.lean
```

| Fájl | Mit keres | Eredmény |
|---|---|---|
| `DuplicateStatements.lean` | két különböző nevű tétel **azonos típussal** (kifejezésszintű egyezés) az `Analysis` / `LinearAlgebra` / `Order.Filter` fákban | 254 csoport; ebből — a szándékos `alias`-ok és a már elavultnak jelöltek kiszűrése után — a 13., 14., 15. és 16. patch |
| `UnusedHypotheses.lean` | olyan **explicit hipotézis**, amely sem az állítás maradékában, sem a bizonyítás termjében nem fordul elő | az `Analysis` / `LinearAlgebra` / `SpecialFunctions` / `Complex` fákban **nincs találat** (a Mathlib `unusedVariables` lintere már kiszűri) |
| `MissingDuals.lean` | `sSup`-os állítás, amelynek a névtranszformációval kapott `sInf`-es duálisa nem létezik | 132 jelölt, túlnyomó részt álpozitív (a duális más néven létezik); a valódi hiány a 17. patch (`sInf_eq_top'`) |

A találatok mindegyikét kézzel ellenőriztem, mielőtt patch lett belőle: megnéztem a forrást,
a hívási helyeket (`rg`), és lefordítottam az érintett modult.

---

# Kreditelismerési dosszié — belépési pontok

**Nyilvános repozitórium:** <https://github.com/attilavjda/szte-mathematics-bsc> —
itt jelenik meg a két tankönyv-formalizáció is (nyílt forráskódú hozzájárulás):
Szabó László *Bevezetés a lineáris algebrába* → `linearis-algebra/`, Leindler László
*Analízis* → `kalkulus/`. (2026‑08‑30-i állapot: a repóban a `README` volt közzétéve,
a két könyvtár feltöltése folyamatban.)

**Merge-elt Mathlib pull requestek (a diffek nyilvánosak):**
[#42810](https://github.com/leanprover-community/mathlib4/pull/42810) ·
[#42579](https://github.com/leanprover-community/mathlib4/pull/42579) ·
[#42592](https://github.com/leanprover-community/mathlib4/pull/42592) ·
[#42763](https://github.com/leanprover-community/mathlib4/pull/42763) ·
[#42907](https://github.com/leanprover-community/mathlib4/pull/42907) ·
[#42493](https://github.com/leanprover-community/mathlib4/pull/42493).

| Fájl | Tartalom |
|---|---|
| `KREDITELISMERES.md` | a szabályzati háttér és az eljárásrend |
| `KOMPETENCIA-LEFEDETTSEG.md` | tételsor szerinti lefedettség (Kalkulus I: K‑1…K‑18, Lineáris algebra I: L‑1…L‑8) |
| `KALKULUS-TEMATIKA-PR-TABLAZAT.md` | a Kalkulus I **tárgytematika** („Tantárgy tartalma”) elemenkénti táblázata: T‑1…T‑20 ↔ saját Lean-bizonyíték ↔ Mathlib-hozzájárulás / PR-jelölt ↔ **beküldött PR (✅ merge-elve / ⬜ még nem)** ↔ kreditátviteli teendő |
| `pr-attekintes/` | a ténylegesen beküldött Mathlib pull requestek áttekintője (`pr_attekintes.pdf` + LaTeX-forrás) és a ma is tisztán illeszkedő hat patch |
| `KALKULUS-TEMATIKA-MATHLIB-4.34-PRJELOLTEK.md` | ugyanaz a T‑1…T‑20 bontás, de **kizárólag a Mathlib‑hozzájárulásokkal**, a **mai `master` (v4.34.0-rc2)** ellen ellenőrizve; ez a fájl a „legújabb Mathlib” nézet, a fenti táblázat a rögzített (pinned) bázisé |
| `MATHLIB-PR-JAVASLATOK.md`, `mathlib-prs/` | a hozzájárulások leírása és a kész patchek (`mathlib-prs/master-4.34/`: 17 ellenőrzött patch a mai masterhez) |
| `PORTFOLIO.md` | feladat ↔ formalizált bizonyítás leltár |
| `RequestProject/` | a Lean-könyvtár (`lake build`, `sorry` nélkül) |
| `Oklevel/` | önkéntes munka oklevél négy tervváltozata (LaTeX + PDF); 2. oldal: tematika ↔ PR táblázat merge-pipákkal, 3. oldal: merge-elt PR-ok linkkel és a tankönyv-formalizációk |
