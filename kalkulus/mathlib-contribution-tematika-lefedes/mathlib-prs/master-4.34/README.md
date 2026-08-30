# Mathlib‑patchek a mai `master` (v4.34.0-rc2) ellen

Ezek a patchek a Kalkulus I tematika egy‑egy pontjához tartoznak; a hozzárendelést és az
indoklást a repó gyökerében lévő
[`KALKULUS-TEMATIKA-MATHLIB-4.34-PRJELOLTEK.md`](../../KALKULUS-TEMATIKA-MATHLIB-4.34-PRJELOLTEK.md)
tartalmazza.

**Bázis:** `leanprover-community/mathlib4`, commit
`58e016c6f6c829b5f25b1a87a88f495f40e70aa7` (2026‑08‑29), toolchain `leanprover/lean4:v4.34.0-rc2`.

**Ellenőrzés módja:** minden patch alkalmazása után az érintett fájl(oka)t
`lake env lean <fájl>` paranccsal lefordítottam a fenti commit ellen — hiba nélkül. A törölt
`deprecated` aliasok hívóhelyeit `rg -w <név> Mathlib Archive Counterexamples MathlibTest`
paranccsal ellenőriztem (mindegyikre 0 találat a saját deklarációján kívül). A **teljes** Mathlib
build nem futott le mind a 21 patchre; benyújtás előtt érdemes `lake build`-del ellenőrizni.

**Ezek nem beküldött pull requestek**, hanem benyújtásra kész diffek.

| Patch | Típus | Érintett fájl(ok) |
|---|---|---|
| `T01-delete-expired-sInf-upperBounds-alias.patch` | tiszta törlés | `Order/CompleteLattice/Basic.lean` |
| `T02-delete-expired-succpred-aliases.patch` | tiszta törlés | `Order/SuccPred/Archimedean.lean` |
| `T03-delete-expired-holder-aliases.patch` | tiszta törlés | `Analysis/MeanInequalities.lean` |
| `T04-delete-expired-polynomial-aliases.patch` | tiszta törlés | `Analysis/Polynomial/Basic.lean` |
| `T04-delete-expired-logDeriv-exp-aliases.patch` | tiszta törlés | `Analysis/SpecialFunctions/Trigonometric/Deriv.lean` |
| `T05-delete-expired-partialInv-aliases.patch` | tiszta törlés (2026‑09‑11 után) | `Logic/Function/Basic.lean` |
| `T06-evenfunction-neg-sub-symmetry.patch` | szimmetria‑hézag pótlása | `Algebra/Group/EvenFunction.lean` |
| `T07-rename-antiperiodic-div-inv-to-div-const.patch` | félrevezető név javítása (+ deprecated alias) | `Algebra/Field/Periodic.lean` |
| `T08-delete-expired-interval-union-primed.patch` | tiszta törlés | `Order/Interval/Set/LinearOrder.lean` |
| `T09-rename-tendsto-mul-atTop-discharge-todo.patch` | TODO végrehajtása + átnevezés + doc‑javítás | `Topology/Order/LeftRightNhds.lean`, `Topology/Algebra/Order/Field.lean` |
| `T10-delete-expired-limit-aliases.patch` | tiszta törlés (2026‑09‑18 / 2026‑10‑07 után) | `Analysis/SpecificLimits/Basic.lean`, `Analysis/SpecialFunctions/Log/Monotone.lean` |
| `T11-delete-expired-continuousOn-typo-aliases.patch` | tiszta törlés | `Topology/ContinuousOn.lean` |
| `T12-generalize-exists-isLocalExtr-nhdsSet-discharge-todo.patch` | TODO végrehajtása: két hipotézis egyre cserélve | `Topology/Order/Compact.lean`, `Topology/MetricSpace/ProperSpace/Lemmas.lean` |
| `T13-delete-expired-isBigO-sub-rev.patch` | tiszta törlés | `Analysis/Calculus/Deriv/Basic.lean` |
| `T14-delete-expired-deriv-comp-of-eq.patch` | tiszta törlés | `Analysis/Calculus/Deriv/Comp.lean` |
| `T15-delete-expired-circleAverage-aliases.patch` | tiszta törlés | `Analysis/Complex/MeanValue.lean` |
| `T16-strictAnti-docstring-fix.patch` | hibás docstring javítása | `Analysis/Calculus/Deriv/MeanValue.lean` |
| `T17-derivativetest-stale-docref.patch` | nem létező tételre hivatkozó docstring javítása | `Analysis/Calculus/DerivativeTest.lean` |
| `T18-dedup-concaveOn-hasDerivWithinAt2.patch` | deduplikáció (14 sor → 7 sor) | `Analysis/Convex/Deriv.lean` |
| `T19-concaveOn-isMaxOn-deriv-duals.patch` | szimmetria‑hézag pótlása (3 hiányzó `ConcaveOn.isMaxOn_*` duális) | `Analysis/Convex/Deriv.lean` |
| `T20-deriv-lhopital-zero-left-on-Ioc-symmetry.patch` | szimmetria‑hézag pótlása (hiányzó `deriv.lhopital_zero_left_on_Ioc`) | `Analysis/Calculus/LHopital.lean` |

Alkalmazás:

```bash
cd mathlib4 && git apply .../T16-strictAnti-docstring-fix.patch
```
