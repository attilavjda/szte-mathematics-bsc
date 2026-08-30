# PR-áttekintés: mi van a csatolt archívumban, és mi került már be a Mathlibbe

- **`pr_attekintes.pdf`** (és a forrása, `pr_attekintes.tex`) — a teljes áttekintés:
  1. mit tartalmaz az `e525434d-…-aristotle(6).tar.gz` archívum (9 javaslat, 11 patch fájl,
     8 gépi ellenőrző Lean-fájl, 2 script);
  2. mindegyik javaslat mai státusza a nyilvános Mathlib `master` ágán
     (`b87b4e892`, 2026-08-30): bekerült / még aktuális / lekörözték;
  3. a szerző összes Mathlib-PR-ja merge-státusszal (6 merge-elt, köztük a
     Darboux-PR, 9 nyitott);
  4. tematikaelem ↔ tétel megfeleltetés a kreditelismeréshez;
  5. ütközések és javasolt következő lépések.

- **`patches/`** — azok a patch fájlok, amelyek a mai `master`-en **tisztán illeszkednek**
  (`git apply --check` ma lefutott mindegyikre):

  | fájl | javaslat |
  |---|---|
  | `abs-abs-sub-abs-dedup.patch` | fordított háromszög-egyenlőtlenség deduplikálása |
  | `sameray-drop-isstrictorderedring.patch` | `SameRay`: felesleges `[IsStrictOrderedRing R]` törlése |
  | `finset-range-add-dedup.patch` | `Finset.range_add` vs. `range_add_eq_union` |
  | `pigeonhole-docstring-fixes.patch` | skatulyaelv modul-docstring javítása |
  | `stale-docstring-references.patch` | elavult docstring-hivatkozások 6 fájlban |
  | `stale-rename-todos-2026-08-30.patch` | átnevezési TODO-k maradéka (Schwarz + `surj''`), mai masterre újragenerálva |

  Alkalmazás: `git -C <mathlib-checkout> apply pr-attekintes/patches/<fájl>`.

Az archívum azon patch-ei, amelyek **már nem** illeszkednek (mert a javított hiba
bekerülésével megszűnt), szándékosan nincsenek itt átmásolva:
`to_additive-reflect.patch`, `to_additive-twins-generated.patch`,
`natantidiagonal-unused-variable.patch` (lásd PR #42592, #42763, #42907).
