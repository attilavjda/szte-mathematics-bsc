# A Mathlib-hozzájárulási javaslatok állapota a **jelenlegi upstream master**-hez képest

**Ellenőrzés dátuma:** 2026-08-29
**Upstream commit:** `bbcd1968ee6950abe88b85dba6995da346c4b2a8` (leanprover-community/mathlib4, `master`)
**Toolchain:** `leanprover/lean4:v4.34.0-rc2` (a projekt saját, rögzített verziója továbbra is Lean 4.28.0 / Mathlib `v4.28.0`)

A korábbi 25 patch a Mathlib **v4.28.0** címkéjéhez készült. Ez a dokumentum végigveszi,
hogy melyik javaslat **létezik-e még** a mai masterben, melyiket **oldotta meg időközben az upstream**,
és milyen **új, még nyitott** hozzájárulási lehetőségeket találtam.

Az érvényes patchek frissített, a mai masterre illeszkedő változata a
[`master-2026-08/`](master-2026-08) könyvtárban van. Mindegyiket **lefordítottam** a masteren
(teljes Mathlib-build, lásd `master-2026-08/BUILD-LOG-master.txt`).

---

## 1. Összefoglaló táblázat

| # | Téma | Állapot a mai masteren |
|---|------|------------------------|
| 01 | L'Hôpital – `linter.flexible` kivétel | **Elavult** – az upstream már megszüntette a kivételt |
| 02 | `arccos`/`Inverse.lean` – flexible kivétel | **Elavult** |
| 03 | `Pow/Real.lean` – flexible kivétel | **Elavult** |
| 04 | `cos_eq_cos_iff` – flexible kivétel | **Elavult** |
| 05 | `Charpoly/Coeff.lean` – flexible kivétel | **Elavult** |
| 06 | `Matrix.Trace` – dokumentáció/prime-elnevezés | **Érvényes**, újragenerálva, fordul |
| 07 | `Contraction.lean` – flexible kivétel | **Elavult** |
| 08 | Feleslegessé vált flexible kivételek (`Pow/NNReal`, `CliffordAlgebra/Basic`) | **Elavult** |
| 09 | `Complex.sameRay_iff` – linter-kivételek | **Részben elavult → átdolgozva** (lásd lent) |
| 10 | `PosLog.lean` – flexible kivétel | **Elavult** |
| 11 | `MeanInequalities` (Hölder) – flexible kivétel | **Elavult** |
| 12 | `Complex/Arg.lean` – periodicitásra visszavezetett duplikáció | **Érvényes**, átdolgozva a mai kontextusra, fordul |
| 13 | `rpow`/`log` duplikált állítások | **Érvényes**, újragenerálva, fordul |
| 14 | Darboux – docstring/állítás eltérés | **Érvényes**, újragenerálva, fordul |
| 15 | `UnitaryGroup` – duplikált coe-lemmák | **Érvényes**, újragenerálva, fordul |
| 16 | `toLin`-primed duplikációk | **Érvényes**, újragenerálva, fordul |
| 17 | `sInf_eq_top'` hiányzó duális | **Elavult** – a master `@[to_dual]`-lal automatikusan generálja |
| 18 | `LinearEquiv.det` coe/symm – golf | **Érvényes**, újragenerálva, fordul |
| 19 | `natCast_le_rank_iff` duplikáció | **Érvényes**, újragenerálva, fordul |
| 20 | `free_of_det_ne_one` duplikáció | **Érvényes**, újragenerálva, fordul |
| 21 | `toDual_eq_repr` duplikáció | **Érvényes**, újragenerálva, fordul |
| 22 | `map_coprod_prod` duplikáció | **Érvényes**, újragenerálva, fordul |
| 23 | Lejárt deprecationök (linalg/analysis) | **Elavult** – az upstream automatikusan törölte |
| 24 | Lejárt deprecationök (calculus) | **Elavult** – az upstream automatikusan törölte |
| 25 | Elavult TODO az intervallumintegrálnál | **Érvényes**, újragenerálva, fordul |
| **26** | *(új)* `fiberwiseColim` – flexible kivétel megszüntetése | **Új javaslat**, fordul |
| **27** | *(új)* `Cotangent/Basic` – két flexible kivétel megszüntetése | **Új javaslat**, fordul |
| **28** | *(új)* `conjugateEquiv_associator_hom` – flexible kivétel megszüntetése | **Új javaslat**, fordul |
| **29** | *(új)* `succ_signVariations_le_X_sub_C_mul` (Descartes-féle előjelszabály) – flexible kivétel megszüntetése | **Új javaslat**, fordul |

**Mérleg:** a 25 régi javaslatból **11 változatlanul érvényes**, **1 (09.) részben**, **1 (12.) kontextusfrissítéssel**,
**12 elavult**, mert az upstream időközben megoldotta. Emellé **4 új** javaslat készült.

---

## 2. Miért avult el ilyen sok javaslat?

Két, azóta bevezetett upstream automatizmus miatt:

* **`.github/workflows/remove_deprecated_decls.yml`** – havonta (minden hó 15-én) automatikusan
  törli a 6 hónapnál régebbi `@[deprecated]` aliasokat, és PR-t nyit belőle. Emiatt a
  „lejárt deprecation” kategória (23., 24. patch) gyakorlatilag megszűnt kézi hozzájárulási
  lehetőségként: a mai masterben a legrégebbi deprecation is 2026-02-i.
* **`.github/workflows/rm_set_option.yml`** – hetente megpróbálja törölni azokat a
  `set_option ... in` sorokat, amelyek nélkül a fájl **változatlan bizonyítással** is lefordul.

Ezen felül az `@[to_dual]` attribútum bevezetése a rendezéselméleti fájlokban automatikusan
legyártja a duális állításokat, így a „hiányzó duálisok” keresése (17. patch, illetve a
`mathlib-scan/MissingDuals.lean` szkript) is jórészt tárgytalanná vált.

**Ami viszont megmaradt kézi munkának:** azok a `set_option linter.flexible false` kivételek,
ahol a bizonyítást *érdemben át kell írni* (a `simp` helyett `simp only [...]`, vagy a bizonyítás
átstrukturálása). Az automatizmus ezeket nem tudja megszüntetni, mert a kivétel törlése önmagában
lint-hibát okozna. A mai masterben **25 ilyen kivétel** van; ezek listája alább.

---

## 3. Az átdolgozott javaslatok

### 09 – `Complex.sameRay_iff` (`Mathlib/Analysis/Complex/Arg.lean`)

Az eredeti patch két linter-kivételt (`linter.flexible` és `linter.unusedSimpArgs`) szüntetett meg.
A masterben a `flexible` kivétel már nincs ott, de az `unusedSimpArgs` kivétel — és a mögötte lévő
`simp [field, hx, mul_comm, eq_comm]` hívás, amelyben a `mul_comm`/`eq_comm` argumentumok
kihasználatlanok — **még mindig jelen van**. A frissített patch a `simp`-et explicit
`div_mul_eq_mul_div` / `div_eq_iff` átírásra cseréli, így a kivétel és a
[#29041](https://github.com/leanprover-community/mathlib4/issues/29041) hivatkozás is törölhető.

### 12 – `image_exp_Ioc_eq_sphere` és `norm_eq_one_iff'` (`Mathlib/Analysis/SpecialFunctions/Complex/Arg.lean`)

A fájlban változatlanul ott a `-- TODO: Replace the next two lemmas by general facts about periodic
functions` megjegyzés. A patch pontosan ezt teszi meg: a `Function.Periodic.image_Ioc` és a
`range_exp_mul_I` segítségével bizonyítja a képhalmazt, a `norm_eq_one_iff'`-et pedig ebből vezeti le
(a `toIocMod`-os kézi számolás helyett). A patch a mai kontextushoz igazítva készült újra.

---

## 4. Az új javaslatok

### 26 – `CategoryTheory/Limits/Shapes/Grothendieck.lean`

A `fiberwiseColim` funktor `map_id` / `map_comp` mezőiben `ext; simp; apply ...` szerepelt, ezért a
fájlban `set_option linter.flexible false in` kivétel és egy `-- TODO: find a good way to fix the
linter` megjegyzés állt. A patch a `simp` hívásokat a linter által javasolt
`simp only [...]` hívásokra cseréli, és törli a kivételt.
*(Ellenőriztem, hogy a kivétel nélkül, az eredeti bizonyítással a linter valóban jelez — tehát a
javítás érdemi, nem csak egy felesleges sor törlése.)*

### 27 – `RingTheory/Extension/Cotangent/Basic.lean`

Két instance-bizonyításban `have ... := by simp [P]; infer_instance` szerepelt, emiatt két
`set_option linter.flexible false in` kivétel (és két `-- TODO: should infer_instance be considered
normalising?` megjegyzés) volt a fájlban. A patch mindkét helyen
`simp only [Generators.toExtension_Ring, P]`-re cseréli a `simp`-et, és törli a kivételeket.

### 29 – `Algebra/Polynomial/RuleOfSigns.lean`

A Descartes-féle előjelszabály induktív lépésében (`succ_signVariations_le_X_sub_C_mul`) egy
`all_goals` blokkon belüli `simp [...]`-et `exact rfl` követett, ezért a fájl elején
`set_option linter.flexible false in` kivétel és `-- TODO: fix non-terminal simp below` megjegyzés
állt. A patch a `simp`-et a két ág simp-halmazának uniójával képzett `simp only [...]`-ra cseréli,
és törli a kivételt.

### 28 – `CategoryTheory/Bicategory/Adjunction/Mate.lean`

A `conjugateEquiv_associator_hom` bizonyításában `simp [...]` után `bicategory` következett
(`-- simp followed by bicategory` megjegyzéssel). A patch a `simp`-et explicit `simp only [...]`
listára cseréli, így a kivétel törölhető.

---

## 5. További, még nyitott lehetőségek (nem készült rájuk patch)

A masterben megmaradt `set_option linter.flexible false` kivételek, azaz a kategória további
kézi munkát igénylő darabjai:

| Fájl | Sor(ok) | Megjegyzés |
|------|---------|------------|
| `Mathlib/SetTheory/Ordinal/Notation.lean` | 880 (`repr_opow`) | Megkíséreltem; a `simp` normálformája után a következő `rw` nem illeszkedik, a bizonyítást érdemben át kell strukturálni |
| `Mathlib/RingTheory/WittVector/FrobeniusFractionField.lean` | 220 | `simp [field, …]` (korábban `field_simp`); a `simp only`-ra cserélés után a lezáró `convert!` nem megy át — a `field` simp-halmaz diszkriminátorát is pótolni kell |
| `Mathlib/CategoryTheory/Dialectica/Monoidal.lean` | 122, 130 | `ext <;> simp; ext; simp; congr 1; ext <;> simp`: ágtól függő simp-halmazok, `suffices`-alapú átírás kell |
| `Mathlib/AlgebraicGeometry/Group/Affine.lean` | 390 | `erw` miatt nem terminális a `simp` |
| `Mathlib/RingTheory/Spectrum/Prime/ChevalleyComplexity.lean` | 277 | nagy simp-halmaz; megkíséreltem, de a `simp only`-ra cserélés után a bizonyítás későbbi `ext` lépése elakad |
| `Mathlib/Computability/PartrecCode.lean` | 254, 364, 614, 654, 694, 923 | mind „TODO: revisit after #13791” |
| `Mathlib/Computability/Primrec/List.lean` | 108, 293, 304, 682 | ua. |
| `Mathlib/Computability/TuringMachine/ToPartrec.lean` | 875, 971, 1167, 1201 | ua. |

Az utolsó három fájl kivételei egy nyitott upstream PR-hoz (#13791) vannak kötve, ezért ezekhez
csak annak rendeződése után érdemes hozzányúlni.

---

## 6. Hogyan ellenőrizhető

```bash
git clone https://github.com/leanprover-community/mathlib4.git
cd mathlib4 && git checkout bbcd1968ee6950abe88b85dba6995da346c4b2a8
lake exe cache get
for p in <ez a repó>/mathlib-prs/master-2026-08/*.patch; do git apply "$p"; done
lake build Mathlib
```

Mind a 17 patch **egyszerre**, konfliktus nélkül alkalmazható. A teljes `lake build Mathlib`
velük együtt **8802 job, 0 hiba, 0 figyelmeztetés** eredménnyel fut le; a napló:
[`master-2026-08/BUILD-LOG-master.txt`](master-2026-08/BUILD-LOG-master.txt).

Emellett minden patchet **külön-külön** is lefordítottam az általa érintett modulokra, a 26. patchnél
pedig azt is ellenőriztem, hogy a `set_option linter.flexible false` sor törlése az *eredeti*
bizonyítással valóban lint-figyelmeztetést vált ki — vagyis a javítás érdemi.

---

## 7. A repó saját Lean-portfóliója és a legújabb Mathlib

A `RequestProject/` alatti **mind a 17 saját Lean-modult** lefordítottam a mai master ellen is
(Lean `v4.34.0-rc2`). Az első próbafordításkor hat modul hibázott — nem matematikai hiba miatt,
hanem a közben megváltozott `simp`-normálformák, redukálhatóság és egy-két megváltozott
Mathlib-szignatúra miatt. Ezeket **verziófüggetlenül kijavítottam**, azaz úgy, hogy a forrás
*mind* a rögzített Lean 4.28.0 / Mathlib `v4.28.0`, *mind* a mai master alatt hibátlanul fordul:

| Modul | Az eltérés | A megoldás |
|---|---|---|
| `Portfolio/Kalkulus.lean` | a `simpa` a `Tendsto` célban a függvényt `Pi`-alakúra (`f - g`) hozta, a cél viszont pontonkénti (`fun x => f x - g x`) maradt (3 hely) | a `simpa using` helyett közvetlen `exact`, mert a `Continuous.sub`-ból jövő alak már pontosan a kívánt |
| `Kreditelismeres/KalkulusDifferencial.lean` | ugyanez a `HasDerivAt.sub`-nál; továbbá a `taylor_mean_remainder_lagrange` felfelé rendezetlen intervallumokra (`uIcc`, `uIoo`) és `x₀ ≠ x` feltételre változott | `simpa` helyett `rwa [sub_self]`; a Taylor-tételhez új `taylor_mean_remainder_lagrange_Icc` burkoló, amely `first`-tel mindkét Mathlib-szignatúrát kiszolgálja |
| `Kreditelismeres/LinAlgKomplexVektor.lean` | a `congrFun` eredménye már béta-redukált, ezért a `simp only at h` „no progress” | a hipotézis explicit típussal való bevezetése (`have h : … := congrFun ht i`) |
| `Portfolio/Automatak.lean` | a `Language α` és a `Set (List α)` közötti redukálhatóság szigorodott, a `simp [Language.mem_leftQuotient]` így nem talált célt (4 hely) | a `Language.mem_leftQuotient` (amúgy `Iff.rfl`) explicit alkalmazása `show`-val kiegészítve |
| `Portfolio/Szamitastudomany.lean` | `ℕ →. ℕ` vs. `ℕ → Part ℕ` redukálhatóság a Rice-tétel alkalmazásánál | a halmazbeli tagság helyett explicit egyenlőség-típusú `have`, `by simp` helyett `rfl` |
| `Kreditelismeres/KalkulusHatarertek.lean` | csak áttételesen hibázott (a `Portfolio/Kalkulus` importja miatt) | a fenti javítással megszűnt |

**Eredmény:** a projekt teljes egésze (17 modul) `sorry` nélkül, **hiba és figyelmeztetés nélkül
fordul a rögzített Lean 4.28.0 / Mathlib `v4.28.0` alatt**, és **hiba nélkül fordul a mai
Mathlib master (`bbcd196`, Lean `v4.34.0-rc2`) alatt is** — ott mindössze néhány
elavultsági (`deprecated`) figyelmeztetés marad (`push_neg`, `if_pos`, `if_neg`), ezek a
rögzített verzióban még a hivatalos elnevezések.

A repó `lean-toolchain`/`lake-manifest.json` fájlját szándékosan **nem** írtam át: a
kreditelismerési dossziéhoz benyújtott build a rögzített verzióval reprodukálható, a
master-kompatibilitás pedig így is biztosított.
