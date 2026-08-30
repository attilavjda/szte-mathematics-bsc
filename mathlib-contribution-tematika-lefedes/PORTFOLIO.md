# Bizonyítéktár — gépileg ellenőrzött portfólió

Ez a fájl a validációs kérelmek **3. mellékletének** nyersanyaga: tantárgyanként megadja, hogy a
tananyag melyik feladatához / tételéhez melyik Lean 4 deklaráció tartozik, és hol van
upstream (Mathlib) hozzájárulási lehetőség.

## Hogyan ellenőrizhető?

```bash
lake exe cache get      # Mathlib előfordított fájljai
lake build              # a teljes portfólió újraellenőrzése
```

* Lean toolchain és Mathlib-verzió: a repó `lean-toolchain` és `lake-manifest.json` fájljai rögzítik.
* A portfólió **egyetlen `sorry`-t sem tartalmaz**:
  ```bash
  rg -n "sorry" RequestProject/    # nincs találat
  ```
* A kulcstételek axiómafüggése ellenőrizve (`#print axioms`): mindegyik csak a standard
  `propext`, `Classical.choice`, `Quot.sound` axiómákra épül (a
  `not_functionally_complete_iff_neg` csak `propext`-re).

## Fájlszerkezet

| Fájl | Tartalom |
|---|---|
| `RequestProject/AutomatakEsFormalisNyelvek.lean` | DFA-konstrukciók, zártsági tételek, `aⁿbⁿ` |
| `RequestProject/Logika.lean` | ítéletlogika szintaxis/szemantika, Hilbert-kalkulus, helyesség, dedukciós tétel |
| `RequestProject/SzamitastudomanyAlapjai.lean` | megszámlálhatóság, átlós módszer, nem felismerhető nyelv |
| `RequestProject/Kriptografia.lean` | RSA, Diffie–Hellman, ElGamal |
| `RequestProject/KalkulusI.lean` | szuprémum, sorok, Bolzano, szigorú monotonitás |
| `RequestProject/LinearisAlgebraI.lean` | rang–nullitás, determináns, Cramer, sajátértékek |
| `RequestProject/Portfolio/Automatak.lean` | kiegészítő automataelmélet (konkatenáció, nem reguláris nyelvek, Myhill–Nerode) |
| `RequestProject/Portfolio/Logika.lean` | rezolúció, DNF, funkcionális teljesség, `{¬,↔}` nem teljes, **teljességi tétel** |
| `RequestProject/Portfolio/Szamitastudomany.lean` | megállási probléma, s-m-n, Rice, Post |
| `RequestProject/Portfolio/Kriptografia.lean` | one-time pad, Shamir, Euler–Fermat, APN |
| `RequestProject/Portfolio/Kalkulus.lean` | a `kalkulus_gyakorlo.pdf` feladatai |
| `RequestProject/Portfolio/LinearisAlgebra.lean` | determinánsok, rang, Cauchy–Schwarz, sajátértékek |

---

## 1. Kalkulus I — `kalkulus_gyakorlo.pdf` feladatai

| Feladat | Tartalom | Lean deklaráció (`Portfolio/Kalkulus.lean`) |
|---|---|---|
| 1.9. | √2 irracionális | `ex_1_9` |
| 1.11. | fordított háromszög-egyenlőtlenség | `ex_1_11` |
| 1.13. | általánosított háromszög-egyenlőtlenség (véges összegre) | `ex_1_13` |
| 1.14. a) | ∑ i = n(n+1)/2 | `ex_1_14a` |
| 1.14. b) | ∑ i³ = (n(n+1)/2)² | `ex_1_14b` |
| 1.14. c) | mértani sor részletösszege | `ex_1_14c` |
| 1.15. a) | ∑ i(3i+1) = n(n+1)² | `ex_1_15a` |
| 1.15. b) | 3·∑ i(i+1) = n(n+1)(n+2) | `ex_1_15b` |
| 1.15. c) | kétoldali becslés | `ex_1_15c_lower`, `ex_1_15c_upper` |
| 1.15. d) | n! < ((n+1)/2)ⁿ | `ex_1_15d` (segédtétel: `bernoulli_two_le`) |
| 2.11. | függvénykompozíció (Csebisev-jellegű azonosság) | `ex_2_11` |
| 2.18. | injektív függvények kompozíciója injektív | `ex_2_18` |
| 2.19. | polinom gyökeinek száma ≤ fokszám | `ex_2_19` |
| 3.7. i) | határérték | `ex_3_7i` |
| 3.14. | folytonosság / közbülsőérték-jellegű állítás | `ex_3_14` |
| 3.15. | folytonos függvények egyenlősége | `ex_3_15` |
| 3.16. c) | (1+1/n)ⁿ < 4 | `ex_3_16c` |
| 4.8./4.18. | x·eˣ alsó korlátja | `ex_4_8_18` |
| 4.10. e) | (eˣ−(1+x))/x² → 1/2 (L'Hospital) | `ex_4_10e` |
| 4.13. | **középponti konvexitás + folytonosság ⇒ konvexitás** | `ex_4_13` |

Elmélet (`RequestProject/KalkulusI.lean`): `sup_unique`, `tendsto_one_div_atTop`, `frog_series`,
`exists_root_cubic` (Bolzano), `strictMono_cube`.

---

## 2. Lineáris algebra I

| Tétel / feladattípus | Lean deklaráció |
|---|---|
| det(AB) = det A · det B | `Portfolio/LinearisAlgebra.det_mul_eq` |
| det Aᵀ = det A | `Portfolio/LinearisAlgebra.det_transpose_eq` |
| Sarrus-szabály 3×3-ra | `Portfolio/LinearisAlgebra.det_three_sarrus` |
| egyértelmű megoldhatóság ⇔ det ≠ 0 | `Portfolio/LinearisAlgebra.exists_unique_solution`, `LinearisAlgebraI.isUnit_iff_det_ne_zero` |
| nemtriviális magelem létezése | `Portfolio/LinearisAlgebra.exists_nontrivial_kernel` |
| Cramer-szabály (2×2) | `LinearisAlgebraI.cramer_two` |
| rang–nullitás tétel | `LinearisAlgebraI.rank_nullity` |
| rang(Aᵀ) = rang(A) | `Portfolio/LinearisAlgebra.rank_transpose_eq` |
| altér dimenziója ≤ tér dimenziója | `Portfolio/LinearisAlgebra.finrank_submodule_le` |
| Cauchy–Schwarz-egyenlőtlenség | `Portfolio/LinearisAlgebra.cauchy_schwarz` |
| ortogonális rendszer lineárisan független | `Portfolio/LinearisAlgebra.linearIndependent_of_orthogonal` |
| különböző sajátértékhez tartozó sajátvektorok függetlenek | `Portfolio/LinearisAlgebra.linearIndependent_pair_of_eigen` |
| konkrét sajátérték-számítás | `Portfolio/LinearisAlgebra.eigenvalues_example`, `LinearisAlgebraI.eigen_example` |
| 2×2 determináns képlete | `LinearisAlgebraI.det_two_by_two` |

---

## 3. Automaták és formális nyelvek (Ésik-jegyzet)

| Tétel | Lean deklaráció |
|---|---|
| szorzatautomata és a metszet felismerése | `AutomatakEsFormalisNyelvek.prodDFA`, `accepts_prodDFA` |
| komplementer automata | `complDFA`, `accepts_complDFA` |
| unió automatája | `unionDFA`, `accepts_unionDFA` |
| konkrét automata (paritás) helyessége | `parityDFA`, `parityDFA_accepts` |
| `aⁿbⁿ` nem felismerhető | `anbn`, `anbn_not_recognizable` |
| zártság szimmetrikus differenciára | `Portfolio/Automata.isRegular_symmDiff` |
| **zártság konkatenációra (1.4. Tétel)** | `Portfolio/Automata.isRegular_mul` |
| **zártság Kleene-iterációra (1.5. Tétel)** | `Portfolio/Automata.isRegular_kstar` (segédlemmák: `cons_mem_kstar`, `kstar_split`) |
| `{w wᴿ}` nem reguláris | `Portfolio/Automata.wwR`, `wwR_not_regular` |
| `{aⁿ²}` nem reguláris | `Portfolio/Automata.squares`, `squares_not_regular` |
| Myhill–Nerode-tétel | `Portfolio/Automata.myhill_nerode` |

---

## 4. Logika és informatikai alkalmazásai

| Tétel | Lean deklaráció |
|---|---|
| ítéletlogika szintaxisa, szemantikája | `Logika.PFormula`, `Logika.eval`, `Logika.Entails` |
| Hilbert-kalkulus | `Logika.Hilbert`, `Hilbert.id'` |
| helyességi tétel | `Logika.Hilbert.soundness` |
| gyengítés, dedukciós tétel | `Logika.Hilbert.weaken`, `Hilbert.deduction_of`, `Hilbert.deduction` |
| ellentmondás-mentesség | `Logika.Hilbert.consistent` |
| rezolúció helyessége | `Portfolio/Logika.resolution_sound` |
| DNF-konstrukció | `Portfolio/Logika.litFor`, `conjOf`, `disjOf`, `eval_conjOf`, `eval_disjOf` |
| **funkcionális teljesség** | `Portfolio/Logika.functionally_complete` |
| `{¬,↔}` **nem** funkcionálisan teljes | `Portfolio/Logika.IffF`, `IffF.second_difference`, `not_functionally_complete_iff_neg` |
| **teljességi tétel (Kalmár)** | `Portfolio/Logika.Hilbert.completeness` (segédtételek: `efq`, `byCases`, `ctxOf`, `signed`, `kalmar`, `elim`) |

---

## 5. A számítástudomány alapjai

| Tétel | Lean deklaráció |
|---|---|
| a szavak halmaza megszámlálható | `SzamitastudomanyAlapjai.words_countable` |
| a nyelvek halmaza nem megszámlálható (átlós módszer) | `SzamitastudomanyAlapjai.languages_not_countable` |
| a felismerhető nyelvek megszámlálhatóak ⇒ van nem felismerhető nyelv | `recognizableLanguages_countable`, `exists_not_recognizable` |
| nincs univerzális eldöntő | `SzamitastudomanyAlapjai.no_universal_decider` |
| **megállási probléma** | `Portfolio/Szamitastudomany.halting_problem` |
| s-m-n tétel | `Portfolio/Szamitastudomany.smn_theorem` |
| **Rice tétele** (alkalmazás) | `Portfolio/Szamitastudomany.rice_theorem_undefined` |
| Post tétele | `Portfolio/Szamitastudomany.post_theorem` |
| létezik nem kiszámítható függvény | `Portfolio/Szamitastudomany.exists_not_computable` |

---

## 6. Kriptográfia és adatbiztonság

| Tétel | Lean deklaráció |
|---|---|
| **one-time pad tökéletes titkossága** | `Portfolio/Kripto.otp_perfect_secrecy` |
| Shamir-féle titokmegosztás: két rész visszaadja a titkot | `Portfolio/Kripto.shamir_two_shares` |
| egyetlen rész nem árul el semmit | `Portfolio/Kripto.shamir_one_share_no_info` |
| Euler–Fermat-tétel | `Portfolio/Kripto.euler_theorem` |
| RSA helyessége | `Kriptografia.rsa_correct`, `pow_mod_prime_of_exp_congr` |
| Diffie–Hellman kulcsegyeztetés | `Kriptografia.diffie_hellman_correct` |
| ElGamal helyessége | `Kriptografia.elgamal_correct` |
| **a köbfüggvény APN karakterisztika 2 felett** | `Portfolio/Kripto.cube_is_apn`, `cube_apn_ncard` |

---

## 7. Azonosított Mathlib-hiányok (upstream hozzájárulási célok)

Ezek olyan állítások, amelyek a tananyagban központi szerepet játszanak, de a jelen Mathlib-verzióban
nem találhatók meg. Mindegyik jó PR-jelölt, és mindegyik közvetlenül egy vizsgatételhez köthető —
ez a kreditelismerési érvelés legerősebb része.

| # | Hiányzó állítás | Tantárgy | Jelen repóbeli megvalósítás | Megjegyzés |
|---|---|---|---|---|
| 1 | `Language.IsRegular` zártsága a **konkatenációra** | Automaták | `Portfolio/Automata.isRegular_mul` | a `Language.IsRegular` névtérben jelenleg csak `compl`, `add`, `inf`, `reverse` van |
| 2 | `Language.IsRegular` zártsága a **Kleene-iterációra** (`L∗`) | Automaták | `Portfolio/Automata.isRegular_kstar` | ugyanígy hiányzik a Mathlibből |
| 3 | **Kleene tétele**: reguláris kifejezés ↔ véges automata | Automaták | *még nincs* | nagy, de nagyon értékes hozzájárulás |
| 4 | részhalmaz-konstrukció (NFA determinizálás) helyessége | Automaták | *még nincs* | |
| 5 | **középponti konvexitás + folytonosság ⇒ konvexitás** | Kalkulus | `Portfolio/Kalkulus.ex_4_13` | a `Mathlib/Analysis/Convex` alatt nincs ilyen állítás |
| 6 | ítéletkalkulus **teljességi tétele** Hilbert-rendszerre | Logika | `Portfolio/Logika.Hilbert.completeness` | a Mathlibben nincs ítéletlogikai Hilbert-kalkulus |
| 7 | funkcionális teljesség / összekötő-rendszerek teljességének elmélete | Logika | `functionally_complete`, `not_functionally_complete_iff_neg` | |
| 8 | APN függvények elmélete (differenciális egyenletesség) | Kriptográfia | `cube_is_apn`, `cube_apn_ncard` | kapcsolódik a Kasami/APN projekthez |
| 9 | Shamir-féle titokmegosztás helyessége és biztonsága | Kriptográfia | `shamir_two_shares`, `shamir_one_share_no_info` | általános (k, n) küszöbre kiterjeszthető |
| 10 | bonyolultságelmélet (P, NP, Cook–Levin) | Számítástudomány | *még nincs* | hosszú távú cél |

## 8. Külső projektek beillesztése a bizonyítéktárba

| Projekt | Mely tárgyhoz | Milyen tanulási eredményt igazol |
|---|---|---|
| Merge-elt Mathlib PR-ok (háromszög-egyenlőtlenség és társai) | Kalkulus I | analízis-alapfogalmak, egyenlőtlenségek, bizonyítási készség, szakértői bírálaton átment munka |
| Kasami / APN formalizáció | Kriptográfia | S-dobozok, differenciális kriptoanalízis, véges testek |
| FBK Trento: folytonos idejű temporális logika, induktív invariánsok tanúsítványainak ellenőrzése | Logika és informatikai alkalmazásai | temporális logika, modellellenőrzés, formális verifikáció — a tárgy „informatikai alkalmazásai" fele |
| CircomAudit | Kriptográfia; Számítástudomány | ZK-áramkörök, protokoll- és implementációbiztonság |
| ArkLib, Cedar | Lineáris algebra I; Kriptográfia | véges testek feletti lineáris algebra, polinom-elkötelezettségek, hozzáférés-vezérlési logika |

Minden külső projekthez a kérelemben meg kell adni: a repó URL-jét, a saját commitok / PR-ok
permalinkjeit, a közreműködés arányát, az időszakot és a becsült munkaórát.

---

## 9. Előkészített Mathlib-hozzájárulások (`mathlib-prs/`)

A `mathlib-prs/` könyvtárban **25 benyújtásra kész `.patch` fájl** található; mindegyik a
`lake build` paranccsal a pinned Mathlib-commiton (`8f9d9cf`, Lean 4.28.0) figyelmeztetés nélkül
lefordul. A patchek típusai: maintainer-TODO teljesítése, linter-kivétel megszüntetése,
duplikált állítások kiszűrése, hibás állítás javítása, lejárt elavult nevek törlése,
hiányzó duális állítás pótlása.

| Fájl | Tartalom |
|---|---|
| `mathlib-prs/01–08` | első kör: L'Hospital, arccos, rpow, `cos_eq_cos_iff`, `charpoly_inv`, `trace`, `toMatrix_dualTensorHom`, elavult kivételek |
| `mathlib-prs/09–17` | második kör: `Complex.sameRay_iff`, `posLog_sum`, Hölder, `Arg` deduplikáció, 6 duplikált rpow/log-lemma, **Darboux-hibajavítás**, `UnitaryGroup`, `toLin`, `sInf_eq_top'` |
| `mathlib-prs/18–25` | harmadik kör: `det_coe_symm`, `natCast_le_rank_iff`, `free_of_det_ne_one`, `toDual_eq_repr`, `map_coprod_prod`, lejárt deprecationök (34 db), elavult TODO |
| `mathlib-prs/BUILD-LOG-all-17-patches.txt` | a 01–17 patchek **együttes** alkalmazása után készült build-napló (2357 job, 0 hiba, 0 figyelmeztetés) |
| `mathlib-prs/BUILD-LOG-all-25-patches.txt` | a **mind a 25** patch együttes alkalmazása után készült build-napló (2693 job, 0 hiba, 0 figyelmeztetés) |
| `mathlib-prs/MASTER-2026-08-STATUS.md` | **2026-08-29:** a 25 javaslat állapota a mai upstream `master`-en (11 változatlanul érvényes, 2 átdolgozva, 12 elavult) + 3 új javaslat |
| `mathlib-prs/master-2026-08/` | a mai masterre (`bbcd196`, Lean `v4.34.0-rc2`) illeszkedő, lefordított 17 patch |

A részletes leírás: [`MATHLIB-PR-JAVASLATOK.md`](MATHLIB-PR-JAVASLATOK.md).
A tantárgyi tematikához való kötés: [`KOMPETENCIA-LEFEDETTSEG.md`](KOMPETENCIA-LEFEDETTSEG.md).
A kereséshez használt szkriptek: [`mathlib-scan/`](mathlib-scan/).
