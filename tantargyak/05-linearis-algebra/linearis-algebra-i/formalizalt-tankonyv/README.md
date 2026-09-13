# Lineáris algebra — Szabó László *Bevezetés a lineáris algebrába* (2006) formalizálása

Ez a könyvtár **önálló, külön fordítható Lean 4 + Mathlib projekt**: Szabó László
*Bevezetés a lineáris algebrába* (Polygon jegyzettár, Szegedi Tudományegyetem Bolyai
Intézet, 2006) című jegyzetének **1–18. fejezetét** formalizálja, valamint a rá épülő
**Lineáris algebra I. (MBLK15E)** tantárgyi tematikát.

Az analízis anyag ettől függetlenül, a szomszédos `Analizis/` projektben található.

## Fordítás és futtatás

```bash
cd LinearisAlgebra
lake exe cache get     # a Mathlib előre lefordított változatának letöltése
lake build             # a teljes könyvtár fordítása (ellenőrzése)
```

A `lake build` egyben az anyag **ellenőrzése** is: minden definíció és tétel átmegy a Lean
magján. A könyvtár `sorry`-mentes, `axiom`-mentes; a fordítás hibamentesen és
figyelmeztetés nélkül fut le.

Egyetlen

```lean
import LinearisAlgebra
```

sorral az egész formalizált anyag elérhető (a gyökérmodul: `LinearisAlgebra.lean`).

## Terjedelem

* 29 modul, kb. 8 900 sor, 500-nál több tétel és lemma.

## Alapelvek

* **Tankönyvhű (faithful) megfogalmazás:** a definíciók a jegyzet saját fogalmai (pl. a
  `det'` a jegyzet rekurzív, első sor szerinti kifejtéssel adott determinánsa), és külön
  híd-lemmák kötik össze őket a Mathlib fogalmaival (`det'_eq_det`, …).
* **Tankönyvhű bizonyítások:** ahol lehet, a bizonyítás a könyv gondolatmenetét követi.
* **Magyar nyelvű dokumentáció**, a jegyzet számozásával (pl. „**9.2. Tétel.**”).

### Elkészült modulok

| Modul | Könyvbeli anyag | Fő tartalom |
|---|---|---|
| `LinearisAlgebra/Ch01_Bevezetes.lean` | 1. fejezet | `Szamtest` (számtest) struktúra, példák (`ℂ`, `ℝ`, `ℚ`, `ℚ(√2)`), összeg- és szorzatlemmák |
| `LinearisAlgebra/Ch02_Matrixok.lean` | 2. fejezet | `Matrix'`, nullmátrix, diagonális, háromszög- és egységmátrix, a 2.3/2.5/2.7. tételek, transzponált |
| `LinearisAlgebra/Ch03_Determinans.lean` | 3. fejezet | rekurzív `det'` (kifejtés az első sor szerint), `det'_eq_det`, `det'_one/two/three`, aldeterminánsok, sorcsere |
| `LinearisAlgebra/Ch03b_DualitasVandermonde.lean` | 3. fejezet (folytatás) | **3.7. dualitási elv**, **3.8.** oszlopcsere, **3.9.** kifejtés oszlop szerint, **3.11–3.12.** Vandermonde-determináns, **3.13.** aldetermináns és komplementere, **3.16. szorzástétel** |
| `LinearisAlgebra/Ch03c_Laplace.lean` | 3.14–3.15 | a **Laplace-tétel** (kifejtés `r` kijelölt sor szerint) és **duálisa** (kifejtés `r` kijelölt oszlop szerint); a jegyzet bizonyítás nélkül közli, itt teljes bizonyítással |
| `LinearisAlgebra/Ch04_Inverzmatrix.lean` | 4. fejezet | `Inverze` és egyértelműsége, ferde kifejtési tétel, `adjungaltMatrix`, `A·adj A = |A|·E`, az inverz létezésének feltétele, `(AB)⁻¹ = B⁻¹A⁻¹`, `(Aᵀ)⁻¹`, hasonlóság |
| `LinearisAlgebra/Ch05_Egyenletrendszerek.lean` | 5. fejezet | `Megoldasa`, mátrix- és vektoregyenlet-alak, elemi átalakítások ekvivalenciája, **Cramer-szabály**, homogén rendszerek, a megoldáshalmaz szerkezete |
| `LinearisAlgebra/Ch05b_GaussElimination.lean` | 5. fejezet (folytatás) | `ElemiLepes`, `ElemiAtalakitasok`, az elemi átalakítások megoldástartósága, **5.3.** `Lepcsos` (lépcsős alak), **5.4. Tétel** (`letezik_lepcsos`), **Gauss-elimináció** (`gauss_elimination`) |
| `LinearisAlgebra/Ch06_Vektorterek.lean` | 6. fejezet | `Vektorter` (a 6.1. axiómák), **6.3.** és **6.5. Tétel**, példák, `Alter` és altérkritérium, alterek metszete, `Generalt` (**6.10. Tétel**), alterek összege (**6.12. Tétel**) |
| `LinearisAlgebra/Ch07_LinearisFuggetlenseg.lean` | 7. fejezet | `LinFuggetlen`/`LinFuggo`, **7.2. Tétel** (három ekvivalens jellemzés), **7.3. Tétel**, **7.4. Kicserélési tétel**, **7.5. Következmény** |
| `LinearisAlgebra/Ch08_VegesDimenzios.lean` | 8. fejezet | `Bazis`, `MinimalisGenerator`, `MaximalisFuggetlen`, **8.2. Tétel**, **8.3. Tétel** (bázissá egészítés, generátorrendszer bázist tartalmaz, bázisok elemszáma), dimenzió, koordináták egyértelműsége |
| `LinearisAlgebra/Ch08b_DimenzioTetel.lean` | 8. fejezet (folytatás) | **8.5.**, **8.6.** (altér dimenziója), **8.7. alterek dimenziótétele**, **8.8–8.9.** vektorrendszer rangja, **8.10–8.12.** ekvivalens vektorrendszerek és elemi átalakításaik |
| `LinearisAlgebra/Ch09_MatrixRang.lean` | 9. fejezet (részben) | oszloprang, sorrang, **9.2. rangszámtétel** (sorrang = oszloprang), a mátrix rangja, **9.4./9.5. Következmény**, **9.6. Tétel**, **9.7. Kronecker–Capelli-tétel** |
| `LinearisAlgebra/Ch09b_Determinansrang.lean` | 9. fejezet (folytatás) | `aldeterminans`, `DeterminansRangja`, a **9.2. rangszámtétel** teljes alakja: `r_o(A) = r_s(A) = r_d(A)` |
| `LinearisAlgebra/Ch10_LinearisLekepezesek.lean` | 10. fejezet | `LinearisLekepezes`, `Mag`, `Kepter`, **10.2. Tétel**, **10.3. dimenziótétel**, **10.4. Következmény**, homogén rendszer megoldásalterének dimenziója, alaprendszer, **10.8–10.10.** izomorfia-tételek |
| `LinearisAlgebra/Ch11_MuveletekLekepezesekkel.lean` | 11. fejezet | **11.1–11.3. Tétel**, `Hom(U,V)` mint vektortér |
| `LinearisAlgebra/Ch12_LekepezesMatrixa.lean` | 12. fejezet | **12.1. Tétel**, `LekepezesMatrixa`, koordináták, koordináta-transzformáció, **12.3. Tétel** (összeg, skalárszoros, kompozíció mátrixa), **12.4. Tétel** (`Hom(U,V) ≅ T^{m×n}`, `dim = mn`) |
| `LinearisAlgebra/Ch13_Baziscsere.lean` | 13. fejezet | `AtteresMatrixa`, **13.2–13.5. Tétel** (áttérés inverze, koordináta-transzformáció, `PA' = AS`, hasonlóság), **13.6–13.8.** a leképezés rangja |
| `LinearisAlgebra/Ch14_Sajatertek.lean` | 14. fejezet | sajátérték, sajátvektor, `karPol` karakterisztikus polinom, **14.2. Tétel**, **14.3. Tétel** (hasonló mátrixok karakterisztikus polinomja), **14.4. Definíció** |
| `LinearisAlgebra/Ch14b_Diagonalizalhatosag.lean` | 14. fejezet (kiegészítés) | sajátaltér és altér volta, sajátérték ⟺ nemtriviális sajátaltér, **különböző sajátértékekhez tartozó sajátvektorok lineárisan függetlenek**, sajátbázis ⟺ a transzformáció mátrixa diagonális, `n` különböző sajátérték ⇒ diagonalizálható |
| `LinearisAlgebra/Ch15_BilinearisKvadratikus.lean` | 15. fejezet | `BilinearisLekepezes`, `bilinMatrixa`, koordinátás alak, **15.2. Tétel**, `KvadratikusAlak`, **15.4. Tétel** (polarizáció), báziscsere `B = SASᵀ`, rang, kanonikus alak, **15.7. alaptétel**, **15.8. Következmény** |
| `LinearisAlgebra/Ch16_ValosKvadratikus.lean` | 16. fejezet | valós kvadratikus alakok normálalakja, tehetetlenségi tétel, definitség |
| `LinearisAlgebra/Ch16b_Fominorok.lean` | 16.7–16.8 | főminorok, és a pozitív definitség jellemzése a főminorok pozitivitásával (Sylvester-kritérium; a jegyzet bizonyítás nélkül közli) |
| `LinearisAlgebra/Ch17_EuklidesziTerek.lean` | 17. fejezet | `BelsoSzorzat`, hossz, távolság, **17.3. Cauchy–Bunyakovszkij–Schwarz**, **17.4. háromszög-egyenlőtlenség**, szög, ortogonális és ortonormált rendszerek, ortogonális mátrixok, **Gram–Schmidt-ortogonalizáció**, ortonormált bázis létezése, izomorfia `ℝⁿ`-nel |
| `LinearisAlgebra/Peldak2_Kidolgozott.lean` | 4., 5., 14. fejezet | **kidolgozott gyakorlófeladatok** konkrét `ℚ` feletti mátrixokon: Cramer-szabály, inverzmátrix, karakterisztikus gyökök és sajátvektorok |
| `LinearisAlgebra/Ch18_Fotengelytetel.lean` | 18. fejezet | szimmetrikus transzformációk, **18.2.** (mátrix szimmetriája ortonormált bázisban), **18.4.** sajátvektorokból álló ortonormált bázis, **18.5.** ortogonális diagonalizálás, **18.6. főtengelytétel** |


### Lineáris algebra I. — a tematika pontjai és állapotuk

1. Komplex számok: kanonikus és trigonometrikus alak, Moivre-képlet, egységgyökök és
   primitív egységgyökök (számuk `φ(n)`) — `LinearisAlgebra/Tematika/LinearisAlgebraI.lean`.
2. `ℝⁿ` vektorai, lineáris kombináció — `LinearisAlgebra/Tematika/LinearisAlgebraI.lean`.
3. Belső szorzat, hossz, Cauchy–Schwarz- és háromszög-egyenlőtlenség, merőlegesség,
   merőleges vetítés — `Ch17`, `LinearisAlgebra/Tematika/LinearisAlgebraI.lean`.
4. Egyenesek, síkok, hipersíkok — `LinearisAlgebra/Tematika/LinearisAlgebraI.lean`.
5. Lineáris egyenletrendszerek, elemi átalakítások, Gauss-elimináció — `Ch05`, `Ch05b`.
6. Mátrixműveletek, inverz — `Ch02`, `Ch04`.
7. Determinánsok, kifejtési tétel, szorzástétel, Cramer-szabály — `Ch03`, `Ch04`, `Ch05`.
8. Homogén egyenletrendszerek, a megoldáshalmaz szerkezete — `Ch05`.
9. Vektorterek, alterek, generálás — `Ch06`.
10. Lineáris függetlenség, bázis, dimenzió — `Ch07`, `Ch08`.
11. Mátrixok rangja, rangszámtétel, Kronecker–Capelli-tétel — `Ch09`, `Ch09b`.
12. Lineáris leképezések, mag és képtér, dimenziótétel — `Ch10`.
13. Lineáris leképezés mátrixa, báziscsere, koordináta-transzformáció — `Ch12`, `Ch13`.
14. Sajátérték, sajátvektor, karakterisztikus polinom; sajátalterek, diagonalizálhatóság
    — `Ch14`, `Ch14b`.
15. Bilineáris leképezések és kvadratikus alakok — `Ch15`, `Ch16`; euklideszi terek,
    ortonormált bázis, főtengelytétel — `Ch17`, `Ch18`.
16. Alkalmazások: blokkmátrixok és számolás velük, LU-faktorizáció, Leontyev-mátrix, a
    determináns mint előjeles térfogat, merőleges vetítés (a háromszög nevezetes pontjai,
    Euler-vonal) — `LinearisAlgebra/Tematika/LinearisAlgebraI_Alkalmazasok.lean`.

---
