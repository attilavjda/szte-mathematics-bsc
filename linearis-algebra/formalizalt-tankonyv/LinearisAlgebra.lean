-- Szabó László: Bevezetés a lineáris algebrába (Polygon jegyzettár, 2006), 1–18. fejezet
import LinearisAlgebra.Ch01_Bevezetes
import LinearisAlgebra.Ch02_Matrixok
import LinearisAlgebra.Ch03_Determinans
import LinearisAlgebra.Ch03b_DualitasVandermonde
import LinearisAlgebra.Ch03c_Laplace
import LinearisAlgebra.Ch04_Inverzmatrix
import LinearisAlgebra.Ch05_Egyenletrendszerek
import LinearisAlgebra.Ch05b_GaussElimination
import LinearisAlgebra.Ch06_Vektorterek
import LinearisAlgebra.Ch07_LinearisFuggetlenseg
import LinearisAlgebra.Ch08_VegesDimenzios
import LinearisAlgebra.Ch08b_DimenzioTetel
import LinearisAlgebra.Ch09_MatrixRang
import LinearisAlgebra.Ch09b_Determinansrang
import LinearisAlgebra.Ch10_LinearisLekepezesek
import LinearisAlgebra.Ch11_MuveletekLekepezesekkel
import LinearisAlgebra.Ch12_LekepezesMatrixa
import LinearisAlgebra.Ch13_Baziscsere
import LinearisAlgebra.Ch14_Sajatertek
import LinearisAlgebra.Ch14b_Diagonalizalhatosag
import LinearisAlgebra.Ch15_BilinearisKvadratikus
import LinearisAlgebra.Ch16_ValosKvadratikus
import LinearisAlgebra.Ch16b_Fominorok
import LinearisAlgebra.Ch17_EuklidesziTerek
import LinearisAlgebra.Ch18_Fotengelytetel
import LinearisAlgebra.Peldak
import LinearisAlgebra.Peldak2_Kidolgozott

-- A Lineáris algebra I. előadás (MBLK15E) tematikája
import LinearisAlgebra.Tematika.LinearisAlgebraI
import LinearisAlgebra.Tematika.LinearisAlgebraI_Alkalmazasok

/-!
# Lineáris algebra — Szabó László *Bevezetés a lineáris algebrába* (2006) formalizálása

Ez a fájl a könyvtár **gyökérmodulja**: importálja az összes almodult, így egyetlen

```lean
import LinearisAlgebra
```

sorral az egész formalizált lineáris algebra anyag elérhető.

## Felépítés

* `LinearisAlgebra.Ch01`–`Ch05` — alapfogalmak, mátrixok, determináns (Laplace-kifejtés,
  Vandermonde-determináns), inverzmátrix, lineáris egyenletrendszerek (Cramer-szabály,
  Gauss-elimináció).
* `LinearisAlgebra.Ch06`–`Ch09` — vektorterek, lineáris függetlenség, véges dimenziós terek,
  dimenziótétel, mátrixrang és determinánsrang.
* `LinearisAlgebra.Ch10`–`Ch14` — lineáris leképezések, műveletek leképezésekkel, a leképezés
  mátrixa, báziscsere, sajátérték és diagonalizálhatóság.
* `LinearisAlgebra.Ch15`–`Ch18` — bilineáris és kvadratikus alakok, valós kvadratikus alakok,
  főminorok, euklideszi terek, főtengelytétel.
* `LinearisAlgebra.Peldak`, `LinearisAlgebra.Peldak2_Kidolgozott` — a jegyzet kidolgozott
  példái konkrét mátrixokon.
* `LinearisAlgebra.Tematika.*` — a *Lineáris algebra I.* (MBLK15E) tematikájának pontjai
  formális állításokként, a fenti modulokra építve.

## Alapelvek

* **Tankönyvhű megfogalmazás:** a definíciók a jegyzet saját fogalmai (pl. `det'` a jegyzet
  rekurzív determináns-definíciója), és külön híd-lemmák kötik őket a Mathlib megfelelőihez
  (`det'_eq_det`, …).
* **Tankönyvhű bizonyítások és magyar nyelvű dokumentáció**, a jegyzet számozásával.
* A könyvtár `sorry`-mentes és `axiom`-mentes.
-/
