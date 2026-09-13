-- Leindler László: Analízis (Polygon, 2001), 3–8. fejezet
import Analizis.Ch03_ValosSzamok
import Analizis.Ch04a_SorozatokAlapok
import Analizis.Ch04b_SorozatokMuveletek
import Analizis.Ch04c_Konvergenciakriteriumok
import Analizis.Ch04d_Peldak
import Analizis.Ch04e_Szamsorok
import Analizis.Ch04f_NevezetesHatarertekek
import Analizis.Ch04g_LimeszSzuperior
import Analizis.Ch04h_Kiegeszitesek
import Analizis.Ch04i_PeldakMegjegyzesek
import Analizis.Ch05a_FuggvenyekAlapfogalmak
import Analizis.Ch05b_Folytonossag
import Analizis.Ch05c_ZartIntervallum
import Analizis.Ch05d_FuggvenyHatarertek
import Analizis.Ch05e_AlgebraiFuggvenyek
import Analizis.Ch05f_ExponencialisLogaritmus
import Analizis.Ch05g_TrigonometrikusFuggvenyek
import Analizis.Ch05h_VegtelenbenVettHatarertek
import Analizis.Ch05i_Kiegeszitesek
import Analizis.Ch06a_Differencialhatosag
import Analizis.Ch06b_ElemiDerivaltak
import Analizis.Ch06c_DifferencialFeloldali
import Analizis.Ch06d_TortkitevoLHospital
import Analizis.Ch07a_MagasabbrenduDerivaltak
import Analizis.Ch07b_TaylorFormula
import Analizis.Ch08a_MonotonitasSzelsoertek
import Analizis.Ch08b_KonvexsegInflexio
import Analizis.Ch08c_JeltartasSzelsoertek
import Analizis.Ch08d_MagasabbrenduInflexio
import Analizis.Ch08e_FuggvenyDiszkusszio

-- A Kalkulus I. előadás (MBLK37E) tematikája
import Analizis.Tematika.KalkulusI
import Analizis.Tematika.KalkulusI_Fuggvenytan

/-!
# Analízis — Leindler László *Analízis* (Polygon, 2001) című jegyzetének formalizálása

Ez a fájl a könyvtár **gyökérmodulja**: importálja az összes almodult, így egyetlen

```lean
import Analizis
```

sorral az egész formalizált analízis-anyag elérhető.

## Felépítés

* `Analizis.Ch03_*` — a valós számok (3. fejezet).
* `Analizis.Ch04*` — sorozatok, konvergencia, számsorok, limesz szuperior (4. fejezet).
* `Analizis.Ch05*` — függvények, folytonosság, függvényhatárérték, elemi függvények
  (5. fejezet).
* `Analizis.Ch06*` — differenciálhatóság, elemi deriváltak, L'Hospital-szabály (6. fejezet).
* `Analizis.Ch07*` — magasabbrendű deriváltak, Taylor-formula (7. fejezet).
* `Analizis.Ch08*` — monotonitás, szélsőérték, konvexség, inflexió, függvénydiszkusszió
  (8. fejezet, a jegyzet 126. oldaláig).
* `Analizis.Tematika.*` — a *Kalkulus I. előadás* (MBLK37E) tematikájának pontjai formális
  állításokként, a fenti modulokra építve.

## Alapelvek

* **Tankönyvhű megfogalmazás:** a definíciók a jegyzet saját fogalmai (pl. `Derivalt` a
  Cauchy-féle differenciálhányados), és külön híd-lemmák kötik őket a Mathlib megfelelőihez
  (`derivalt_iff_hasDerivAt`, …).
* **Tankönyvhű bizonyítások és magyar nyelvű dokumentáció**, a jegyzet számozásával.
* A könyvtár `sorry`-mentes és `axiom`-mentes.
-/
