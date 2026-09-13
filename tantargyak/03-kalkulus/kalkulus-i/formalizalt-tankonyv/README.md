# Analízis — Leindler László *Analízis* (Polygon, 2001) formalizálása

Ez a könyvtár **önálló, külön fordítható Lean 4 + Mathlib projekt**: Leindler László
*Analízis* (Polygon, 2001) című jegyzetének **3–8. fejezetét** (az 5–126. oldalt, a
függvénydiszkusszió végéig) formalizálja, valamint a rá épülő **Kalkulus I. előadás
(MBLK37E)** tantárgyi tematikát. Az integrálszámítás (a jegyzet 9. fejezetétől) — a
feladatkiírásnak megfelelően — nem része az anyagnak.

A lineáris algebra anyag ettől függetlenül, a szomszédos `LinearisAlgebra/` projektben
található.

## Fordítás és futtatás

```bash
cd Analizis
lake exe cache get     # a Mathlib előre lefordított változatának letöltése
lake build             # a teljes könyvtár fordítása (ellenőrzése)
```

A `lake build` egyben az anyag **ellenőrzése** is: minden definíció és tétel átmegy a Lean
magján. A könyvtár `sorry`-mentes, `axiom`-mentes; a fordítás hibamentesen és
figyelmeztetés nélkül fut le.

Egyetlen

```lean
import Analizis
```

sorral az egész formalizált anyag elérhető (a gyökérmodul: `Analizis.lean`).

## Terjedelem

* 32 modul, kb. 10 500 sor, 600-nál több tétel és lemma.

## Alapelvek

* **Tankönyvhű (faithful) megfogalmazás:** a definíciók a jegyzet saját fogalmai (pl. a
  `Derivalt` a *Cauchy-féle* differenciálhányados-definíció, nem a Mathlib `HasDerivAt`-je),
  és külön híd-lemmák kötik össze őket a Mathlib fogalmaival (`derivalt_iff_hasDerivAt`, …).
* **Tankönyvhű bizonyítások:** ahol lehet, a bizonyítás a könyv gondolatmenetét követi.
* **Magyar nyelvű dokumentáció**, a jegyzet számozásával (pl. „**8.4.1. Tétel.**”).

### Elkészült modulok

| Modul | Könyvbeli anyag | Fő tartalom |
|---|---|---|
| `Analizis/Ch03_ValosSzamok.lean` | 3. fejezet | a valós számok 1–10. axiómája, abszolút érték, Arkhimédész-tulajdonság, binomiális tétel, intervallumok |
| `Analizis/Ch04a_SorozatokAlapok.lean` | 4.1–4.5 | `Sorozat`, `HatarErtek`, `Konvergens`, a határérték egyértelműsége, Bernoulli-egyenlőtlenség |
| `Analizis/Ch04b_SorozatokMuveletek.lean` | 4.6–4.7 | határérték és műveletek, rendőrelv, `+∞`-be divergálás |
| `Analizis/Ch04c_Konvergenciakriteriumok.lean` | 4.14–4.17 | torlódási pont, monoton korlátos sorozat, Bolzano–Weierstrass, Cauchy-kritérium, az `e` szám, valós számsorok alapfogalmai, geometriai sor |
| `Analizis/Ch04d_Peldak.lean` | 4.13 | a 4.13. pont feladatai: gyöktelenítés, `∞/∞` típusú határértékek, teleszkopikus szorzatok, négyzetösszeg, rendőrelv |
| `Analizis/Ch04e_Szamsorok.lean` | 4.17 (folytatás) | **4.17.5.** (a konvergencia szükséges feltétele), **4.17.6.** Cauchy-féle konvergenciakritérium sorokra, **4.17.7.** a geometriai sor divergens esete, **4.17.8.** a harmonikus sor divergenciája |
| `Analizis/Ch04f_NevezetesHatarertekek.lean` | 4.7 (folytatás) | **4.7.3.** a `qⁿ` sorozat divergens esete, **4.7.5.** oszcilláló sorozat, **4.7.6–4.7.9.** példák (`ⁿ√a → 1`, `aⁿ/n! → 0`, `ⁿ√n → 1`) |
| `Analizis/Ch04g_LimeszSzuperior.lean` | 4.14.10–4.15.3 | legnagyobb és legkisebb torlódási pont, **4.14.12.** limesz szuperior/inferior, **4.14.13.** konvergencia ⟺ `lim sup = lim inf`, a szubadditivitási egyenlőtlenségek és ellenpélda |
| `Analizis/Ch04h_Kiegeszitesek.lean` | 4.6, 4.8, 4.9 | **4.6.3., 4.6.5., 4.6.6.** a konvergencia egyenértékű megfogalmazásai, **4.8.6.** átrendezett sorozat, **4.8.8–4.8.11.** fésűs egyesítés és következményei, **4.9.3.** polinomhányados határértéke |
| `Analizis/Ch04i_PeldakMegjegyzesek.lean` | 4.2–4.14 | a 4. fejezet számozott *példái és megjegyzései*: **4.2.2–4.2.3.**, **4.3.2.**, **4.4.2.**, **4.5.2.**, **4.6.9–4.6.10.**, **4.8.7.**, **4.9.2.**, **4.10.2.**, **4.11.2.**, **4.12.2.**, **4.14.7.**, **4.14.11.** |
| `Analizis/Ch05a_FuggvenyekAlapfogalmak.lean` | 5.1 | korlátosság, felső/alsó határ, szélső értékek, monotonitás, húr, konvex/konkáv görbe, 5.1.8. Tétel, inflexiós pont, páros/páratlan függvény |
| `Analizis/Ch05b_Folytonossag.lean` | 5.2–5.6 | Heine- és Cauchy-féle folytonosság és ekvivalenciájuk, féloldali folytonosság, egyenletes folytonosság, műveletek, összetett és inverz függvény |
| `Analizis/Ch05c_ZartIntervallum.lean` | 5.14 | korlátosság, Weierstrass-tétel, Heine-tétel, Bolzano–Darboux-tétel |
| `Analizis/Ch05d_FuggvenyHatarertek.lean` | 5.15–5.19 | Heine/Cauchy-féle függvényhatárérték és ekvivalenciájuk, műveletek, féloldali határértékek, szakadási helyek, végtelen határértékek |
| `Analizis/Ch05e_AlgebraiFuggvenyek.lean` | 5.7 | polinom- és racionális törtfüggvények, hatvány-, gyök- és törtkitevős hatványfüggvények, algebrai függvények |
| `Analizis/Ch05f_ExponencialisLogaritmus.lean` | 5.8–5.10 | exponenciális függvény (racionális közelítés, azonosságok, folytonosság), logaritmusfüggvény, irracionális kitevőjű hatványfüggvény |
| `Analizis/Ch05g_TrigonometrikusFuggvenyek.lean` | 5.11–5.13 | periodicitás, trigonometrikus polinom, **5.11.2** (`sin`, `cos` folytonossága), **5.11.3** (`tg`, `ctg`), ciklometrikus függvények (`arcsin`, `arccos`, `arctg`, `arcctg`), **5.12.1** transzcendens és **5.13.1** elemi függvények, hiperbolikus függvények |
| `Analizis/Ch05h_VegtelenbenVettHatarertek.lean` | 5.18–5.19 | a végtelenben vett határérték Heine-féle definíciói és ekvivalenciájuk a Cauchy-féle definíciókkal, a mínusz végtelenben vett határérték, **5.19.3.** `lim_{|x|→∞} (1+1/x)^x = e` |
| `Analizis/Ch05i_Kiegeszitesek.lean` | 5.1, 5.3, 5.5, 5.7, 5.15, 5.16 | **5.1.9.** görbe inflexiós pontja, **5.3.6.** féloldali folytonosság Heine-féle alakja, **5.5.1.** összetett függvény, **5.7.4–5.7.6.** racionális egész és törtfüggvények, **5.15.4.** féloldali határérték Heine-féle alakja, **5.16.4.** meg nem szüntethető szakadás |
| `Analizis/Ch06a_Differencialhatosag.lean` | 6.1–6.2, 6.10 | `kulonbsegiHanyados`, `Derivalt`, differenciálhatóság ⇒ folytonosság, műveleti szabályok, láncszabály, Rolle-, Lagrange- és Cauchy-féle középértéktétel |
| `Analizis/Ch06b_ElemiDerivaltak.lean` | 6.3–6.9, 6.11 | hatvány-, trigonometrikus, ciklometrikus, logaritmus-, exponenciális és hiperbolikus függvények deriváltjai, inverz függvény deriváltja, L'Hospital-szabály |
| `Analizis/Ch06c_DifferencialFeloldali.lean` | 6.1.4–6.2.2, 6.6.4, 6.10.5 | a differenciál, féloldali differenciálhányadosok és a **6.1.6. Tétel**, zárt intervallumon differenciálható és folytonosan differenciálható függvény, `(arcctg x)'`, **6.10.5.** `f' = g' ⇒ f = g + C` |
| `Analizis/Ch06d_TortkitevoLHospital.lean` | 6.8.3–6.8.4, 6.11.3 | páratlan nevezőjű törtkitevős hatvány és deriváltja, a **l'Hospital-szabály** a `±∞`-ben |
| `Analizis/Ch07a_MagasabbrenduDerivaltak.lean` | 7.0–7.1 | `nDerivalt` (magasabbrendű differenciálhányados), `NszerDifferencialhato`, kapcsolat a Mathlib `iteratedDeriv`-jével, összeg deriváltja, **7.1.1. Leibniz-formula** |
| `Analizis/Ch07b_TaylorFormula.lean` | 7.2, 8.5.2 | Taylor-polinom, Lagrange-féle maradéktag, **7.2.1. Taylor-formula**, Maclaurin-formula, **8.5.2. Tétel** (szélsőérték és monotonitás magasabbrendű deriváltakkal) |
| `Analizis/Ch08a_MonotonitasSzelsoertek.lean` | 8.1–8.5 | 8.1.1, 8.1.2, 8.2.1, **8.3.1 (Darboux-tétel)**, 8.3.2, 8.4.1, 8.5.1 |
| `Analizis/Ch08b_KonvexsegInflexio.lean` | 8.6–8.8 | **8.6.1** (konvexitás ⟺ `f'' ≥ 0`), **8.7.1**, **8.7.2**, példa, valamint a 8.8. függvénydiszkussziós séma |
| `Analizis/Ch08c_JeltartasSzelsoertek.lean` | 8.2.2, 8.4.2–8.4.3 | pontbeli növekedés folytonos derivált mellett, a derivált előjelváltása és a szigorú szélső érték szükséges és elegendő feltétele |
| `Analizis/Ch08e_FuggvenyDiszkusszio.lean` | 8.8 | a **függvénydiszkusszió sémája kidolgozva** az `f(x) = x³ - 3x` függvényre: folytonosság, értékkészlet, zérushelyek, páratlanság, monotonitási intervallumok, szigorú helyi szélsőértékek, konvex/konkáv szakaszok, inflexiós pont, a `±∞`-beli viselkedés |
| `Analizis/Ch08d_MagasabbrenduInflexio.lean` | 8.7.3 | inflexiós pont magasabbrendű differenciálhányadosokkal (`f⁽ⁱ⁾(x₀) = 0`, `i ≤ 2k`, `f⁽²ᵏ⁺¹⁾(x₀) ≠ 0`) |


### Kalkulus I. — a tematika pontjai és állapotuk

1. A valós számok teste, teljességi axióma — `Ch03`.
2. Teljes indukció, nevezetes egyenlőtlenségek (Bernoulli, számtani-mértani, Cauchy–Schwarz)
   — `Analizis/Tematika/KalkulusI.lean`.
3. Elemi függvények és inverzeik, függvénytranszformációk — `Ch05e`, `Ch05f`, `Ch05g`,
   `Analizis/Tematika/KalkulusI.lean`.
4. Függvényhatárérték, folytonosság — `Ch05b`, `Ch05d`.
5. Kompakt intervallumon folytonos függvények (Weierstrass, Bolzano, Heine) — `Ch05c`.
6. Pontbeli derivált, érintő, láncszabály, implicit deriválás — `Ch06a`, `Ch06b`.
7. Középértéktételek (Rolle, Lagrange, Cauchy) — `Ch06a`.
8. Monotonitás és derivált, lokális szélsőérték (első/második derivált teszt) — `Ch08a`;
   intervallumon vett (abszolút) szélsőértékek — `Analizis/Tematika/KalkulusI.lean`.
9. Konvexitás és a második derivált, inflexió, grafikonvázolás — `Ch08b`.
10. L'Hospital-szabály — `Ch06b`.
11. Magasabbrendű deriváltak, Leibniz-formula, Taylor-formula, magasabbrendű
    szélsőérték-kritérium — `Ch07a`, `Ch07b`.
12. Értelmezési tartomány, értékkészlet, inverz és összetett függvény, szimmetriák;
    elemi határérték-számítási technikák (nevezetes határértékek, racionális
    törtfüggvény a végtelenben, gyöktelenítés) —
    `Analizis/Tematika/KalkulusI_Fuggvenytan.lean`.

