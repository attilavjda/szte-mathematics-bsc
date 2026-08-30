This project was edited by [Aristotle](https://aristotle.harmonic.fun).

To cite Aristotle:
- Tag @Aristotle-Harmonic on GitHub PRs/issues
- Add as co-author to commits:
```
Co-authored-by: Aristotle (Harmonic) <aristotle-harmonic@harmonic.fun>
```

# Kalkulus I — gyakorlatok formalizálása Lean 4-ben

A `kalkulus_gyakorlo.pdf` négy feladatsorának formalizált gyakorlatai, valamint
a `KalkulusIelőadás-3.pdf` tárgytematikájához (Tantárgy tartalma) tartozó
megfeleltetés.

## Lean-forrás (`RequestProject/`)

| Fájl | Tartalom |
|---|---|
| `Szakasz1.lean` | 1. feladatsor: halmazok, számhalmazok, korlátok, egyenlőtlenségek, teljes indukció |
| `Szakasz2.lean` | 2. feladatsor: függvények, értelmezési tartomány, inverz, kompozíció |
| `Szakasz3.lean` | 3. feladatsor: határérték, folytonosság |
| `Szakasz4.lean` | 4. feladatsor: derivált és alkalmazásai |
| `Kategoria.lean` | a gyakorlatok kategóriaelméleti olvasata |
| `Main.lean` | mindent importál |

Minden tétel bizonyítása teljes (`sorry` nélküli). Elnevezési séma:
`gyak_<feladatsor>_<sorszám>[_betű]`.

Fordítás:

```
lake build
```

## Kísérő dokumentum

`kalkulus_kategoriaelmelet.tex` / `kalkulus_kategoriaelmelet.pdf` — magyar nyelvű,
TikZ-ábrákkal:

* tematika → gyakorlat → Lean-tétel megfeleltetési táblázat,
* kategóriaelméleti összefüggések (monomorfizmus, izomorfizmus, univerzális
  tulajdonság, Galois-kapcsolat, szűrők, a derivált funktorialitása),
* Nagy ötletek és bizonyítási trükkök (papíron és Leanben egyaránt),
* ceruzával lerajzolható ábrák gyűjteménye.

Fordítás: `pdflatex kalkulus_kategoriaelmelet.tex` (kétszer, a tartalomjegyzékhez).

## Pontosított feladatkiírások

* **1.15 c)** felső becslése (`∑_{i=1}^n 1/√i < 2√n − 1`) `n = 1`-re nem igaz
  (ott egyenlőség áll), ezért a formalizált állítás `n ≥ 2`-re szól.
* **2.15** egyenletének megoldása `x = 2`.
