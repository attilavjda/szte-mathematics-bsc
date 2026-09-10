# A `Matrix.trace_units_conj'` tétel a két tankönyv anyagában

> **A kérdés.** Hol helyezkedik el a Mathlib alábbi tétele a Szabó-jegyzetben, benne
> van-e a könyvben vagy a könyvtár formalizációiban, van-e kalkulus- (Leindler-)
> megfelelője, és mi a közös mintázat kategóriaelméleti nézetben?
>
> ```lean
> theorem trace_units_conj' (M : (Matrix m m R)ˣ) (N : Matrix m m R) :
>     trace ((↑M⁻¹ : Matrix _ _ _) * N * (↑M : Matrix _ _ _)) = trace N
> ```

## 1. Rövid válasz

| Kérdés | Válasz |
|---|---|
| Benne van a Szabó-jegyzetben? | **Nem szó szerint.** A *nyom* (trace) fogalma a jegyzetben egyáltalán nem szerepel. |
| Van-e a jegyzetben megfelelője? | **Igen, ugyanaz a mintázat háromszor is:** 4.5. Tétel (determináns), 9.6. Tétel (rang), 14.3. Tétel (karakterisztikus polinom) — mind az `X⁻¹AX` alakú **hasonlóságra** (4.4. Definíció) vonatkozó invariancia. |
| Benne volt a könyvtár formalizációjában? | **A nyom eddig nem** (`nyom`/`trace` nem fordult elő). A hasonlósági invariancia három esete igen: `Ch04.hasonlo_det`, `Ch09.rang_hasonlo`, `Ch14.karPol_hasonlo`, `Ch14.karPol_fuggetlen_bazistol`. |
| Most már benne van? | **Igen**, a jelen menetben hozzáadott `LinearisAlgebra/LinearisAlgebra/Nyom_Konjugacio.lean` modulban, a jegyzet jelöléseivel és bizonyítási stílusában. |
| Kalkulus- (Leindler-) megfelelő? | **Igen:** a fixpont *multiplikátorának* (a fixpontbeli differenciálhányadosnak) az invarianciája koordinátacserére; a bizonyítás a 6.4.1. Tétel (láncszabály) kétszeri alkalmazása. Formalizálva: `Analizis/Analizis/Konjugacio_Invariancia.lean`. |
| Közös mintázat kategóriaelméletben? | **Igen:** „ciklikus mennyiség ⟹ konjugálásra invariáns ⟹ izomorfizmus-invariáns, tehát az *objektumhoz/transzformációhoz*, nem a *reprezentációhoz* tartozik”. Egyetlen lemmában kimondva tetszőleges monoidra: `ciklikus_konjugacio_invarians`. |

## 2. A Szabó-jegyzetbeli hely, pontosan

A Mathlib-tétel `M⁻¹ N M` kifejezése betű szerint a jegyzet

* **4.4. Definíció** *(hasonló mátrixok)*: `A ≈ B`, ha van olyan `X` nemelfajuló mátrix,
  hogy `B = X⁻¹AX` — formalizálva: `SzaboLinAlg.Ch04.Hasonlo`

fogalma. A jegyzet ezután minden fejezetben megkérdezi, hogy egy-egy mennyiség
túléli-e ezt az átírást:

| Jegyzetbeli hely | Állítás | Formalizált név |
|---|---|---|
| **4.5. Tétel** | hasonló mátrixok determinánsa egyenlő | `SzaboLinAlg.Ch04.hasonlo_det` |
| **9.6. Tétel** | hasonló mátrixok rangja egyenlő | `SzaboLinAlg.Ch09.rang_hasonlo` |
| **13.5. Következmény** | egy lineáris transzformáció két bázisbeli mátrixa hasonló | `SzaboLinAlg.Ch13.hasonlo_baziscsere` |
| **14.3. Tétel** | hasonló mátrixok karakterisztikus polinomja egyenlő | `SzaboLinAlg.Ch14.karPol_hasonlo` |
| **14.4. Definíció** | ezért a transzformáció karakterisztikus polinomja bázisfüggetlen | `SzaboLinAlg.Ch14.karPol_fuggetlen_bazistol` |
| *(hiányzott)* | **hasonló mátrixok nyoma egyenlő** | **`SzaboLinAlg.Nyom.nyom_hasonlo` (új)** |

A `trace_units_conj'` tehát a jegyzet szempontjából **a sor hiányzó negyedik tagja**:
ugyanaz a kérdés, csak a nyomra. A 4.4. Definíció `X⁻¹` írásmódja és a Mathlib `Mˣ`
egységcsoportos írásmódja között annyi a különbség, hogy a jegyzet az invertálhatóságot
`Inverze X Y` (`XY = YX = E`, 4.1. Definíció) alakban adja meg; ezért a modulban
mindkét változat szerepel:

```lean
theorem nyom_konjugalt {A X Y : Matrix' T n n} (hXY : Inverze X Y) :
    nyom (Y * A * X) = nyom A                        -- a jegyzet nyelvén: tr (X⁻¹AX) = tr A

theorem nyom_egysegkonjugalt (M : (Matrix' T n n)ˣ) (N : Matrix' T n n) :
    nyom ((↑M⁻¹ : Matrix' T n n) * N * (↑M : Matrix' T n n)) = nyom N   -- szó szerint a Mathlib-alak
```

A **14.1. Definíció** felől nézve a nyom nem is „idegen test”: másodrendű mátrixra
`f_A(x) = x² − (tr A)·x + |A|` (`SzaboLinAlg.Nyom.karPol_fin_two`), azaz a nyom a
karakterisztikus polinom egyik együtthatója, így a `nyom_hasonlo` a **14.3. Tétel**
együtthatónkénti következménye is. Ez magyarázza, miért „kellene” a jegyzetben
szerepelnie: a 14. fejezet gépezete már tartalmazza.

## 3. A bizonyítás magja — és miért ugyanaz mindegyik esetben

A jegyzet 4.5. Tételének bizonyítása:
`|X⁻¹AX| = |X⁻¹|·|A|·|X| = |A|·(|X⁻¹||X|) = |A|`.
Az új nyom-tételé (ugyanabban a stílusban):
`tr (X⁻¹AX) = tr (X·(X⁻¹A)) = tr ((XX⁻¹)A) = tr A`.

Mindkettőben egyetlen közös lépés dolgozik: a mennyiség **ciklikus**, azaz
`F(AB) = F(BA)`. A nyomnál ez az összegzési sorrend cseréje
(`nyom_szorzat_kommutal`), a determinánsnál a szorzástétel + `ab = ba`. Ezt a lépést
a modul egyszer, tetszőleges monoidra mondja ki:

```lean
theorem ciklikus_konjugacio_invarians {M S : Type*} [Monoid M] (F : M → S)
    (hciklikus : ∀ a b : M, F (a * b) = F (b * a)) (u : Mˣ) (x : M) :
    F ((↑u⁻¹ : M) * x * u) = F x
```

és a nyomra (`nyom_egysegkonjugalt`) és a determinánsra (`det_egysegkonjugalt`)
egyaránt alkalmazza. Ez a Mathlib-tétel „csontváza”.

## 4. A kalkulus- / Leindler-megfelelő

A Leindler-jegyzet nem beszél mátrixokról, de a `X⁻¹ · − · X` művelet analízisbeli
megfelelője jól ismert: a **koordinátacsere (átparaméterezés)**, `F = h ∘ f ∘ h⁻¹`.
A nyom egydimenziós megfelelője a derivált (`1 × 1`-es mátrix nyoma = maga a szám),
és a hasonlósági invariancia megfelelője:

> **Tétel** (`Leindler.Konjugacio.multiplikator_konjugalt_invarians`). Ha `x₀` az `f`
> fixpontja (`f(x₀) = x₀`), `f'(x₀) = c`, továbbá `h` koordinátacsere (`h⁻¹∘h = id`,
> `h∘h⁻¹ = id`) `h'(x₀) = p`, `(h⁻¹)'(h x₀) = q`, `p·q = 1`, akkor `h(x₀)` fixpontja a
> `F = h ∘ f ∘ h⁻¹` függvénynek, és `F'(h x₀) = p·c·q = c`.

A bizonyítás a **6.4.1. Tétel (láncszabály)** kétszeri alkalmazása, a jegyzet saját
`Derivalt` (6.1.3. Definíció) fogalmával; a `q = 1/p` alak a 6.5. pont
inverzfüggvény-tételéből jön (`multiplikator_konjugalt_invarians_reciprok`).

**A megfeleltetés pontról pontra:**

| Lineáris algebra (Szabó) | Kalkulus (Leindler) |
|---|---|
| `X` nemelfajuló mátrix (4.3.–4.4.) | `h` kölcsönösen egyértelmű, differenciálható koordinátacsere |
| `A ↦ X⁻¹AX` (bázisváltás) | `f ↦ h ∘ f ∘ h⁻¹` (átparaméterezés) |
| `(XY)⁻¹ = Y⁻¹X⁻¹`, `XX⁻¹ = E` | `(h∘g)⁻¹ = g⁻¹∘h⁻¹`, `h∘h⁻¹ = id` |
| szorzat mátrixa = mátrixok szorzata (12.6.) | láncszabály: deriváltak szorzódnak (6.4.1.) |
| `tr(X⁻¹AX) = tr A`, `|X⁻¹AX| = |A|` | `(h∘f∘h⁻¹)'(h x₀) = f'(x₀)` fixpontban |
| a transzformáció (nem a mátrix) invariánsa (14.4.) | a dinamika (nem a koordináták) invariánsa: vonzó/taszító fixpont (`vonzo_fixpont_invarians`) |

Egy figyelemre méltó részlet: az analízisbeli bizonyításban **pontosan ott** kell
kihasználni, hogy `x₀` fixpont, ahol a mátrixos bizonyításban azt, hogy a két oldalon
`X` és `X⁻¹` áll — a külső `h`-t az `f(x₀) = x₀` pontban kell deriválni, különben a
`p` és a `q = 1/p` nem esne ki. „Fixpont nélkül” a derivált nem invariáns, csak
konjugált (`f'(x₀)` helyett `h'(f x₀)·f'(x₀)·q`), ugyanúgy, ahogy egy nem négyzetes
`A`-nál `P⁻¹AS` esetén (13.4. Tétel) nincs nyominvariancia.

## 5. A közös mintázat kategóriaelméletben

A projekt `KATEGORIAELMELETI_MINTAZATOK.md` dokumentuma hat közös mintázatot sorol
fel; a jelen tétel egy hetediket ad hozzá, amely a 2. (funktor) és a 3. (univerzális
tulajdonság) mintázat közé illeszkedik:

> **Izomorfizmus-invariáns mennyiség.** Egy `V` objektum endomorfizmusai monoidot
> (egyobjektumú kategóriát) alkotnak; egy bázis megválasztása `V ≅ Tⁿ`
> izomorfizmus, a bázisváltás pedig konjugálás egy `Aut(V)`-beli elemmel. Egy
> `F : End V → S` mennyiség pontosan akkor „a transzformáció (az objektum)
> tulajdonsága”, és nem a reprezentációé, ha invariáns a konjugálásra, azaz ha
> az `Aut(V)`-hatás pályáin állandó — ehhez elég a **ciklikusság** `F(AB) = F(BA)`.

Két további réteg:

1. **Kategóriaelméleti nyom.** Szimmetrikus monoidális kategóriában (pl. véges
   dimenziós vektorterek a tenzorszorzattal) minden dualizálható objektum
   endomorfizmusához definiálható `tr(f) : I → I`, és a definícióból *azonnal*
   adódik a ciklikusság `tr(fg) = tr(gf)`, ebből pedig a `tr(g⁻¹fg) = tr(f)`
   konjugációs invariancia. A Mathlib-tétel ennek a mátrix-modellbeli esete.
2. **Funktorialitás.** A bázisválasztás mint funktor felől nézve az invariancia
   annak a kijelentése, hogy `F` **átmegy a hányadoson**: `End V / konjugálás → S`.
   Ez ugyanaz a gondolat, mint a 14.4. Definíció („a transzformáció karakterisztikus
   polinomja”) és a 13.7. Tétel („a leképezés rangja”) mögött; a modulban a
   `nyom_fuggetlen_bazistol` és a `transzformacioNyom` mondja ki a nyomra.

A kalkulusbeli megfelelő ugyanez egy másik kategóriában: az objektumok a
„fázisterek”, a morfizmusok a differenciálható leképezések, az izomorfizmusok a
koordinátacserék, és a multiplikátor `f ↦ f'(x₀)` az a mennyiség, amely a
konjugálási pályákon állandó — a láncszabály funktorialitása (`(g∘f)' = g'·f'`,
6.4.1. Tétel) miatt.

## 6. Amit a jelen menetben hozzáadtam

* `LinearisAlgebra/LinearisAlgebra/Nyom_Konjugacio.lean`
  — `ciklikus_konjugacio_invarians`, `ciklikus_konjugacio_invarians'`, `nyom`,
  `nyom_eq_trace`, `nyom_osszeg`, `nyom_skalarszoros`, `nyom_transzponalt`,
  `nyom_egysegmatrix`, `nyom_szorzat_kommutal`, `nyom_konjugalt`, `nyom_konjugalt'`,
  `nyom_hasonlo`, `nyom_egysegkonjugalt`, `det_egysegkonjugalt`,
  `nyom_fuggetlen_bazistol`, `transzformacioNyom`, `karPol_fin_two`.
* `Analizis/Analizis/Konjugacio_Invariancia.lean`
  — `Fixpont`, `Multiplikator`, `Koordinatacsere`, `konjugalt`, `fixpont_konjugalt`,
  `multiplikator_konjugalt_invarians`, `multiplikator_konjugalt_invarians_reciprok`,
  `vonzo_fixpont_invarians`, `multiplikator_unicitas`, `linearis_pelda`.
* Mindkét modul be van kötve a megfelelő gyökérmodulba, és `sorry` nélkül fordul.

---

### English summary

The Mathlib theorem `Matrix.trace_units_conj'` (`tr(M⁻¹NM) = tr N`) does **not**
appear in Szabó's *Bevezetés a lineáris algebrába*: the notion of trace is absent
from the book. Its `X⁻¹AX` shape, however, is literally Definition 4.4 (similar
matrices), and the book states the very same invariance pattern three times — for
the determinant (Thm 4.5), the rank (Thm 9.6) and the characteristic polynomial
(Thm 14.3, giving the basis-independent Definition 14.4). The library formalized
those three but not the trace; this run adds the missing fourth case in the book's
own notation and proof style, together with the general reason all four hold: a
cyclic quantity (`F(AB) = F(BA)`) is invariant under conjugation by a unit
(`ciklikus_konjugacio_invarians`, stated for an arbitrary monoid).

The calculus counterpart in Leindler's *Analízis* is the invariance of the
multiplier of a fixed point under a change of coordinates, `F = h ∘ f ∘ h⁻¹`,
proved by two applications of the chain rule (Thm 6.4.1); the fixed-point
hypothesis plays exactly the role that "the same `X` on both sides" plays in the
matrix proof. Categorically, all of these instantiate one pattern: a quantity on
`End V` descends to the isomorphism/conjugation quotient — i.e. it is an invariant
of the transformation rather than of its representation — and cyclicity, which the
categorical trace in a symmetric monoidal category satisfies by construction, is
the sufficient condition.
