# Lawvere–Schanuel, Session 1 („Galileo and multiplication of objects”) — átfedések a két könyvvel és a két formalizációval

*Overlaps between the Lawvere–Schanuel excerpt on multiplication (of objects) and the two
Hungarian textbooks / their Lean formalizations. Hungarian first, English summary at the end.*

## 0. Miről szól az idézett rész

A *Conceptual Mathematics* 1. session-je nem a számok szorzásáról szól, hanem az
**objektumok szorzásáról**. A fő gondolatok:

1. **Leképezés (map) és kompozíció.** A madár röpte egy leképezés `TIME → SPACE`;
   az `shadow` és `level` leképezésekkel komponálva két egyszerűbb mozgást kapunk.
2. **`SPACE = PLANE × LINE`.** A szorzat *nem* halmazként van definiálva, hanem a
   „három objektum, két leképezés” séma által: a `shadow : SPACE → PLANE` és
   `level : SPACE → LINE` vetítések olyanok, hogy egy pontot (vagy egy egész mozgást)
   a két vetülete egyértelműen meghatároz — ez az **univerzális tulajdonság**.
3. **Folytonosság.** Galilei észrevétele: ha a vetületek mozgása folytonos, akkor a
   térbeli mozgás is az.
4. **Ugyanez a séma másutt:** független választások (étkezés-példa, `3 × 4`),
   szakasz × körlap = henger, logika: `A és B`, végül a számok szorzása.

## 1. Átfedések a **Leindler: Analízis** anyaggal (`Analizis/`)

| Lawvere, Session 1 | Leindler / a formalizáció |
| --- | --- |
| „map”, függvény mint hozzárendelés | 5.1. Definíció, `Analizis/Analizis/Ch05a_FuggvenyekAlapfogalmak.lean` |
| kompozíció (`shadow ∘ flight`) | **összetett függvény**, 5.5.1. Definíció: `Ch05.OsszetettFv`, `Ch05.osszetettFv_eq_comp` |
| a kompozíció megőrzi a „jó” tulajdonságokat | 5.5.2. Tétel (`Ch05.osszetettFv_folytonos`), láncszabály 6.4. (`Ch06`) |
| `SPACE = PLANE × LINE`, `shadow`, `level` | `Lawvere.arnyek`, `Lawvere.szint`, `Lawvere.galilei_univerzalis` (új modul) |
| „a röpte a két filmből visszaállítható” | `Lawvere.galilei_egyertelmu`, `Lawvere.szorzatEkvivalencia` |
| Galilei folytonossági észrevétele | `Lawvere.folytonosSikba_iff` — a jegyzet 5.2.2. (Cauchy-féle) folytonosságával |
| ugyanez sorozatokra | `Lawvere.hatarErtekSikban_iff` — a jegyzet 4.2. `Ch04.HatarErtek` fogalmával |
| logikai példa (`A and B`) | `Lawvere.es_univerzalis` |
| étkezés-példa (`3 · 4 = 12`) | `Lawvere.etkezesek_szama` |

**Fontos különbség.** A Leindler-jegyzet (és így a formalizáció) egyváltozós valós
analízis: a szorzat *implicit* módon van jelen (rendezett párok, `ℝ²`, koordinátánkénti
konvergencia), de sehol nincs kimondva univerzális tulajdonságként. Az új
`Analizis/Analizis/Lawvere_SzorzatObjektum.lean` modul pontosan ezt a hiányzó, kimondott
kapcsolatot formalizálja — végig a **jegyzet saját** ε-δ definícióival, nem Mathlib-beli
topologikus fogalmakkal.

## 2. Átfedések a **Szabó: Bevezetés a lineáris algebrába** anyaggal (`LinearisAlgebra/`)

A lineáris algebra oldalán az átfedés lényegesen erősebb, mert ott a szorzat és a
vetítések explicit szerepet játszanak.

| Lawvere, Session 1 | Szabó / a formalizáció |
| --- | --- |
| szorzatobjektum, vetítések | `Lawvere.szorzatVektorter`, `Lawvere.arnyek_linearis`, `Lawvere.szint_linearis` (új modul) |
| univerzális tulajdonság | `Lawvere.szorzat_univerzalis_linearis`, `Lawvere.szorzat_lekepezespar` |
| `n`-szeres szorzat, `Tⁿ` | 6. fejezet `Ch06.tupleVektorter`; `Lawvere.tuple_vetites_linearis`, `Lawvere.tuple_univerzalis_linearis` |
| „a pont a vetületeiből visszaállítható” | bázis szerinti **koordináták**, 12.3.: `Ch12.koordinatai`, `Ch12.koordinatai_spec`, `Ch12.koordinatai_injective`; összefoglalva `Lawvere.koordinatak_univerzalis` |
| `V ≅ Tⁿ` (a tér *mint* szorzat) | 10.10. Tétel: `Ch10.izomorf_tuple` |
| kompozíció, kategóriaaxiómák | 10.7. Tétel: `Ch10.linearisLekepezes_comp`; `Lawvere.kompozicio_kategoria` |
| a kompozíció „funktoriális” képe | 12.6.: `Ch12.matrixa_comp` — a kompozíció mátrixa a mátrixok szorzata |
| szorzatból *induló* leképezések | 15.1. Definíció: `Ch15.BilinearisLekepezes`; `Lawvere.bilinearis_valtozonkent_linearis` |
| a *számok* szorzása mint leképezés | `Lawvere.szamszorzas_bilinearis` (`T × T → T`) |
| bázis univerzális tulajdonsága (duális oldal) | 12.1. Tétel: `Ch12.letezik_egyertelmu_lekepezes` — egy lineáris leképezést a bázisképek egyértelműen meghatároznak (ez a *koprodukt*/szabadság-tulajdonság, `Tⁿ` esetén egybeesik a szorzattal) |

### A „multiplication map” kifejezés két olvasata

* **Lawvere értelmében** (a részletben): a szorzat *vetítései* (`shadow`, `level`) —
  ezek a fenti táblázat első soraiban szerepelnek.
* **A tankönyvek szokásos értelmében**: a szorzás mint művelet-leképezés
  (`(a,b) ↦ a·b`, `(λ,v) ↦ λv`, `(A,B) ↦ AB`, `⟨u,v⟩`). Ezek mind a **szorzatból
  induló bilineáris** leképezések, és a jegyzet 15. fejezete, illetve a 2. fejezet
  mátrixszorzása pontosan ezekről szól. A `Lawvere.szamszorzas_bilinearis` és
  `Lawvere.bilinearis_valtozonkent_linearis` ezt a második olvasatot köti össze az
  elsővel: a szorzás *maga* egy szorzatobjektumon értelmezett leképezés.

## 3. Ami **nincs** átfedésben

* **Kategória, funktor, természetes transzformáció** — a két magyar jegyzet és a
  formalizációjuk egyetlen helyen sem használja ezeket a fogalmakat.
* **Az univerzális tulajdonság mint módszer.** A jegyzetek konkrét konstrukciókat
  adnak (rendezett `n`-esek, koordináták), és utólag bizonyítanak róluk állításokat;
  Lawvere fordítva jár el: a tulajdonság a definíció.
* **A geometriai/topologikus példák** (szakasz × körlap = henger, mozgás a térben)
  a Leindler-anyag egyváltozós keretén kívül esnek.
* **Az egyértelműség „izomorfizmus erejéig”** (a szorzatobjektum kategóriaelméleti
  unicitása) nincs formalizálva; a fenti `∃!`-állítások mindig egy *rögzített*
  konstrukció (`Prod`, `Fin n → T`) univerzális tulajdonságát mondják ki.

## 4. Az új Lean modulok

* `Analizis/Analizis/Lawvere_SzorzatObjektum.lean` — a szorzat univerzális
  tulajdonsága halmazokra, a Galilei-féle „két filmből visszaállítható a röpte”
  állítás, a koordinátánkénti folytonosság és konvergencia a jegyzet ε-δ
  definícióival, a kompozíció kategóriaaxiómái az összetett függvényre, a logikai
  „és” példa és az étkezés-példa (`3 · 4 = 12`).
* `LinearisAlgebra/LinearisAlgebra/Lawvere_SzorzatObjektum.lean` — a direkt szorzat
  mint a jegyzet szerinti vektortér, a vetítések linearitása, a szorzat univerzális
  tulajdonsága lineáris leképezésekre, a `Tⁿ`-re vonatkozó `n`-szeres változat, a
  bázis szerinti koordinátázás mint „shadow + level”, valamint a szorzás mint
  bilineáris leképezés.

Mindkét modul be van kötve a megfelelő gyökérmodulba, `sorry`- és `axiom`-mentes, és
a projektek `lake build`-je hibamentesen lefordítja őket.

---

## English summary

The excerpt is Session 1 of *Conceptual Mathematics*, whose subject is the **product of
objects** (`SPACE = PLANE × LINE`), presented through its two projection maps and the
universal property they satisfy, plus composition of maps and Galileo's observation that
a spatial motion is continuous exactly when its two projections are.

* **Overlap with Leindler (analysis):** the notion of map and of composite function
  (5.5.1) with its continuity theorem (5.5.2) and the chain rule; implicitly, ordered
  pairs and componentwise convergence/continuity. Formalized explicitly in the new module
  `Analizis/Analizis/Lawvere_SzorzatObjektum.lean`, stated with the book's own ε-δ
  definitions: the universal property of the product, unique reconstruction of the
  "flight" from its shadow and level films, componentwise continuity and convergence,
  associativity/identity laws of composition, the logical `A and B` example, and the
  meals example `3 · 4 = 12`.
* **Overlap with Szabó (linear algebra):** much stronger — direct products `U × V` and
  `Tⁿ` with their linear projections, coordinates with respect to a basis (12.3) as the
  "shadow + level" decomposition, `V ≅ Tⁿ` (10.10), composition of linear maps (10.7) and
  matrix multiplication as its matrix (12.6, functoriality), and bilinear maps (15.1) as
  maps *out of* a product — including number multiplication `T × T → T` itself. All of
  this is tied together in `LinearisAlgebra/LinearisAlgebra/Lawvere_SzorzatObjektum.lean`.
* **No overlap:** categories, functors, universal properties *as a general method*, the
  uniqueness of a product up to isomorphism, and the geometric/topological examples
  (cylinder = disk × segment, motion in space).
