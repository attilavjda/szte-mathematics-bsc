import Mathlib
import Analizis.Ch03_ValosSzamok
import Analizis.Ch05b_Folytonossag
import Analizis.Ch06a_Differencialhatosag
import Analizis.Alkalmazas_Folyoprofil

/-!
# Közös kategóriaelméleti mintázatok — az analízis oldala

Ez a modul **nem a Leindler-jegyzet része**, hanem a két formalizált tankönyv
(Leindler: *Analízis*, Szabó: *Bevezetés a lineáris algebrába*) **közös szerkezeti
mintázatait** gyűjti össze, a Lawvere–Schanuel-féle *Conceptual Mathematics* fogalmi
nyelvén, és mindegyiket egy hegyvidéki vízrajzi kérdésre alkalmazza.

Öt mintázat szerepel; mindegyiknek pontosan megfelel egy állítás a lineáris algebra
oldalán is (`LinearisAlgebra/LinearisAlgebra/Mintazatok_Kategoriaelmelet.lean`):

| # | mintázat | itt (analízis) | ott (lineáris algebra) |
|---|----------|----------------|------------------------|
| 1 | **kategória**: kompozíció, asszociativitás, egység, és a jó tulajdonság öröklődik | `folytonos_kategoria` | `linearis_kategoria` |
| 2 | **funktor**: a lokális „erősítés” szorzódik a kompozíció mentén | `erzekenyseg_szorzodik` (láncszabály, 6.4.1.) | `matrixa_comp` (12.6.) |
| 3 | **adjunkció / univerzális tulajdonság**: a *legkisebb* olyan objektum, amely lefed egy adathalmazt | `szupremum_adjunkcio` (3. fejezet, 10. axióma) | `generalt_adjunkcio` (6.10.) |
| 4 | **rendezés megőrzése (poset-funktor)**: monoton leképezések kompozíciója monoton | `csokkeno_kompozicio` (8.1.2.) | `nemnegativ_monoton` |
| 5 | **lax struktúra**: a megmaradás sérülésének mértéke kompozicionális (kociklus) | `veszteseg_kompozicio` | `veszteseg_szorzat` |
| 6 | **fixpont / mértani sor**: a rekurzió véges összeggé oldható fel | `veszteseg_iteralt` | `neumann_inverz` |

A mintázatok vízrajzi olvasata a `KATEGORIAELMELETI_MINTAZATOK.md` dokumentumban van
kifejtve. Minden bizonyítás a **jegyzet saját tételeire** épül (3. fejezet teljességi
axióma, 5.5.2. összetett függvény, 6.4.1. láncszabály, 8.1.2. monotonitás).
-/

namespace Leindler.Mintazatok

open Set Leindler Leindler.Ch03 Leindler.Ch05 Leindler.Ch06

/-! ## 1. mintázat: kategória — a kompozíció és amit megőriz

A Lawvere–Schanuel-féle első fogalom a *leképezés* és a *kompozíció*: az objektumok és a
köztük menő leképezések kategóriát alkotnak, ha a kompozíció asszociatív és van egység.
A jegyzetben ez az 5.5.1. összetett függvény és az 5.5.2. Tétel (a folytonosság öröklődik
a kompozícióra). -/

/-- A függvénykompozíció asszociatív, van egysége (`id`), és **a folytonosság megőrződik**
(5.5.2. Tétel): a folytonos függvények tehát kategóriát alkotnak. Vízrajzi olvasat: ha a
vízgyűjtő szakaszait folytonos átviteli függvények kötik össze, akkor akárhogyan bontjuk
szakaszokra a rendszert, ugyanazt a folytonos egészet kapjuk. -/
theorem folytonos_kategoria (f g h : ℝ → ℝ) (x₀ : ℝ) :
    ((fun x => f (g (h x))) = fun x => (fun y => f (g y)) (h x))
      ∧ ((fun x => f (id x)) = f ∧ (fun x => id (f x)) = f)
      ∧ (HeineFolytonos h x₀ → HeineFolytonos g (h x₀) →
          HeineFolytonos f (g (h x₀)) → HeineFolytonos (fun x => f (g (h x))) x₀) := by
  refine ⟨rfl, ⟨rfl, rfl⟩, fun hh hg hf => ?_⟩
  exact folytonos_osszetett (folytonos_osszetett hh hg) hf

/-! ## 2. mintázat: funktor — a lokális erősítés szorzódik

A derivált *funktor*: minden differenciálható függvényhez hozzárendel egy számot (a lokális
lineáris közelítést), és a kompozíciót szorzattá alakítja (`D(f∘g) = Df · Dg`), az
identitást pedig `1`-be viszi. Ez a jegyzet 6.4.1. láncszabálya. -/

/-- **Funktorialitás (6.4.1. láncszabály).** Egy háromtagú lánc érzékenysége a három
lokális érzékenység szorzata. Vízrajzi olvasat: ha a csapadék → vízállás → vízhozam →
hordalékhozam átalakítások mindegyike differenciálható, akkor a végponti válasz
érzékenysége a lokális érzékenységek **szorzata** — így egyetlen rosszul kalibrált
szakasz multiplikatívan rontja el a becslést, és a hiba forrása lokalizálható. -/
theorem erzekenyseg_szorzodik {f g h : ℝ → ℝ} {x₀ a b c : ℝ}
    (hh : Derivalt h x₀ c) (hg : Derivalt g (h x₀) b) (hf : Derivalt f (g (h x₀)) a) :
    Derivalt (fun x => f (g (h x))) x₀ (a * (b * c)) :=
  derivalt_osszetett (derivalt_osszetett hh hg) hf

/-- A funktor az identitást az egységbe viszi: az „átalakítás nélküli” szakasz
érzékenysége `1`. -/
theorem erzekenyseg_identitas (x₀ : ℝ) : Derivalt (fun x => x) x₀ 1 := derivalt_id x₀

/-! ## 3. mintázat: adjunkció — a *legkisebb* lefedő objektum

A „legkisebb felső korlát” és a „generált altér” ugyanannak a mintázatnak (bal adjungált,
univerzális tulajdonság) a két megjelenése: mindkettő a *legszűkebb* olyan objektum, amely
egy adott adathalmazt lefed, és ezt a `⟨lefedés⟩ ↔ ⟨összehasonlítás⟩` alakú ekvivalencia
fejezi ki. -/

/-- **Adjunkció-alak a 10. (teljességi) axiómából.** Nem üres, felülről korlátos `S`
esetén `sSup S ≤ b` **pontosan akkor**, ha `b` felső korlátja `S`-nek. Vízrajzi olvasat:
a mért árvízszintek `S` halmazát egy gátmagasság pontosan akkor „fedi le”, ha legalább
akkora, mint a szuprémum; a szuprémum tehát a *legolcsóbb biztonságos* magasság. -/
theorem szupremum_adjunkcio {S : Set ℝ} (hne : S.Nonempty) (hbdd : FelulrolKorlatos S)
    (b : ℝ) : sSup S ≤ b ↔ FelsoKorlat S b := by
  obtain ⟨M, hM⟩ := hbdd
  have hbdd' : BddAbove S := ⟨M, fun x hx => hM x hx⟩
  constructor
  · intro hb x hx
    exact (le_csSup hbdd' hx).trans hb
  · intro hb
    exact csSup_le hne hb

/-- A `szupremum_adjunkcio` közvetlen következménye: a szuprémum maga is biztonságos
magasság, és minden biztonságos magasság legalább akkora — azaz a „legkisebb elegendő
beavatkozás” egyértelműen létezik. -/
theorem legkisebb_biztonsagos_szint {S : Set ℝ} (hne : S.Nonempty)
    (hbdd : FelulrolKorlatos S) :
    FelsoKorlat S (sSup S) ∧ ∀ b, FelsoKorlat S b → sSup S ≤ b := by
  refine ⟨(szupremum_adjunkcio hne hbdd (sSup S)).1 le_rfl, fun b hb => ?_⟩
  exact (szupremum_adjunkcio hne hbdd b).2 hb

/-! ## 4. mintázat: rendezéstartó leképezés (poset-funktor)

Egy monoton függvény éppen egy funktor a `(ℝ, ≤)` poset-kategóriák között; a monoton
leképezések kompozíciója monoton, és a „csökkenő ∘ növekvő = csökkenő” előjelszabály a
funktorok összetételének felel meg. -/

/-- Az `I` halmazon növekedő függvény (a jegyzet 8.1. pontjának értelmében). -/
def NovekedoHalmazon (f : ℝ → ℝ) (I : Set ℝ) : Prop :=
  ∀ x ∈ I, ∀ y ∈ I, x ≤ y → f x ≤ f y

/-- Az `I` halmazon csökkenő függvény. -/
def CsokkenoHalmazon (f : ℝ → ℝ) (I : Set ℝ) : Prop :=
  ∀ x ∈ I, ∀ y ∈ I, x ≤ y → f y ≤ f x

/-- **Poset-funktorok kompozíciója.** Növekvő után csökkenő függvényt alkalmazva csökkenő
függvényt kapunk. Vízrajzi olvasat: ha a forrástól mért `s` úthossz növekvő függvénye a
vízgyűjtő terület, a magasság pedig annak csökkenő függvénye, akkor a magasság az úthossz
mentén csökken — a hosszmetszet monotonitása szakaszonként „összeragasztható”. -/
theorem csokkeno_kompozicio {f g : ℝ → ℝ} {I J : Set ℝ} (hmap : ∀ x ∈ I, g x ∈ J)
    (hg : NovekedoHalmazon g I) (hf : CsokkenoHalmazon f J) :
    CsokkenoHalmazon (fun x => f (g x)) I := by
  intro x hx y hy hxy
  exact hf (g x) (hmap x hx) (g y) (hmap y hy) (hg x hx y hy hxy)

/-- Növekvő függvények kompozíciója növekvő (ugyanaz a mintázat, előjelváltás nélkül). -/
theorem novekedo_kompozicio {f g : ℝ → ℝ} {I J : Set ℝ} (hmap : ∀ x ∈ I, g x ∈ J)
    (hg : NovekedoHalmazon g I) (hf : NovekedoHalmazon f J) :
    NovekedoHalmazon (fun x => f (g x)) I := by
  intro x hx y hy hxy
  exact hf (g x) (hmap x hx) (g y) (hmap y hy) (hg x hx y hy hxy)

/-- A `z(x) = H − a·x^p` hosszmetszet (`Leindler.Vizrajz.profil`) csökkenő a pozitív
félegyenesen (8.1.2. Tétel). -/
theorem profil_csokkeno {H a p : ℝ} (ha : 0 < a) (hp : 0 < p) :
    CsokkenoHalmazon (Leindler.Vizrajz.profil H a p) (Ioi (0 : ℝ)) := by
  intro u hu v _ huv
  have h : u ^ p ≤ v ^ p :=
    Real.rpow_le_rpow (le_of_lt (mem_Ioi.mp hu)) huv (le_of_lt hp)
  have : a * u ^ p ≤ a * v ^ p := mul_le_mul_of_nonneg_left h (le_of_lt ha)
  simp only [Leindler.Vizrajz.profil]
  linarith

/-- A mintázat alkalmazása a folyóprofilra: a hosszmetszet növekvő átparaméterezés után is
csökkenő marad. -/
theorem profil_atparameterezve_csokkeno {H a p : ℝ} {g : ℝ → ℝ} {I : Set ℝ}
    (ha : 0 < a) (hp : 0 < p) (hmap : ∀ x ∈ I, g x ∈ Ioi (0 : ℝ))
    (hg : NovekedoHalmazon g I) :
    CsokkenoHalmazon (fun x => Leindler.Vizrajz.profil H a p (g x)) I :=
  csokkeno_kompozicio (J := Ioi (0 : ℝ)) hmap hg (profil_csokkeno ha hp)

/-! ## 5. mintázat: lax struktúra — a megmaradás sérülése kociklus

Ha egy szakasz a beérkező víznek a `c`-szeresét adja tovább, akkor a *veszteség* `1 − c`.
Két szakasz egymás utáni alkalmazásakor a veszteségek nem egyszerűen összeadódnak: a
későbbi szakasz veszteségéhez a korábbi veszteség *átvitellel súlyozva* járul hozzá. Ez
pontosan a lineáris algebra oldalán bizonyított `veszteseg_szorzat` egydimenziós esete, és
azt jelenti, hogy a mért mérleghiány szakaszonkénti járulékokra bontható — *a szivárgás
lokalizálható*. -/

/-- Egy szakasz vesztesége, ha az átbocsátási hányada `c`. -/
def veszteseg (c : ℝ) : ℝ := 1 - c

/-- **Kociklus-azonosság (lax mintázat).** Két egymás utáni szakasz együttes vesztesége a
második szakasz saját vesztesége plusz az első szakasz vesztesége, a második szakasz
átbocsátásával súlyozva. -/
theorem veszteseg_kompozicio (c d : ℝ) : veszteseg (d * c) = veszteseg d + d * veszteseg c := by
  simp only [veszteseg]; ring

/-- A szakasz pontosan akkor vízmegőrző, ha nincs vesztesége. -/
theorem veszteseg_nulla_iff (c : ℝ) : veszteseg c = 0 ↔ c = 1 := by
  simp only [veszteseg, sub_eq_zero]
  exact eq_comm

/-- A vízmegőrző szakaszok zártak a kompozícióra (monoid) — a lax struktúra „szigorú”
része. -/
theorem megorzo_kompozicio {c d : ℝ} (hc : veszteseg c = 0) (hd : veszteseg d = 0) :
    veszteseg (d * c) = 0 := by
  rw [veszteseg_kompozicio, hc, hd]; ring

/-! ## 6. mintázat: fixpont és mértani sor

Az `a = r + c·a` alakú (lefolyás-akkumulációs) rekurziót véges összeg oldja fel; ez
az analízis oldalán a mértani sor, a lineáris algebra oldalán a Neumann-sor
(`neumann_inverz`). -/

/-- **Teleszkóp-azonosság: az `n` szakaszon átvitt víz és az összes veszteség.**
`1 − cⁿ = ∑_{i<n} cⁱ·(1−c)`: a teljes veszteség a szakaszonkénti veszteségek átvitellel
súlyozott összege — ugyanaz a mértani sor, amely a hálózatos esetben `(I − M)` inverzét
adja. -/
theorem veszteseg_iteralt (c : ℝ) (n : ℕ) :
    veszteseg (c ^ n) = ∑ i ∈ Finset.range n, c ^ i * veszteseg c := by
  induction n with
  | zero => simp [veszteseg]
  | succ k ih =>
      rw [Finset.sum_range_succ, ← ih]
      simp only [veszteseg]
      ring

/-- **Fixpont-alak.** Ha `c ≠ 1`, akkor az `a = r + c·a` „akkumulációs egyenletnek”
pontosan egy megoldása van, `a = r/(1−c)` — az egydimenziós Leontyev-egyenlet
(lefolyás-akkumuláció). -/
theorem akkumulacio_egyertelmu {c r : ℝ} (hc : c ≠ 1) :
    ∃! a : ℝ, a = r + c * a := by
  have h1 : (1 : ℝ) - c ≠ 0 := sub_ne_zero.mpr (Ne.symm hc)
  refine ⟨r / (1 - c), ?_, ?_⟩
  · field_simp
    ring
  · intro a ha
    have hra : (1 - c) * a = r := by linarith [ha]
    field_simp
    linarith [hra]

end Leindler.Mintazatok
