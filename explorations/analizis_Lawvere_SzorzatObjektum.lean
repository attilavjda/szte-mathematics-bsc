import Mathlib
import Analizis.Ch04a_SorozatokAlapok
import Analizis.Ch05b_Folytonossag
import Analizis.Ch05i_Kiegeszitesek

/-!
# Átfedés Lawvere–Schanuel *Conceptual Mathematics* 1. session-jével

Lawvere és Schanuel könyvének 1. session-je („Galileo and multiplication of objects”)
az **objektumok szorzatáról** szól: `SPACE = PLANE × LINE`, a két „térkép”
(`shadow`, `level`) segítségével, továbbá a leképezések **kompozíciójáról**
(a madár röptének árnyék-, illetve szintvetülete), és arról a felismerésről, hogy
*a térbeli mozgás pontosan akkor folytonos, ha a két vetülete folytonos*.

Ez a modul azt gyűjti össze, **mi ebből az, ami a Leindler-jegyzet formalizált
anyagában is szerepel**, és a jegyzet saját fogalmaival (Cauchy-féle folytonosság,
sorozat-határérték, összetett függvény) bizonyítja az idézett rész állításait.

A megfeleltetés:

| Lawvere, Session 1 | Leindler-formalizáció |
| --- | --- |
| „map”, kompozíció (`shadow ∘ flight`) | `Ch05.OsszetettFv`, `Ch05.osszetettFv_eq_comp` |
| `SPACE = PLANE × LINE`, `shadow`, `level` | `arnyek`, `szint`, `galilei_univerzalis` |
| a röpte a két vetületéből visszaállítható | `galilei_egyertelmu` |
| „ha a vetületek folytonosak, a mozgás is az” | `folytonosSikba_iff` (`Ch05.CauchyFolytonos`-szal) |
| ugyanez sorozatokra | `hatarErtekSikban_iff` (`Ch04.HatarErtek`-kel) |
| `shadow ∘ flight` folytonos, ha `flight` az | `arnyek_comp_folytonos` |
| logikai példa: `A and B` | `es_univerzalis` |
| étkezés-példa: 3 × 4 lehetőség | `etkezesek_szama` |

Ami **nincs** átfedésben: a kategória, funktor, univerzális tulajdonság *általános*
fogalma; a Leindler-anyag mindezt csak konkrét esetekben (ℝ², sorozatok, összetett
függvény) használja.
-/

namespace Leindler.Lawvere

open Leindler

/-! ## 1. A szorzat univerzális tulajdonsága halmazokra (Lawvere „multiplication of objects”) -/

/-- Lawvere `shadow` leképezése: a `SPACE = PLANE × LINE` szorzat első vetítése. -/
def arnyek {P L : Type*} : P × L → P := Prod.fst

/-- Lawvere `level` leképezése: a `SPACE = PLANE × LINE` szorzat második vetítése. -/
def szint {P L : Type*} : P × L → L := Prod.snd

/-- **A szorzat univerzális tulajdonsága.** Ha adott egy `f : C → P` és egy `g : C → L`
leképezés, akkor pontosan egy olyan `h : C → P × L` van, amelynek az árnyéka `f`, a
szintje pedig `g`. Lawvere pontosan ezt a „három objektum, két leképezés” képet
nevezi az objektumok szorzatának. -/
theorem galilei_univerzalis {P L C : Type*} (f : C → P) (g : C → L) :
    ∃! h : C → P × L, arnyek ∘ h = f ∧ szint ∘ h = g := by
  refine ⟨fun c => (f c, g c), ⟨rfl, rfl⟩, ?_⟩
  rintro h ⟨h₁, h₂⟩
  funext c
  have e₁ : (h c).1 = f c := congrFun h₁ c
  have e₂ : (h c).2 = g c := congrFun h₂ c
  exact Prod.ext e₁ e₂

/-- **„A madár röpte visszaállítható a két filmből.”** Ha ismerjük az árnyék mozgását
(`TIME → PLANE`) és a szint mozgását (`TIME → LINE`), akkor a térbeli röpte
(`TIME → SPACE`) egyértelműen meghatározott. Ez a `galilei_univerzalis` speciális
esete `C = TIME`-mal. -/
theorem galilei_egyertelmu {Idő Sík Egyenes : Type*}
    (arnyekfilm : Idő → Sík) (szintfilm : Idő → Egyenes) :
    ∃! repules : Idő → Sík × Egyenes,
      arnyek ∘ repules = arnyekfilm ∧ szint ∘ repules = szintfilm :=
  galilei_univerzalis arnyekfilm szintfilm

/-- A szorzat univerzális tulajdonsága bijekcióként: a `C → P × L` leképezések
kölcsönösen egyértelműen megfelelnek a `(C → P) × (C → L)` leképezéspároknak. -/
def szorzatEkvivalencia (P L C : Type*) : (C → P × L) ≃ (C → P) × (C → L) where
  toFun h := (arnyek ∘ h, szint ∘ h)
  invFun fg c := (fg.1 c, fg.2 c)
  left_inv _ := rfl
  right_inv _ := rfl

/-! ## 2. Galilei folytonossági észrevétele a jegyzet folytonosság-fogalmával

Lawvere: „ha a shadow és a level mozgása folytonos, akkor a madár mozgása is az”.
A jegyzet 5.2.2. Definíciója (Cauchy-féle folytonosság) szó szerint átvihető a síkba
menő függvényekre, ha a `|f(x) − f(x₀)| < ε` feltételt a két koordinátára írjuk elő. -/

/-- A síkba menő `F : ℝ → ℝ × ℝ` függvény folytonossága az `x₀` pontban, a jegyzet
5.2.2. (Cauchy-féle) definíciójának mintájára: minden `ε > 0`-hoz van `δ > 0`, hogy
`|x − x₀| < δ` esetén *mindkét* koordináta eltérése kisebb `ε`-nál. -/
def FolytonosSikba (F : ℝ → ℝ × ℝ) (x₀ : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x : ℝ, |x - x₀| < δ →
    |(F x).1 - (F x₀).1| < ε ∧ |(F x).2 - (F x₀).2| < ε

/-- **Galilei észrevétele (folytonosság).** A síkba menő mozgás pontosan akkor
folytonos, ha az árnyéka és a szintje is folytonos (a jegyzet 5.2.2. definíciója
szerint). -/
theorem folytonosSikba_iff (F : ℝ → ℝ × ℝ) (x₀ : ℝ) :
    FolytonosSikba F x₀ ↔
      Ch05.CauchyFolytonos (fun x => (F x).1) x₀ ∧
        Ch05.CauchyFolytonos (fun x => (F x).2) x₀ := by
  constructor
  · intro h
    refine ⟨fun ε hε => ?_, fun ε hε => ?_⟩
    · obtain ⟨δ, hδ, hx⟩ := h ε hε
      exact ⟨δ, hδ, fun x hxδ => (hx x hxδ).1⟩
    · obtain ⟨δ, hδ, hx⟩ := h ε hε
      exact ⟨δ, hδ, fun x hxδ => (hx x hxδ).2⟩
  · rintro ⟨h₁, h₂⟩ ε hε
    obtain ⟨δ₁, hδ₁, hx₁⟩ := h₁ ε hε
    obtain ⟨δ₂, hδ₂, hx₂⟩ := h₂ ε hε
    refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, fun x hxδ => ?_⟩
    exact ⟨hx₁ x (lt_of_lt_of_le hxδ (min_le_left _ _)),
      hx₂ x (lt_of_lt_of_le hxδ (min_le_right _ _))⟩

/-- Az árnyék (első vetítés) és egy folytonos síkbeli mozgás kompozíciója folytonos:
Lawvere `shadow ∘ flight` képének megfelelője a jegyzet fogalmaival. -/
theorem arnyek_comp_folytonos {F : ℝ → ℝ × ℝ} {x₀ : ℝ} (hF : FolytonosSikba F x₀) :
    Ch05.CauchyFolytonos (arnyek ∘ F) x₀ :=
  ((folytonosSikba_iff F x₀).1 hF).1

/-- A szint (második vetítés) és egy folytonos síkbeli mozgás kompozíciója folytonos. -/
theorem szint_comp_folytonos {F : ℝ → ℝ × ℝ} {x₀ : ℝ} (hF : FolytonosSikba F x₀) :
    Ch05.CauchyFolytonos (szint ∘ F) x₀ :=
  ((folytonosSikba_iff F x₀).1 hF).2

/-! ## 3. Ugyanez sorozatokra (a jegyzet 4.2. határérték-fogalmával) -/

/-- Síkbeli pontsorozat határértéke, a jegyzet 4.2. (`Ch04.HatarErtek`) definíciójának
mintájára, koordinátánként. -/
def HatarErtekSikban (a : ℕ → ℝ × ℝ) (A : ℝ × ℝ) : Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n > N, |(a n).1 - A.1| < ε ∧ |(a n).2 - A.2| < ε

/-- **Koordinátánkénti konvergencia.** Egy síkbeli pontsorozat pontosan akkor tart
`A`-hoz, ha az árnyéka és a szintje külön-külön tart `A` megfelelő koordinátájához.
(Lawvere „két filmből visszaállítható a röpte” gondolatának sorozatos alakja.) -/
theorem hatarErtekSikban_iff (a : ℕ → ℝ × ℝ) (A : ℝ × ℝ) :
    HatarErtekSikban a A ↔
      Ch04.HatarErtek (fun n => (a n).1) A.1 ∧ Ch04.HatarErtek (fun n => (a n).2) A.2 := by
  constructor
  · intro h
    refine ⟨fun ε hε => ?_, fun ε hε => ?_⟩
    · obtain ⟨N, hN⟩ := h ε hε
      exact ⟨N, fun n hn => (hN n hn).1⟩
    · obtain ⟨N, hN⟩ := h ε hε
      exact ⟨N, fun n hn => (hN n hn).2⟩
  · rintro ⟨h₁, h₂⟩ ε hε
    obtain ⟨N₁, hN₁⟩ := h₁ ε hε
    obtain ⟨N₂, hN₂⟩ := h₂ ε hε
    refine ⟨max N₁ N₂, fun n hn => ?_⟩
    exact ⟨hN₁ n (lt_of_le_of_lt (le_max_left _ _) hn),
      hN₂ n (lt_of_le_of_lt (le_max_right _ _) hn)⟩

/-! ## 4. A kompozíció mint a jegyzet „összetett függvénye”

Lawvere első alapfogalma a leképezések kompozíciója; a jegyzetben ez az
**összetett függvény** (5.5.1. Definíció). A két fogalom azonos, és a jegyzet
5.5.2. Tétele éppen a kompozíció folytonosságát mondja ki. -/

/-- Az összetett függvény a jegyzetben *definíció szerint* a Lawvere-féle kompozíció. -/
theorem osszetett_eq_kompozicio (f g : ℝ → ℝ) : Ch05.OsszetettFv f g = f ∘ g := rfl

/-- A kompozíció asszociatív — Lawvere kategóriafogalmának egyik axiómája, a jegyzet
összetett függvényére kimondva. -/
theorem osszetett_asszociativ (f g h : ℝ → ℝ) :
    Ch05.OsszetettFv (Ch05.OsszetettFv f g) h = Ch05.OsszetettFv f (Ch05.OsszetettFv g h) :=
  rfl

/-- Az identitás a kompozíció egységeleme (Lawvere kategóriaaxiómáinak másik fele). -/
theorem osszetett_id (f : ℝ → ℝ) :
    Ch05.OsszetettFv f id = f ∧ Ch05.OsszetettFv id f = f := ⟨rfl, rfl⟩

/-! ## 5. A logikai példa: `A and B` -/

/-- **Lawvere logikai példája.** A `C`-ből az „`A` és `B`” állításba menő levezetések
ugyanazok, mint a `C`-ből `A`-ba és a `C`-ből `B`-be menő levezetések párjai: az
„és” ugyanaz a szorzatséma, mint a `SPACE = PLANE × LINE`. -/
theorem es_univerzalis (A B C : Prop) : (C → A ∧ B) ↔ (C → A) ∧ (C → B) :=
  ⟨fun h => ⟨fun c => (h c).1, fun c => (h c).2⟩, fun h c => ⟨h.1 c, h.2 c⟩⟩

/-! ## 6. Az étkezés-példa: a szorzat és a számok szorzása -/

/-- Első fogások: leves, tészta, saláta. -/
inductive Elofogas | leves | teszta | salata
  deriving DecidableEq, Fintype

/-- Második fogások: marha, borjú, csirke, hal. -/
inductive Fofogas | marha | borju | csirke | hal
  deriving DecidableEq, Fintype

/-- **Lawvere étkezés-példája.** Az „étkezések” objektuma a két fogáslista szorzata,
és az elemszáma a két elemszám szorzata: `3 · 4 = 12`. Ez az a pont, ahol az
objektumok szorzása a *számok* szorzásává válik. -/
theorem etkezesek_szama : Fintype.card (Elofogas × Fofogas) = 3 * 4 := by
  decide

end Leindler.Lawvere
