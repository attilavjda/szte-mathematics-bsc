import LinearisAlgebra.Ch12_LekepezesMatrixa
import LinearisAlgebra.Ch15_BilinearisKvadratikus

/-!
# Átfedés Lawvere–Schanuel *Conceptual Mathematics* 1. session-jével

Lawvere és Schanuel könyvének 1. session-je („Galileo and multiplication of objects”)
az **objektumok szorzatáról** szól: a `SPACE = PLANE × LINE` egyenlőség értelmét a két
vetítés (`shadow`, `level`) adja meg, azzal a tulajdonsággal, hogy egy tetszőleges
objektumból a szorzatba menő leképezések ugyanazok, mint a vetületekbe menő
leképezéspárok.

Ez a modul azt mutatja meg, **hol jelenik meg ugyanez a séma a lineáris algebra
jegyzet formalizált anyagában**, a jegyzet saját fogalmaival (`Vektorter`,
`LinearisLekepezes`, `Bazis`, `BilinearisLekepezes`) kimondva és bizonyítva.

| Lawvere, Session 1 | Szabó-jegyzet formalizációja |
| --- | --- |
| `SPACE = PLANE × LINE`, `shadow`, `level` | `szorzatVektorter`, `arnyek_linearis`, `szint_linearis` |
| a szorzat univerzális tulajdonsága | `szorzat_univerzalis_linearis` |
| `n`-szeres szorzat (`Tⁿ`) vetítései | `tuple_univerzalis_linearis` |
| „a pont a vetületeiből visszaállítható” | `koordinatak_univerzalis` (bázis szerinti koordináták, 12.3.) |
| leképezések kompozíciója | `Ch10.linearisLekepezes_comp`, `Ch12.matrixa_comp` |
| a *számok* szorzása mint leképezés `T × T → T` | `szamszorzas_bilinearis` |
| szorzatból induló leképezések | `BilinearisLekepezes` (15.1. Definíció) |

Ami **nincs** átfedésben: a kategória, funktor és univerzális tulajdonság általános
fogalma — a jegyzet ezeket csak konkrét alakban (direkt szorzat, koordinátázás,
mátrixszorzás mint kompozíció) használja.
-/

namespace SzaboLinAlg.Lawvere

open scoped BigOperators
open SzaboLinAlg.Ch06 SzaboLinAlg.Ch07 SzaboLinAlg.Ch08 SzaboLinAlg.Ch10
  SzaboLinAlg.Ch12 SzaboLinAlg.Ch15

variable {T : Type*} [Field T] {U V W : Type*} [AddCommGroup U] [Module T U]
  [AddCommGroup V] [Module T V] [AddCommGroup W] [Module T W]

/-! ## 1. Két vektortér szorzata (Lawvere `SPACE = PLANE × LINE`-ja) -/

/-- A `U × V` direkt szorzat a jegyzet 6.1. Definíciója értelmében is vektortér. -/
def szorzatVektorter (T : Type*) [Field T] (U V : Type*) [AddCommGroup U] [Module T U]
    [AddCommGroup V] [Module T V] : Vektorter T (U × V) :=
  modulVektorter T (U × V)

/-- Lawvere `shadow` leképezése lineáris: az első vetítés `U × V → U`. -/
theorem arnyek_linearis : LinearisLekepezes T (Prod.fst : U × V → U) :=
  ⟨fun _ _ => rfl, fun _ _ => rfl⟩

/-- Lawvere `level` leképezése lineáris: a második vetítés `U × V → V`. -/
theorem szint_linearis : LinearisLekepezes T (Prod.snd : U × V → V) :=
  ⟨fun _ _ => rfl, fun _ _ => rfl⟩

/-- **A szorzat univerzális tulajdonsága lineáris leképezésekre.** Ha `f : W → U` és
`g : W → V` lineáris, akkor pontosan egy olyan lineáris `h : W → U × V` van, amelynek
az „árnyéka” `f`, a „szintje” `g`. Ez Lawvere „három objektum, két leképezés”
sémájának lineáris algebrai alakja. -/
theorem szorzat_univerzalis_linearis {f : W → U} {g : W → V}
    (hf : LinearisLekepezes T f) (hg : LinearisLekepezes T g) :
    ∃! h : W → U × V,
      LinearisLekepezes T h ∧ Prod.fst ∘ h = f ∧ Prod.snd ∘ h = g := by
  refine ⟨fun w => (f w, g w), ⟨⟨fun u v => ?_, fun l u => ?_⟩, rfl, rfl⟩, ?_⟩
  · exact Prod.ext (hf.1 u v) (hg.1 u v)
  · exact Prod.ext (hf.2 l u) (hg.2 l u)
  · rintro h ⟨-, h₁, h₂⟩
    funext w
    exact Prod.ext (congrFun h₁ w) (congrFun h₂ w)

/-- A szorzat univerzális tulajdonsága leképezéspárokkal kifejezve: a `W → U × V`
lineáris leképezések kölcsönösen egyértelműen megfelelnek a lineáris leképezéspároknak. -/
theorem szorzat_lekepezespar {h : W → U × V} :
    LinearisLekepezes T h ↔
      LinearisLekepezes T (fun w => (h w).1) ∧ LinearisLekepezes T (fun w => (h w).2) := by
  constructor
  · intro hh
    exact ⟨⟨fun u v => congrArg Prod.fst (hh.1 u v), fun l u => congrArg Prod.fst (hh.2 l u)⟩,
      ⟨fun u v => congrArg Prod.snd (hh.1 u v), fun l u => congrArg Prod.snd (hh.2 l u)⟩⟩
  · rintro ⟨h₁, h₂⟩
    exact ⟨fun u v => Prod.ext (h₁.1 u v) (h₂.1 u v), fun l u => Prod.ext (h₁.2 l u) (h₂.2 l u)⟩

/-! ## 2. Az `n`-szeres szorzat: `Tⁿ` és a koordináták -/

/-- A `Tⁿ` koordinátatér `i`-edik vetítése lineáris (a 6. fejezet `tupleVektorter`
példájának „árnyék-leképezései”). -/
theorem tuple_vetites_linearis {n : ℕ} (i : Fin n) :
    LinearisLekepezes T (fun x : Fin n → T => x i) :=
  ⟨fun _ _ => rfl, fun _ _ => rfl⟩

/-- **Az `n`-szeres szorzat univerzális tulajdonsága.** Egy `W → Tⁿ` lineáris leképezés
pontosan annyi, mint `n` darab lineáris `W → T` leképezés (koordinátafüggvény). -/
theorem tuple_univerzalis_linearis {n : ℕ} {f : Fin n → W → T}
    (hf : ∀ i, LinearisLekepezes T (f i)) :
    ∃! h : W → (Fin n → T), LinearisLekepezes T h ∧ ∀ i w, h w i = f i w := by
  refine ⟨fun w i => f i w, ⟨⟨fun u v => ?_, fun l u => ?_⟩, fun _ _ => rfl⟩, ?_⟩
  · funext i; exact (hf i).1 u v
  · funext i; exact (hf i).2 l u
  · rintro h ⟨-, hcomp⟩
    funext w i
    exact hcomp i w

/-- **„A pont a vetületeiből visszaállítható.”** Ha `v₁,…,v_k` bázis, akkor a bázis
szerinti koordináták (12.3.) minden vektort egyértelműen meghatároznak: a
`x ↦ (x koordinátái)` leképezés injektív, és a koordinátákból a vektor
visszaállítható. Ez Galilei „shadow + level” gondolatának pontos megfelelője. -/
theorem koordinatak_univerzalis {k : ℕ} {v : Fin k → V} (hv : Bazis T v) (x : V) :
    (∑ i, koordinatai hv x i • v i) = x ∧
      ∀ y : V, (∀ i, koordinatai hv x i = koordinatai hv y i) → x = y := by
  refine ⟨(koordinatai_spec hv x).symm, fun y hxy => ?_⟩
  exact koordinatai_injective hv (funext hxy)

/-! ## 3. A *számok* szorzása mint leképezés — a szorzatból *induló* leképezések

Lawvere utolsó képe a szorzás és a számok szorzásának kapcsolatát sejteti. A jegyzetben
ez a 15. fejezet bilineáris leképezéseiben jelenik meg: ezek éppen a `U × V` szorzatból
induló, mindkét változóban lineáris leképezések. -/

/-- A test szorzása bilineáris leképezés `T × T → T`: Lawvere „szorzás mint leképezés”
képének legegyszerűbb esete, a jegyzet 15.1. Definíciója szerint. -/
theorem szamszorzas_bilinearis :
    BilinearisLekepezes T (fun a b : T => a * b) := by
  refine ⟨fun a₁ a₂ b => add_mul a₁ a₂ b, fun a b₁ b₂ => mul_add a b₁ b₂,
    fun c a b => ?_, fun c a b => ?_⟩
  · simp [smul_eq_mul, mul_assoc]
  · simp [smul_eq_mul, mul_left_comm]

/-- Egy bilineáris leképezés mindkét változójában lineáris, azaz a `U × V` szorzat
mindkét „tengelye” mentén a jegyzet 10.1. Definíciója szerinti lineáris leképezést ad. -/
theorem bilinearis_valtozonkent_linearis {l : U → V → T} (hl : BilinearisLekepezes T l)
    (u : U) (v : V) :
    LinearisLekepezes T (fun y : V => l u y) ∧ LinearisLekepezes T (fun x : U => l x v) := by
  refine ⟨⟨fun y₁ y₂ => hl.2.1 u y₁ y₂, fun c y => ?_⟩,
    ⟨fun x₁ x₂ => hl.1 x₁ x₂ v, fun c x => ?_⟩⟩
  · simpa [smul_eq_mul] using hl.2.2.2 c u y
  · simpa [smul_eq_mul] using hl.2.2.1 c x v

/-! ## 4. Kompozíció: Lawvere első alapfogalma a jegyzetben

Lawvere a leképezések kompozíciójával kezdi (`shadow ∘ flight`). A jegyzetben ez a
10.7. Tétel (lineáris leképezések szorzata lineáris) és a 12.6. Tétel (a kompozíció
mátrixa a mátrixok szorzata) — a mátrixszorzás tehát *funktoriális*. -/

/-- Lineáris leképezések kompozíciója lineáris (10.7. Tétel), a kompozíció pedig
asszociatív és az identitás az egységeleme — Lawvere kategóriaaxiómái a jegyzet
lineáris leképezéseire. -/
theorem kompozicio_kategoria {f : U → V} {g : V → W}
    (hf : LinearisLekepezes T f) (hg : LinearisLekepezes T g) :
    LinearisLekepezes T (fun u => g (f u)) ∧
      ((fun u => g (f u)) ∘ (id : U → U) = fun u => g (f u)) ∧
      ((id : W → W) ∘ (fun u => g (f u)) = fun u => g (f u)) :=
  ⟨linearisLekepezes_comp hf hg, rfl, rfl⟩

end SzaboLinAlg.Lawvere
