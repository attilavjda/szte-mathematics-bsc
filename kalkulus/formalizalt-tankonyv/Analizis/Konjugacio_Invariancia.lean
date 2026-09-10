import Mathlib
import Analizis.Ch06a_Differencialhatosag
import Analizis.Ch06b_ElemiDerivaltak

/-!
# Konjugációs invariancia a kalkulusban — a `trace_units_conj'` analízisbeli párja

A lineáris algebrában (Szabó László jegyzete, 4.4. Definíció) egy `A` mátrix
`X⁻¹AX` alakú átírása *bázisváltás*, és az olyan mennyiségek, amelyek ilyenkor
nem változnak (determináns: 4.5. Tétel; rang: 9.6. Tétel; karakterisztikus
polinom: 14.3. Tétel; nyom: `SzaboLinAlg.Nyom.nyom_hasonlo`), valójában nem a
mátrixhoz, hanem a *transzformációhoz* tartoznak.

Ennek pontos analízisbeli megfelelője a **koordinátacsere melletti invariancia**:
ha egy `f` leképezést egy `h` kölcsönösen egyértelmű, differenciálható
„koordinátacserével” átírunk `h ∘ f ∘ h⁻¹` alakba, akkor `f` bizonyos jellemzői
nem változnak. A mátrixnyom egydimenziós megfelelője a **fixpontbeli
differenciálhányados** (a fixpont *multiplikátora*): ez `1 × 1`-es mátrixként
éppen a derivált mátrixának nyoma, és a **6.4.1. Tétel (láncszabály)** szerint
konjugálásra invariáns — a bizonyítás lépésről lépésre ugyanaz, mint a mátrixos
esetben: `h' (x₀) · f' (x₀) · (h⁻¹)' (h x₀) = p · c · p⁻¹ = c`.

A modul a jegyzet saját fogalmaival dolgozik: a `Leindler.Ch06.Derivalt` a 6.1.3.
Definíció szerinti differenciálhányados, a láncszabály a 6.4.1. Tétel
(`derivalt_osszetett`), az inverz függvény deriváltja pedig a 6.5. pont
(`derivalt_inverz`).
-/

namespace Leindler.Konjugacio

open Leindler Leindler.Ch05 Leindler.Ch06

/-! ## A fixpont és a multiplikátor -/

/-- Az `x₀` pont az `f` függvény *fixpontja*, ha `f(x₀) = x₀`. -/
def Fixpont (f : ℝ → ℝ) (x₀ : ℝ) : Prop := f x₀ = x₀

/-- Az `f` függvény `x₀` fixpontjának *multiplikátora* a `c` szám, ha `f` az `x₀`
pontban differenciálható, és `f'(x₀) = c`. (Egydimenziós megfelelője a derivált
mátrixának: `1 × 1`-es mátrixként `c` egyben a determinánsa és a nyoma is.) -/
def Multiplikator (f : ℝ → ℝ) (x₀ c : ℝ) : Prop := Fixpont f x₀ ∧ Derivalt f x₀ c

/-! ## A koordinátacsere (konjugálás) -/

/-- A `h` függvény *koordinátacsere* a `hinv` inverzzel, ha a két függvény
egymás kölcsönös inverze: `h⁻¹(h(x)) = x` és `h(h⁻¹(y)) = y` minden `x`, `y` esetén.
Ez a lineáris algebrabeli `X` nemelfajuló mátrix szerepét játssza. -/
def Koordinatacsere (h hinv : ℝ → ℝ) : Prop :=
  (∀ x, hinv (h x) = x) ∧ ∀ y, h (hinv y) = y

/-- A konjugált (átparaméterezett) függvény: `F = h ∘ f ∘ h⁻¹`, a mátrixos
`X⁻¹AX` (illetve `XAX⁻¹`) pontos megfelelője. -/
def konjugalt (h hinv f : ℝ → ℝ) : ℝ → ℝ := fun y => h (f (hinv y))

/-! ## A fixpont átvitele -/

/-- Koordinátacsere a fixpontot fixpontba viszi: ha `f(x₀) = x₀`, akkor
`(h ∘ f ∘ h⁻¹)(h(x₀)) = h(x₀)`. -/
theorem fixpont_konjugalt {h hinv f : ℝ → ℝ} (hk : Koordinatacsere h hinv) {x₀ : ℝ}
    (hfix : Fixpont f x₀) : Fixpont (konjugalt h hinv f) (h x₀) := by
  unfold Fixpont konjugalt at *
  rw [hk.1 x₀, hfix]

/-! ## A fő tétel: a multiplikátor konjugálásra invariáns -/

/-- **A `Matrix.trace_units_conj'` analízisbeli megfelelője.**
Legyen `x₀` az `f` fixpontja, `f'(x₀) = c`; legyen `h` koordinátacsere a `hinv`
inverzzel, `h'(x₀) = p`, `hinv'(h x₀) = q`, ahol `p·q = 1` (a 6.5. pont szerint
`q = 1/p`). Ekkor a konjugált `F = h ∘ f ∘ h⁻¹` függvénynek `h(x₀)` fixpontja, és
ott a differenciálhányadosa ugyanaz a `c`:
`F'(h x₀) = p · c · q = c`.

*Bizonyítás (a 6.4.1. Tétel kétszeri alkalmazásával).* A láncszabály szerint
`(f ∘ h⁻¹)'(h x₀) = f'(h⁻¹(h x₀))·(h⁻¹)'(h x₀) = c·q`. A külső `h`-t a
`(f ∘ h⁻¹)(h x₀) = f(x₀) = x₀` pontban kell deriválni — **itt használjuk ki, hogy
`x₀` fixpont**, ugyanúgy, ahogy a mátrixos bizonyításban azt, hogy a konjugáló
tényezők a *két* oldalon egymás inverzei. Így
`F'(h x₀) = h'(x₀)·(c·q) = p·c·q = c·(p·q) = c`. -/
theorem multiplikator_konjugalt_invarians {h hinv f : ℝ → ℝ} {x₀ c p q : ℝ}
    (hk : Koordinatacsere h hinv) (hfix : Fixpont f x₀) (hf : Derivalt f x₀ c)
    (hh : Derivalt h x₀ p) (hhinv : Derivalt hinv (h x₀) q) (hpq : p * q = 1) :
    Multiplikator (konjugalt h hinv f) (h x₀) c := by
  refine ⟨fixpont_konjugalt hk hfix, ?_⟩
  have hx : hinv (h x₀) = x₀ := hk.1 x₀
  -- belső lépés: `(f ∘ h⁻¹)' (h x₀) = c · q`
  have h1 : Derivalt (fun y => f (hinv y)) (h x₀) (c * q) := by
    refine derivalt_osszetett hhinv ?_
    rw [hx]
    exact hf
  -- külső lépés: a `h`-t az `f (h⁻¹ (h x₀)) = f x₀ = x₀` pontban deriváljuk
  have h2 : Derivalt h (f (hinv (h x₀))) p := by
    rw [hx, hfix]
    exact hh
  have h3 : Derivalt (fun y => h (f (hinv y))) (h x₀) (p * (c * q)) :=
    derivalt_osszetett h1 h2
  have : p * (c * q) = c := by
    calc p * (c * q) = c * (p * q) := by ring
      _ = c := by rw [hpq, mul_one]
  rw [this] at h3
  exact h3

/-- Ugyanez a jegyzet 6.5. pontjának inverzfüggvény-tételével: ha `h'(x₀) = p ≠ 0`,
akkor `hinv'(h x₀) = 1/p`, tehát a `p·q = 1` feltétel automatikusan teljesül. -/
theorem multiplikator_konjugalt_invarians_reciprok {h hinv f : ℝ → ℝ} {x₀ c p : ℝ}
    (hk : Koordinatacsere h hinv) (hfix : Fixpont f x₀) (hf : Derivalt f x₀ c)
    (hh : Derivalt h x₀ p) (hp : p ≠ 0) (hhinv : Derivalt hinv (h x₀) (1 / p)) :
    Multiplikator (konjugalt h hinv f) (h x₀) c :=
  multiplikator_konjugalt_invarians hk hfix hf hh hhinv (by field_simp)

/-! ## Következmények: a multiplikátor mint invariáns -/

/-- A „vonzó fixpont” tulajdonság (`|f'(x₀)| < 1`) koordinátacserére invariáns:
az iteráció konvergenciasebességét jellemző mennyiség nem a koordinátáktól,
hanem magától a leképezéstől függ. (A mátrixos megfelelője: a sajátértékek,
illetve a nyom hasonlósági invarianciája.) -/
theorem vonzo_fixpont_invarians {h hinv f : ℝ → ℝ} {x₀ c p q : ℝ}
    (hk : Koordinatacsere h hinv) (hfix : Fixpont f x₀) (hf : Derivalt f x₀ c)
    (hh : Derivalt h x₀ p) (hhinv : Derivalt hinv (h x₀) q) (hpq : p * q = 1)
    (hc : |c| < 1) :
    ∃ c', Multiplikator (konjugalt h hinv f) (h x₀) c' ∧ |c'| < 1 :=
  ⟨c, multiplikator_konjugalt_invarians hk hfix hf hh hhinv hpq, hc⟩

/-- A multiplikátor egyértelmű (a differenciálhányados unicitása, 6.1. pont),
ezért a fenti tétel valóban azt mondja, hogy a konjugált leképezés
multiplikátora *ugyanaz*, nem csak azt, hogy `c` is jó érték. -/
theorem multiplikator_unicitas {f : ℝ → ℝ} {x₀ c c' : ℝ} (h : Multiplikator f x₀ c)
    (h' : Multiplikator f x₀ c') : c = c' :=
  derivalt_unicitas h.2 h'.2

/-! ## Példa: a jegyzetbeli lineáris eset

Az `f(x) = a·x` leképezés `0`-ban fixpontot vesz fel, multiplikátora `a`; a
`h(x) = b·x` (`b ≠ 0`) koordinátacsere mellett a konjugált leképezés
`F(y) = b·a·(y/b) = a·y`, tehát a multiplikátor változatlanul `a` — pontosan úgy,
ahogy `1 × 1`-es mátrixokra `X⁻¹AX = A`. -/
theorem linearis_pelda (a b : ℝ) (hb : b ≠ 0) :
    konjugalt (fun x => b * x) (fun y => y / b) (fun x => a * x) = fun y => a * y := by
  funext y
  show b * (a * (y / b)) = a * y
  have hby : b * (y / b) = y := by field_simp
  calc b * (a * (y / b)) = a * (b * (y / b)) := by ring
    _ = a * y := by rw [hby]

end Leindler.Konjugacio
