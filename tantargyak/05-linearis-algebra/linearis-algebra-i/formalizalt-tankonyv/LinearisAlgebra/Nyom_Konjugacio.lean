import LinearisAlgebra.Ch14_Sajatertek

/-!
# A mátrix nyoma és a konjugációs invariancia

Ez a modul a Mathlib

```
theorem Matrix.trace_units_conj' (M : (Matrix m m R)ˣ) (N : Matrix m m R) :
    trace ((↑M⁻¹ : Matrix _ _ _) * N * (↑M : Matrix _ _ _)) = trace N
```

tételét helyezi el a jegyzet anyagában.

**Hol van ez a jegyzetben?**  A *nyom* (angolul `trace`) fogalma Szabó László
*Bevezetés a lineáris algebrába* című jegyzetében **nem szerepel**; a tétel
`X⁻¹AX` alakja viszont szó szerint a jegyzet

* **4.4. Definíció** (hasonló mátrixok: `B = X⁻¹AX`, lásd `SzaboLinAlg.Ch04.Hasonlo`)

fogalma, és a tétel tartalma — „ez a mennyiség hasonló mátrixokra ugyanaz” —
pontosan az a mintázat, amelyet a jegyzet három helyen ki is mond:

* **4.5. Tétel**: hasonló mátrixok determinánsa egyenlő (`Ch04.hasonlo_det`),
* **9.6. Tétel**: hasonló mátrixok rangja egyenlő (`Ch09.rang_hasonlo`),
* **14.3. Tétel**: hasonló mátrixok karakterisztikus polinomja egyenlő
  (`Ch14.karPol_hasonlo`), és emiatt **14.4. Definíció**: a lineáris transzformáció
  karakterisztikus polinomja független a bázis megválasztásától
  (`Ch14.karPol_fuggetlen_bazistol`, a 13.5. Következménnyel együtt).

Itt tehát a hiányzó negyedik esetet, a **nyomot** vezetjük be a jegyzet jelöléseivel
és bizonyítási stílusában, majd megmutatjuk, hogy a Mathlib-tétel ennek a
mintázatnak egy példánya.

**A közös mintázat.** Mindegyik bizonyítás ugyanabból az egyetlen tulajdonságból
következik: a szóban forgó `F` mennyiség *ciklikus*, azaz `F (AB) = F (BA)`
(a determinánsnál ez a szorzástételből, a nyomnál az összegzés sorrendjének
felcseréléséből adódik). Ezt a lépést a `ciklikus_konjugacio_invarians` lemma
egyszer, tetszőleges monoidra mondja ki — ez a Mathlib-tétel „kategóriaelméleti
váza” (lásd a modul végén a megjegyzést és a `KATEGORIAELMELETI_MINTAZATOK.md`
dokumentumot).
-/

namespace SzaboLinAlg
namespace Nyom

open scoped BigOperators
open SzaboLinAlg.Ch02 SzaboLinAlg.Ch03 SzaboLinAlg.Ch04 SzaboLinAlg.Ch07 SzaboLinAlg.Ch08
  SzaboLinAlg.Ch10 SzaboLinAlg.Ch12 SzaboLinAlg.Ch13 SzaboLinAlg.Ch14

/-! ## A mintázat: ciklikus mennyiség konjugálásra invariáns -/

/-- **A mintázat (tetszőleges monoidban).** Ha az `F` mennyiség *ciklikus*, azaz
`F (a·b) = F (b·a)` minden `a, b` esetén, akkor `F` invariáns az invertálható
elemekkel való konjugálásra: `F (u⁻¹ · x · u) = F x`.

*Bizonyítás.* `F (u⁻¹xu) = F ((u⁻¹x)·u) = F (u·(u⁻¹x)) = F ((uu⁻¹)x) = F x`. -/
theorem ciklikus_konjugacio_invarians {M S : Type*} [Monoid M] (F : M → S)
    (hciklikus : ∀ a b : M, F (a * b) = F (b * a)) (u : Mˣ) (x : M) :
    F ((↑u⁻¹ : M) * x * u) = F x := by
  calc F ((↑u⁻¹ : M) * x * u) = F ((↑u : M) * ((↑u⁻¹ : M) * x)) :=
        hciklikus ((↑u⁻¹ : M) * x) u
    _ = F (((↑u : M) * (↑u⁻¹ : M)) * x) := by rw [mul_assoc]
    _ = F x := by rw [u.mul_inv, one_mul]

/-- Ugyanez a mintázat a másik oldalról konjugálva: `F (u · x · u⁻¹) = F x`. -/
theorem ciklikus_konjugacio_invarians' {M S : Type*} [Monoid M] (F : M → S)
    (hciklikus : ∀ a b : M, F (a * b) = F (b * a)) (u : Mˣ) (x : M) :
    F ((↑u : M) * x * (↑u⁻¹ : M)) = F x := by
  have := ciklikus_konjugacio_invarians F hciklikus u⁻¹ x
  simpa using this

/-! ## A nyom (trace) a jegyzet jelöléseivel -/

variable {T : Type*} [Field T] {n : ℕ}

/-- **Definíció (kiegészítés a jegyzethez).** Az `A ∈ Tⁿˣⁿ` négyzetes mátrix *nyoma*
a főátlójában álló elemek összege: `tr A = a₁₁ + a₂₂ + ⋯ + aₙₙ`.

(A jegyzet a 2.1. Definícióban bevezeti a főátlót, de a nyomot nem definiálja;
ez az egyetlen új fogalom ebben a modulban.) -/
def nyom (A : Matrix' T n n) : T := ∑ i, A i i

@[simp] theorem nyom_apply (A : Matrix' T n n) : nyom A = ∑ i, A i i := rfl

/-- A jegyzet szerinti nyom megegyezik a Mathlib `Matrix.trace` fogalmával. -/
theorem nyom_eq_trace (A : Matrix' T n n) : nyom A = Matrix.trace A := rfl

/-- A nyom additív: `tr (A + B) = tr A + tr B` (2.2. Definíció szerinti összeadás). -/
theorem nyom_osszeg (A B : Matrix' T n n) : nyom (A + B) = nyom A + nyom B := by
  simp [nyom, Finset.sum_add_distrib]

/-- A nyom homogén: `tr (λA) = λ·tr A` (2.2. Definíció szerinti skalárszoros). -/
theorem nyom_skalarszoros (lam : T) (A : Matrix' T n n) :
    nyom (lam • A) = lam * nyom A := by
  simp [nyom, Finset.mul_sum]

/-- A transzponálás nem változtatja meg a nyomot (2.6. Definíció): `tr Aᵀ = tr A`. -/
theorem nyom_transzponalt (A : Matrix' T n n) : nyom (Matrix.transpose A) = nyom A := rfl

/-- Az egységmátrix nyoma `n` (2.1. Definíció). -/
theorem nyom_egysegmatrix : nyom (1 : Matrix' T n n) = (n : T) := by
  simp [nyom]

/-- **A kulcslépés (a nyom ciklikus).** `tr (AB) = tr (BA)`.

*Bizonyítás (a jegyzet 2.4. Definíciójának szorzatképletével).*
`tr (AB) = ∑ᵢ ∑ⱼ aᵢⱼ bⱼᵢ`, és `tr (BA) = ∑ⱼ ∑ᵢ bⱼᵢ aᵢⱼ`; a két kettős összeg a
tagok sorrendjétől eltekintve azonos, tehát egyenlő. -/
theorem nyom_szorzat_kommutal (A B : Matrix' T n n) : nyom (A * B) = nyom (B * A) := by
  simp only [nyom, Matrix.mul_apply]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => mul_comm _ _

/-! ## A Mathlib-tétel megfelelője a jegyzet nyelvén -/

/-- **A `Matrix.trace_units_conj'` megfelelője.** Ha `X` és `Y` egymás inverzei
(4.1. Definíció, `Inverze X Y`), akkor `tr (Y A X) = tr A`, azaz — a jegyzet
`X⁻¹AX` írásmódjával — `tr (X⁻¹AX) = tr A`.

*Bizonyítás (a 4.5. Tétel determinánsra adott gondolatmenetének mintájára).*
`tr (YAX) = tr ((YA)X) = tr (X(YA)) = tr ((XY)A) = tr (EA) = tr A`. -/
theorem nyom_konjugalt {A X Y : Matrix' T n n} (hXY : Inverze X Y) :
    nyom (Y * A * X) = nyom A := by
  calc nyom (Y * A * X) = nyom (X * (Y * A)) := nyom_szorzat_kommutal _ _
    _ = nyom ((X * Y) * A) := by rw [Matrix.mul_assoc]
    _ = nyom A := by rw [hXY.2, Matrix.one_mul]

/-- Ugyanez a másik oldalról konjugálva: `tr (XAX⁻¹) = tr A`. -/
theorem nyom_konjugalt' {A X Y : Matrix' T n n} (hXY : Inverze X Y) :
    nyom (X * A * Y) = nyom A :=
  nyom_konjugalt (inverz_inverze hXY)

/-- **A hiányzó „4.5. Tétel a nyomra”.** Hasonló mátrixok nyoma megegyezik
(4.4. Definíció). Ez a determinánsra vonatkozó `Ch04.hasonlo_det`, a rangra
vonatkozó `Ch09.rang_hasonlo` és a karakterisztikus polinomra vonatkozó
`Ch14.karPol_hasonlo` tételek mintája szerinti állítás. -/
theorem nyom_hasonlo {A B : Matrix' T n n} (h : Hasonlo A B) : nyom B = nyom A := by
  obtain ⟨X, Y, hXY, hB⟩ := h
  rw [hB, nyom_konjugalt hXY]

/-- A `Matrix.trace_units_conj'` szó szerinti alakja: egységcsoportbeli `M` mellett
`tr (M⁻¹ N M) = tr N`; itt a fenti általános mintázat (`ciklikus_konjugacio_invarians`)
egyenes következményeként. -/
theorem nyom_egysegkonjugalt (M : (Matrix' T n n)ˣ) (N : Matrix' T n n) :
    nyom ((↑M⁻¹ : Matrix' T n n) * N * (↑M : Matrix' T n n)) = nyom N :=
  ciklikus_konjugacio_invarians nyom nyom_szorzat_kommutal M N

/-- Ugyanaz a mintázat a determinánsra alkalmazva: a 4.5. Tétel is a
`ciklikus_konjugacio_invarians` lemma példánya, hiszen `|AB| = |A||B| = |BA|`. -/
theorem det_egysegkonjugalt (M : (Matrix' T n n)ˣ) (N : Matrix' T n n) :
    det' ((↑M⁻¹ : Matrix' T n n) * N * (↑M : Matrix' T n n)) = det' N := by
  refine ciklikus_konjugacio_invarians det' (fun A B => ?_) M N
  rw [det'_eq_det, det'_eq_det, Matrix.det_mul, Matrix.det_mul, mul_comm]

/-! ## A lineáris transzformáció nyoma (a 14.4. Definíció mintájára) -/

variable {V : Type*} [AddCommGroup V] [Module T V] {m : ℕ}

/-- **A 14.4. Definíció mintájára.** Egy lineáris transzformáció különböző bázisokban
felírt mátrixainak nyoma megegyezik (13.5. Következmény + a fenti `nyom_hasonlo`),
ezért a *transzformáció nyoma* jól definiált fogalom. -/
theorem nyom_fuggetlen_bazistol {f : V → V} (hf : LinearisLekepezes T f)
    {e e' : Fin m → V} (he : Bazis T e) (he' : Bazis T e') {A A' : Matrix' T m m}
    (hA : LekepezesMatrixa f e e A) (hA' : LekepezesMatrixa f e' e' A') :
    nyom A' = nyom A := by
  obtain ⟨P, hP, -⟩ := letezik_egyertelmu_atteres (T := T) (e := e) he'
  exact nyom_hasonlo (hasonlo_baziscsere hf he he' hP hA hA')

/-- **A 14.4. Definíció mintájára.** A `φ` lineáris transzformáció *nyoma* az `ℰ`
bázisban felírt mátrixának nyoma; az előző tétel szerint ez nem függ a bázistól. -/
noncomputable def transzformacioNyom {f : V → V} {e : Fin m → V} (he : Bazis T e)
    (_hf : LinearisLekepezes T f) : T := nyom (matrixa e he f)

/-! ## Kapcsolat a karakterisztikus polinommal (14.1. Definíció), `n = 2` esetén -/

/-- Másodrendű mátrixra a karakterisztikus polinom `f_A(x) = x² − (tr A)x + |A|`,
azaz a nyom éppen a 14.1. Definícióbeli karakterisztikus polinom együtthatója —
így a `nyom_hasonlo` a 14.3. Tétel egyik együtthatónkénti következménye is. -/
theorem karPol_fin_two (A : Matrix' T 2 2) :
    karPol A = Polynomial.X ^ 2 - Polynomial.C (nyom A) * Polynomial.X
      + Polynomial.C (det' A) := by
  rw [karPol, det'_eq_det, Matrix.det_fin_two, Matrix.det_fin_two]
  simp only [Matrix.sub_apply, Matrix.map_apply, Matrix.diagonal_apply, nyom,
    Fin.sum_univ_two, Polynomial.C_add, Polynomial.C_sub, Polynomial.C_mul]
  simp only [if_true, if_neg (by decide : ¬(0 : Fin 2) = 1), if_neg (by decide : ¬(1 : Fin 2) = 0)]
  ring

/-! ## Megjegyzés: a kategóriaelméleti minta

A `ciklikus_konjugacio_invarians` lemma állítása kategóriaelméleti nyelven:
`Tⁿˣⁿ` az `n` dimenziós tér endomorfizmusainak monoidja (azaz az `End V`
egyobjektumú kategória), a bázisváltás pedig egy `V ≅ V` izomorfizmussal való
konjugálás. Egy `F : End V → S` mennyiség pontosan akkor öröklődik át
izomorfizmus mentén (azaz pontosan akkor a *transzformáció* és nem a *mátrix*
invariánsa), ha a konjugálásra invariáns; ehhez elég a ciklikusság `F(AB) = F(BA)`.

A nyom esetében ez több, mint elégséges feltétel: szimmetrikus monoidális
kategóriában a `tr` (kategóriaelméleti nyom) definíció szerint ciklikus, és a
`tr(f) = tr(g⁻¹fg)` invariancia ennek közvetlen következménye. A jegyzet három
tétele (4.5., 9.6., 14.3.) és a Mathlib `Matrix.trace_units_conj'` tétele tehát
ugyanannak az egy mintázatnak a példányai.
-/

end Nyom
end SzaboLinAlg
