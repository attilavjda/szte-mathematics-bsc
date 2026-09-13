import LinearisAlgebra.Ch10_LinearisLekepezesek

/-!
# Szabó László: Bevezetés a lineáris algebrába — 11. fejezet

**Műveletek lineáris leképezésekkel** (a jegyzet 59–61. oldala).

* **11.1. Definíció** — lineáris leképezések összege és skalárszorosa (pontonként),
* **11.2. Tétel** — `Hom(U,V)` ezekkel a műveletekkel vektorteret alkot,
* **11.3. Tétel** — `c(φψ) = (cφ)ψ = φ(cψ)`, valamint a szorzás disztributivitása az
  összeadásra nézve.

A könyv a leképezéseket jobbról írja (`uφ`), a `φψ` szorzat tehát az „előbb `φ`, azután
`ψ`” kompozíciót jelenti; itt ezt a `fun u => ψ (φ u)` alakban írjuk.
-/

namespace SzaboLinAlg
namespace Ch11

open scoped BigOperators
open SzaboLinAlg.Ch06 SzaboLinAlg.Ch10

variable {T : Type*} [Field T] {U V W : Type*} [AddCommGroup U] [Module T U]
  [AddCommGroup V] [Module T V] [AddCommGroup W] [Module T W]

/-! ## 11.1. Definíció -/

omit [AddCommGroup U] in
/-- **11.1. Definíció.** Két leképezés összege pontonként: `u(φ + ψ) = uφ + uψ`.
(A `U → V` függvénytéren ez éppen a Mathlib `+` művelete.) -/
theorem osszeg_apply (f g : U → V) (u : U) : (f + g) u = f u + g u := rfl

omit [AddCommGroup U] [Module T U] in
/-- **11.1. Definíció.** A leképezés skalárszorosa pontonként: `u(cφ) = c(uφ)`. -/
theorem skalarszoros_apply (c : T) (f : U → V) (u : U) : (c • f) u = c • f u := rfl

/-! ## 11.2. Tétel -/

/-- **11.2. Tétel (első rész).** Lineáris leképezések összege is lineáris.

*Bizonyítás.* `(u+v)(φ+ψ) = (u+v)φ + (u+v)ψ = (uφ + vφ) + (uψ + vψ)
= (uφ + uψ) + (vφ + vψ) = u(φ+ψ) + v(φ+ψ)`, és hasonlóan a skalárszorosra. -/
theorem linearisLekepezes_add {f g : U → V} (hf : LinearisLekepezes T f)
    (hg : LinearisLekepezes T g) : LinearisLekepezes T (f + g) := by
  refine ⟨fun u v => ?_, fun l u => ?_⟩
  · show f (u + v) + g (u + v) = (f u + g u) + (f v + g v)
    rw [hf.1, hg.1]
    abel
  · show f (l • u) + g (l • u) = l • (f u + g u)
    rw [hf.2, hg.2, smul_add]

/-- **11.2. Tétel (első rész).** Lineáris leképezés skalárszorosa is lineáris. -/
theorem linearisLekepezes_smul' (c : T) {f : U → V} (hf : LinearisLekepezes T f) :
    LinearisLekepezes T (c • f) := by
  refine ⟨fun u v => ?_, fun l u => ?_⟩
  · show c • f (u + v) = c • f u + c • f v
    rw [hf.1, smul_add]
  · show c • f (l • u) = l • (c • f u)
    rw [hf.2, smul_comm]

/-- **11.1. Definíció.** A `Hom(U,V)` halmaz: az `U`-ból `V`-be menő lineáris
leképezések halmaza. -/
def Hom (T : Type*) [Field T] (U V : Type*) [AddCommGroup U] [Module T U]
    [AddCommGroup V] [Module T V] : Set (U → V) := {f | LinearisLekepezes T f}

/-- **11.2. Tétel.** `Hom(U,V)` altér a `V^U` függvénytérben, ezért maga is vektortér. -/
theorem alter_hom : Alter T (Hom T U V) :=
  ⟨⟨0, linearisLekepezes_zero⟩, fun _ hf _ hg => linearisLekepezes_add hf hg,
    fun c _ hf => linearisLekepezes_smul' c hf⟩

/-- `Hom(U,V)` mint részmodulus (altér) a `U → V` függvénytérben. -/
def homAlter (T : Type*) [Field T] (U V : Type*) [AddCommGroup U] [Module T U]
    [AddCommGroup V] [Module T V] : Submodule T (U → V) where
  carrier := Hom T U V
  add_mem' hf hg := linearisLekepezes_add hf hg
  zero_mem' := linearisLekepezes_zero
  smul_mem' c _ hf := linearisLekepezes_smul' c hf

@[simp] theorem coe_homAlter : (homAlter T U V : Set (U → V)) = Hom T U V := rfl

/-- **11.2. Tétel.** `Hom(U,V)` a 6.1. Definíció értelmében vett vektortér. -/
def homVektorter (T : Type*) [Field T] (U V : Type*) [AddCommGroup U] [Module T U]
    [AddCommGroup V] [Module T V] : Vektorter T (homAlter T U V) :=
  modulVektorter T _

/-! ## 11.3. Tétel -/

omit [AddCommGroup U] [Module T U] [AddCommGroup V] [Module T V] in
/-- **(11.3.1)** `c(φψ) = φ(cψ)` (a bal oldal a kompozíció `c`-szerese). -/
theorem smul_comp {f : U → V} {g : V → W} (c : T) :
    (c • fun u => g (f u)) = fun u => (c • g) (f u) := rfl

omit [AddCommGroup U] [Module T U] in
/-- **(11.3.1)** `c(φψ) = (cφ)ψ`, ha `ψ` lineáris.

*Bizonyítás.* `u(c(φψ)) = c((uφ)ψ) = ((c(uφ))ψ = (u(cφ))ψ`. -/
theorem smul_comp' {f : U → V} {g : V → W} (hg : LinearisLekepezes T g) (c : T) :
    (c • fun u => g (f u)) = fun u => g ((c • f) u) := by
  funext u
  show c • g (f u) = g (c • f u)
  rw [hg.2]

omit [AddCommGroup U] [Module T U] in
/-- **(11.3.2)** `(φ + ψ)τ = φτ + ψτ`, ha `τ` lineáris. -/
theorem add_comp {f g : U → V} {t : V → W} (ht : LinearisLekepezes T t) :
    (fun u => t ((f + g) u)) = (fun u => t (f u)) + fun u => t (g u) := by
  funext u
  show t (f u + g u) = t (f u) + t (g u)
  rw [ht.1]

omit [AddCommGroup U] [AddCommGroup V] in
/-- **(11.3.2)** `φ(ψ + τ) = φψ + φτ`. -/
theorem comp_add {f : U → V} {g t : V → W} :
    (fun u => (g + t) (f u)) = (fun u => g (f u)) + fun u => t (f u) := rfl

end Ch11
end SzaboLinAlg
