import LinearisAlgebra.Ch11_MuveletekLekepezesekkel

/-!
# Szabó László: Bevezetés a lineáris algebrába — 12. fejezet

**Lineáris leképezések mátrixa** (a jegyzet 62–65. oldala).

* **12.1. Tétel** — a bázisvektorok képei egyértelműen meghatározzák a lineáris
  leképezést, és tetszőlegesen előírhatók,
* **12.2. Definíció** — a `φ` lineáris leképezés mátrixa az `ℰ` és `ℱ` bázisokban:
  `eᵢφ = ∑ⱼ aᵢⱼfⱼ`, továbbá a koordinátasorok kapcsolata: `y = xA`,
* **12.3. Tétel** — összeg, skalárszoros és szorzat (kompozíció) mátrixa,
* **12.4. Következmény** — `Hom(U,V)` izomorf a `T^{m×n}` mátrixtérrel.
-/

namespace SzaboLinAlg
namespace Ch12

open scoped BigOperators
open SzaboLinAlg.Ch02 SzaboLinAlg.Ch06 SzaboLinAlg.Ch07 SzaboLinAlg.Ch08 SzaboLinAlg.Ch10
  SzaboLinAlg.Ch11

variable {T : Type*} [Field T] {U V W : Type*} [AddCommGroup U] [Module T U]
  [AddCommGroup V] [Module T V] [AddCommGroup W] [Module T W] {m n p : ℕ}

/-! ## Segédlemma: lineáris leképezés és lineáris kombináció -/

/-- Lineáris leképezés lineáris kombinációt lineáris kombinációba visz:
`(∑ λᵢuᵢ)φ = ∑ λᵢ(uᵢφ)`. -/
theorem map_kombinacio {f : U → V} (hf : LinearisLekepezes T f) {k : ℕ} (x : Fin k → T)
    (u : Fin k → U) : f (∑ i, x i • u i) = ∑ i, x i • f (u i) := by
  have h : f (∑ i, x i • u i) = toLin hf (∑ i, x i • u i) := rfl
  rw [h, map_sum]
  simp [map_smul]

/-! ## 12.1. Tétel -/

/-- **12.1. Tétel.** Ha `e₁,…,e_m` bázis `U`-ban és `v₁,…,v_m ∈ V` tetszőleges
vektorrendszer, akkor pontosan egy olyan `φ ∈ Hom(U,V)` létezik, amelyre `eᵢφ = vᵢ`.

*Bizonyítás.* Az egyértelműség: ha `u = ∑ λᵢeᵢ`, akkor a linearitás miatt
`uφ = ∑ λᵢvᵢ`, tehát `φ`-t a bázisképek meghatározzák. A létezés: az
`u = ∑ λᵢeᵢ ↦ ∑ λᵢvᵢ` hozzárendelés jóldefiniált (a bázis szerinti előállítás
egyértelmű) és lineáris. -/
theorem letezik_egyertelmu_lekepezes {e : Fin m → U} (he : Bazis T e) (v : Fin m → V) :
    ∃! f : U → V, LinearisLekepezes T f ∧ ∀ i, f (e i) = v i := by
  classical
  set B : Module.Basis (Fin m) T U := toModuleBasis he with hB
  have hBe : ⇑B = e := Module.Basis.coe_mk _ _
  refine ⟨⇑(B.constr T v), ⟨⟨fun a b => map_add _ a b, fun l a => map_smul _ l a⟩,
    fun i => ?_⟩, ?_⟩
  · have := Module.Basis.constr_basis B T v i
    rwa [hBe] at this
  · rintro g ⟨hg, hge⟩
    have : toLin hg = B.constr T v := by
      refine Module.Basis.ext B fun i => ?_
      rw [Module.Basis.constr_basis B T v i]
      show g (B i) = v i
      rw [hBe]
      exact hge i
    exact congrArg (fun φ : U →ₗ[T] V => ⇑φ) this

/-! ## 12.2. Definíció -/

/-- **12.2. Definíció.** Az `A = (aᵢⱼ)` mátrix a `φ` lineáris leképezés mátrixa az
`ℰ : e₁,…,e_m` és `ℱ : f₁,…,f_n` bázisokban, ha `eᵢφ = ∑ⱼ aᵢⱼfⱼ` minden `i`-re. -/
def LekepezesMatrixa (f : U → V) (e : Fin m → U) (fb : Fin n → V) (A : Matrix' T m n) :
    Prop := ∀ i, f (e i) = ∑ j, A i j • fb j

omit [AddCommGroup U] [Module T U] in
/-- **12.2. Definíció.** Adott bázisok mellett a lineáris leképezés mátrixa létezik és
egyértelmű. -/
theorem letezik_egyertelmu_matrix {e : Fin m → U} {fb : Fin n → V} (hfb : Bazis T fb)
    (f : U → V) : ∃! A : Matrix' T m n, LekepezesMatrixa f e fb A := by
  classical
  have hex : ∀ i, ∃! g : Fin n → T, f (e i) = ∑ j, g j • fb j :=
    fun i => koordinatak_egyertelmuek hfb (f (e i))
  refine ⟨fun i j => Classical.choose (hex i) j, fun i => (Classical.choose_spec (hex i)).1,
    ?_⟩
  intro A hA
  funext i
  exact ((hex i).unique (hA i) (Classical.choose_spec (hex i)).1)

/-- Adott bázis szerinti koordináták (a 8.4. Definíció alapján). -/
noncomputable def koordinatai {k : ℕ} {v : Fin k → V} (hv : Bazis T v) (x : V) :
    Fin k → T := Classical.choose (koordinatak_egyertelmuek hv x)

theorem koordinatai_spec {k : ℕ} {v : Fin k → V} (hv : Bazis T v) (x : V) :
    x = ∑ i, koordinatai hv x i • v i :=
  (Classical.choose_spec (koordinatak_egyertelmuek hv x)).1

theorem koordinatai_eq {k : ℕ} {v : Fin k → V} (hv : Bazis T v) {x : V} {g : Fin k → T}
    (hg : x = ∑ i, g i • v i) : koordinatai hv x = g :=
  ((koordinatak_egyertelmuek hv x).unique
    (Classical.choose_spec (koordinatak_egyertelmuek hv x)).1 hg)

omit [AddCommGroup U] [Module T U] in
/-- A nullvektor koordinátái mind nullák. -/
theorem koordinatai_zero {k : ℕ} {v : Fin k → V} (hv : Bazis T v) :
    koordinatai hv (0 : V) = 0 :=
  koordinatai_eq hv (by simp)

omit [AddCommGroup U] [Module T U] in
/-- Egy vektor pontosan akkor a nullvektor, ha minden koordinátája nullával egyenlő. -/
theorem koordinatai_eq_zero_iff {k : ℕ} {v : Fin k → V} (hv : Bazis T v) (x : V) :
    koordinatai hv x = 0 ↔ x = 0 := by
  constructor
  · intro h
    have hx := koordinatai_spec hv x
    rw [h] at hx
    simpa using hx
  · rintro rfl
    exact koordinatai_zero hv

omit [AddCommGroup U] [Module T U] in
/-- A vektort a koordinátái egyértelműen meghatározzák. -/
theorem koordinatai_injective {k : ℕ} {v : Fin k → V} (hv : Bazis T v) :
    Function.Injective (koordinatai hv) := by
  intro a b h
  rw [koordinatai_spec hv a, koordinatai_spec hv b, h]

omit [AddCommGroup U] [Module T U] in
/-- A koordináták skalárszorzást tiszteletben tartó volta: `(cx)` koordinátái `c`-szeresei
`x` koordinátáinak. -/
theorem koordinatai_smul {k : ℕ} {v : Fin k → V} (hv : Bazis T v) (c : T) (x : V) :
    koordinatai hv (c • x) = c • koordinatai hv x := by
  refine koordinatai_eq hv ?_
  conv_lhs => rw [koordinatai_spec hv x]
  rw [Finset.smul_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [smul_smul]; rfl

/-- A `φ` leképezés mátrixa az `ℰ` és `ℱ` bázisokban. -/
noncomputable def matrixa (e : Fin m → U) {fb : Fin n → V} (hfb : Bazis T fb) (f : U → V) :
    Matrix' T m n := fun i j => koordinatai hfb (f (e i)) j

omit [AddCommGroup U] [Module T U] in
theorem lekepezesMatrixa_matrixa (e : Fin m → U) {fb : Fin n → V} (hfb : Bazis T fb)
    (f : U → V) : LekepezesMatrixa f e fb (matrixa e hfb f) :=
  fun i => koordinatai_spec hfb (f (e i))

/-- **12.2.** *Koordináta-transzformáció:* ha `u` koordinátasora az `ℰ` bázisban `x`,
akkor `uφ` koordinátasora az `ℱ` bázisban `y = xA`, azaz `yⱼ = ∑ᵢ xᵢaᵢⱼ`.

*Bizonyítás.* `uφ = (∑ᵢ xᵢeᵢ)φ = ∑ᵢ xᵢ(eᵢφ) = ∑ᵢ xᵢ ∑ⱼ aᵢⱼfⱼ = ∑ⱼ (∑ᵢ xᵢaᵢⱼ) fⱼ`. -/
theorem koordinata_transzformacio {f : U → V} (hf : LinearisLekepezes T f)
    {e : Fin m → U} {fb : Fin n → V} {A : Matrix' T m n} (hA : LekepezesMatrixa f e fb A)
    {u : U} {x : Fin m → T} (hu : u = ∑ i, x i • e i) :
    f u = ∑ j, (∑ i, x i * A i j) • fb j := by
  subst hu
  rw [map_kombinacio hf]
  calc ∑ i, x i • f (e i) = ∑ i, ∑ j, (x i * A i j) • fb j := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hA i, Finset.smul_sum]
        exact Finset.sum_congr rfl fun j _ => by rw [smul_smul]
    _ = ∑ j, ∑ i, (x i * A i j) • fb j := Finset.sum_comm
    _ = ∑ j, (∑ i, x i * A i j) • fb j := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_smul]

/-- **12.2.** A koordináták és a mátrix kapcsolata: `uφ` koordinátasora `u`
koordinátasorának és a leképezés mátrixának szorzata, azaz `y = xA`. -/
theorem koordinatai_map {f : U → V} (hf : LinearisLekepezes T f) {e : Fin m → U}
    {fb : Fin n → V} (he : Bazis T e) (hfb : Bazis T fb) {A : Matrix' T m n}
    (hA : LekepezesMatrixa f e fb A) (u : U) :
    koordinatai hfb (f u) = Matrix.vecMul (koordinatai he u) A := by
  refine koordinatai_eq hfb ?_
  exact koordinata_transzformacio hf hA (koordinatai_spec he u)

/-! ## 12.3. Tétel -/

omit [AddCommGroup U] [Module T U] in
/-- **12.3. Tétel.** Lineáris leképezések összegének mátrixa a mátrixok összege. -/
theorem matrixa_add {f g : U → V} {e : Fin m → U} {fb : Fin n → V} {A B : Matrix' T m n}
    (hA : LekepezesMatrixa f e fb A) (hB : LekepezesMatrixa g e fb B) :
    LekepezesMatrixa (f + g) e fb (A + B) := by
  intro i
  show f (e i) + g (e i) = _
  rw [hA i, hB i, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by rw [← add_smul]; rfl

omit [AddCommGroup U] [Module T U] in
/-- **12.3. Tétel.** A `c`-szeres leképezés mátrixa a mátrix `c`-szerese. -/
theorem matrixa_smul {f : U → V} {e : Fin m → U} {fb : Fin n → V} {A : Matrix' T m n}
    (hA : LekepezesMatrixa f e fb A) (c : T) :
    LekepezesMatrixa (c • f) e fb (c • A) := by
  intro i
  show c • f (e i) = _
  rw [hA i, Finset.smul_sum]
  exact Finset.sum_congr rfl fun j _ => by rw [smul_smul]; rfl

omit [AddCommGroup U] [Module T U] in
/-- **12.3. Tétel.** Lineáris leképezések szorzatának (kompozíciójának) mátrixa a
mátrixok szorzata.

*Bizonyítás.* `eᵢ(φψ) = (eᵢφ)ψ = (∑ⱼ aᵢⱼfⱼ)ψ = ∑ⱼ aᵢⱼ(fⱼψ) = ∑ⱼ aᵢⱼ ∑ₖ bⱼₖgₖ
= ∑ₖ (∑ⱼ aᵢⱼbⱼₖ) gₖ`. -/
theorem matrixa_comp {f : U → V} {g : V → W} (hg : LinearisLekepezes T g)
    {e : Fin m → U} {fb : Fin n → V} {gb : Fin p → W} {A : Matrix' T m n}
    {B : Matrix' T n p} (hA : LekepezesMatrixa f e fb A)
    (hB : LekepezesMatrixa g fb gb B) :
    LekepezesMatrixa (fun u => g (f u)) e gb (A * B) := by
  intro i
  show g (f (e i)) = _
  rw [hA i, map_kombinacio hg]
  calc ∑ j, A i j • g (fb j) = ∑ j, ∑ k, (A i j * B j k) • gb k := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hB j, Finset.smul_sum]
        exact Finset.sum_congr rfl fun k _ => by rw [smul_smul]
    _ = ∑ k, ∑ j, (A i j * B j k) • gb k := Finset.sum_comm
    _ = ∑ k, (A * B) i k • gb k := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [← Finset.sum_smul]
        rfl

omit [AddCommGroup U] [Module T U] in
/-- A `matrixa` függvény éppen a (12.2. értelemben vett) egyértelmű mátrixot adja. -/
theorem matrixa_eq {e : Fin m → U} {fb : Fin n → V} (hfb : Bazis T fb) {f : U → V}
    {A : Matrix' T m n} (hA : LekepezesMatrixa f e fb A) : matrixa e hfb f = A :=
  (letezik_egyertelmu_matrix hfb f).unique (lekepezesMatrixa_matrixa e hfb f) hA

/-! ## 12.4. Következmény -/

/-- **12.4. Következmény.** Ha `dim U = m` és `dim V = n`, akkor `Hom(U,V)` izomorf a
`T^{m×n}` mátrixtérrel (és így `mn`-dimenziós).

*Bizonyítás.* A `Φ : φ ↦ A_{φ}` hozzárendelés a 12.1. Tétel szerint bijektív (a
bázisképek és a mátrix kölcsönösen egyértelműen meghatározzák egymást), a 12.3. Tétel
szerint pedig lineáris. -/
theorem izomorf_hom_matrix {e : Fin m → U} {fb : Fin n → V} (he : Bazis T e)
    (hfb : Bazis T fb) : Izomorf T (homAlter T U V) (Matrix' T m n) := by
  classical
  refine ⟨fun f => matrixa e hfb f.1, ⟨⟨fun f g => ?_, fun c f => ?_⟩, ?_, ?_⟩⟩
  · exact matrixa_eq hfb (matrixa_add (lekepezesMatrixa_matrixa e hfb f.1)
      (lekepezesMatrixa_matrixa e hfb g.1))
  · exact matrixa_eq hfb (matrixa_smul (lekepezesMatrixa_matrixa e hfb f.1) c)
  · rintro ⟨f, hf⟩ ⟨g, hg⟩ hfg
    have hfg' : ∀ i, f (e i) = g (e i) := by
      intro i
      rw [lekepezesMatrixa_matrixa e hfb f i, lekepezesMatrixa_matrixa e hfb g i]
      simp only [hfg]
    have := (letezik_egyertelmu_lekepezes he fun i => f (e i)).unique
      ⟨hf, fun i => rfl⟩ ⟨hg, fun i => (hfg' i).symm⟩
    exact Subtype.ext this
  · intro A
    obtain ⟨f, ⟨hf, hfe⟩, -⟩ := letezik_egyertelmu_lekepezes he fun i => ∑ j, A i j • fb j
    exact ⟨⟨f, hf⟩, matrixa_eq hfb (fun i => hfe i)⟩

/-- **12.4. Következmény.** `Hom(U,V)` dimenziója `mn`, ha `dim U = m` és `dim V = n`. -/
theorem dimenzioja_hom {e : Fin m → U} {fb : Fin n → V} (he : Bazis T e)
    (hfb : Bazis T fb) : Dimenzioja T (homAlter T U V) (m * n) := by
  have hM : Dimenzioja T (Matrix' T m n) (m * n) :=
    dimenzioja_of_finrank_eq (by simp [Module.finrank_matrix])
  exact dimenzioja_of_izomorf (izomorf_symm (izomorf_hom_matrix he hfb)) hM

end Ch12
end SzaboLinAlg
