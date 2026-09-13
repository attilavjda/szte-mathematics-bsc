import LinearisAlgebra.Ch12_LekepezesMatrixa

/-!
# Szabó László: Bevezetés a lineáris algebrába — 13. fejezet

**Áttérés új bázisra. Koordináta-transzformáció** (a jegyzet 66–69. oldala).

* **13.1. Definíció** — az áttérés mátrixa (`e = Pe'`),
* **13.2. Tétel** — `PP' = P'P = E`, azaz `P` nemelfajuló és `P' = P⁻¹`,
* **13.3. Tétel** — a koordinátasorok kapcsolata: `x' = xP`,
* **13.4. Tétel** — `A^{ℰ',ℱ'} = P⁻¹A^{ℰ,ℱ}S`,
* **13.5. Következmény** — lineáris transzformáció különböző bázisbeli mátrixai
  hasonlóak,
* **13.6. Definíció** — a lineáris leképezés rangja: `r(φ) = dim (Im φ)`,
* **13.7. Tétel** — `r(φ)` megegyezik a leképezés (bármely) bázisbeli mátrixának
  rangjával,
* **13.8. Következmény** — `φ` pontosan akkor bijektív, ha (bármely) bázisbeli mátrixa
  nemelfajuló.
-/

namespace SzaboLinAlg
namespace Ch13

open scoped BigOperators
open SzaboLinAlg.Ch02 SzaboLinAlg.Ch03 SzaboLinAlg.Ch04 SzaboLinAlg.Ch06 SzaboLinAlg.Ch07
  SzaboLinAlg.Ch08 SzaboLinAlg.Ch09 SzaboLinAlg.Ch10 SzaboLinAlg.Ch12

variable {T : Type*} [Field T] {U V : Type*} [AddCommGroup U] [Module T U]
  [AddCommGroup V] [Module T V] {m n : ℕ}

/-! ## Segédlemma -/

/-- Egymásba helyettesített lineáris kombinációk: `∑ⱼ aᵢⱼ(∑ₖ bⱼₖwₖ) = ∑ₖ (AB)ᵢₖwₖ`. -/
theorem kombinacio_szorzat {a b c : ℕ} (A : Matrix' T a b) (B : Matrix' T b c)
    (w : Fin c → V) (i : Fin a) :
    ∑ j, A i j • ∑ k, B j k • w k = ∑ k, (A * B) i k • w k := by
  calc ∑ j, A i j • ∑ k, B j k • w k = ∑ j, ∑ k, (A i j * B j k) • w k := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.smul_sum]
        exact Finset.sum_congr rfl fun k _ => by rw [smul_smul]
    _ = ∑ k, ∑ j, (A i j * B j k) • w k := Finset.sum_comm
    _ = ∑ k, (A * B) i k • w k := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [← Finset.sum_smul]
        rfl

/-- Az egységmátrixszal képzett lineáris kombináció a bázisvektort adja vissza. -/
theorem kombinacio_one {k : ℕ} (v : Fin k → V) (i : Fin k) :
    ∑ j, (1 : Matrix' T k k) i j • v j = v i := by
  simp [Matrix.one_apply, ite_smul]

/-! ## 13.1. Definíció -/

/-- **13.1. Definíció.** A `P = (pᵢⱼ)` mátrix az `ℰ : e₁,…,e_m` bázisról az
`ℰ' : e'₁,…,e'_m` bázisra való *áttérés mátrixa*, ha `eᵢ = ∑ⱼ pᵢⱼe'ⱼ` minden `i`-re. -/
def AtteresMatrixa (e e' : Fin m → U) (P : Matrix' T m m) : Prop :=
  ∀ i, e i = ∑ j, P i j • e' j

/-- Az áttérés mátrixa az identikus leképezés mátrixa a két bázisban. -/
theorem atteresMatrixa_iff_lekepezesMatrixa (e e' : Fin m → U) (P : Matrix' T m m) :
    AtteresMatrixa e e' P ↔ LekepezesMatrixa (id : U → U) e e' P := Iff.rfl

/-- Adott két bázis esetén az áttérés mátrixa létezik és egyértelmű. -/
theorem letezik_egyertelmu_atteres {e e' : Fin m → U} (he' : Bazis T e') :
    ∃! P : Matrix' T m m, AtteresMatrixa e e' P :=
  letezik_egyertelmu_matrix he' id

/-! ## 13.2. Tétel -/

/-- **13.2. Tétel.** Ha `P` az `ℰ`-ről `ℰ'`-re, `P'` pedig az `ℰ'`-ről `ℰ`-re való áttérés
mátrixa, akkor `PP' = P'P = E`; tehát `P` és `P'` nemelfajuló és `P' = P⁻¹`.

*Bizonyítás.* `e = Pe' = P(P'e) = (PP')e`, és mivel `ℰ` bázis, minden vektor
koordinátasora egyértelmű, ezért `PP' = E`; hasonlóan `P'P = E`. -/
theorem atteres_inverze {e e' : Fin m → U} (he : Bazis T e) (he' : Bazis T e')
    {P P' : Matrix' T m m} (hP : AtteresMatrixa e e' P) (hP' : AtteresMatrixa e' e P') :
    Inverze P P' := by
  constructor
  · -- `P'P = E`, mert `e' = P'e = P'(Pe') = (P'P)e'`
    funext j
    refine egyertelmu_eloallitas he'.1 ?_
    rw [kombinacio_one e' j, ← kombinacio_szorzat P' P e' j]
    symm
    calc e' j = ∑ i, P' j i • e i := hP' j
      _ = ∑ i, P' j i • ∑ l, P i l • e' l :=
          Finset.sum_congr rfl fun i _ => by rw [← hP i]
  · -- `PP' = E`, mert `e = Pe' = P(P'e) = (PP')e`
    funext i
    refine egyertelmu_eloallitas he.1 ?_
    rw [kombinacio_one e i, ← kombinacio_szorzat P P' e i]
    symm
    calc e i = ∑ j, P i j • e' j := hP i
      _ = ∑ j, P i j • ∑ l, P' j l • e l :=
          Finset.sum_congr rfl fun j _ => by rw [← hP' j]

/-! ## 13.3. Tétel -/

/-- **13.3. Tétel.** Ha az `u` vektor koordinátasora `ℰ`-ben `x`, `ℰ'`-ben pedig `x'`,
és `P` az áttérés mátrixa `ℰ`-ről `ℰ'`-re, akkor `x' = xP`.

*Bizonyítás.* `x'e' = u = xe = x(Pe') = (xP)e'`, és a koordinátasor egyértelmű. -/
theorem koordinata_atteres {e e' : Fin m → U} (he' : Bazis T e') {P : Matrix' T m m}
    (hP : AtteresMatrixa e e' P) {u : U} {x x' : Fin m → T} (hx : u = ∑ i, x i • e i)
    (hx' : u = ∑ j, x' j • e' j) : x' = fun j => ∑ i, x i * P i j := by
  refine egyertelmu_eloallitas he'.1 ?_
  rw [← hx']
  exact koordinata_transzformacio (T := T) linearisLekepezes_id hP hx

/-! ## 13.4. Tétel, 13.5. Következmény -/

/-- **13.4. Tétel.** Ha `P` az `ℰ`-ről `ℰ'`-re, `S` pedig az `ℱ`-ről `ℱ'`-re való áttérés
mátrixa, továbbá `A`, illetve `A'` a `φ` mátrixa az `(ℰ,ℱ)`, illetve `(ℰ',ℱ')`
bázispárban, akkor `PA' = AS` (azaz `A' = P⁻¹AS`).

*Bizonyítás.* `Af = eφ = (Pe')φ = P(e'φ) = P(A'f')`, ugyanakkor `Af = A(Sf') = (AS)f'`;
mivel `ℱ'` bázis, innen `PA' = AS`. -/
theorem matrixa_baziscsere {f : U → V} (hf : LinearisLekepezes T f)
    {e e' : Fin m → U} {fb fb' : Fin n → V} (hfb' : Bazis T fb')
    {P : Matrix' T m m} {A A' : Matrix' T m n} {S : Matrix' T n n}
    (hP : AtteresMatrixa e e' P) (hS : AtteresMatrixa fb fb' S)
    (hA : LekepezesMatrixa f e fb A) (hA' : LekepezesMatrixa f e' fb' A') :
    P * A' = A * S := by
  funext i
  refine egyertelmu_eloallitas hfb'.1 ?_
  have h1 : f (e i) = ∑ k, (P * A') i k • fb' k := by
    rw [← kombinacio_szorzat P A' fb' i, hP i, map_kombinacio hf]
    exact Finset.sum_congr rfl fun j _ => by rw [hA' j]
  have h2 : f (e i) = ∑ k, (A * S) i k • fb' k := by
    rw [← kombinacio_szorzat A S fb' i, hA i]
    exact Finset.sum_congr rfl fun j _ => by rw [hS j]
  rw [← h1, ← h2]

/-- **13.5. Következmény.** Egy lineáris transzformáció különböző bázisokban felírt
mátrixai hasonlóak: `A' = P⁻¹AP`. -/
theorem hasonlo_baziscsere {f : U → U} (hf : LinearisLekepezes T f) {e e' : Fin m → U}
    (he : Bazis T e) (he' : Bazis T e') {P A A' : Matrix' T m m}
    (hP : AtteresMatrixa e e' P) (hA : LekepezesMatrixa f e e A)
    (hA' : LekepezesMatrixa f e' e' A') : Hasonlo A A' := by
  obtain ⟨P', hP', -⟩ := letezik_egyertelmu_atteres (T := T) (e := e') he
  have hinv : Inverze P P' := atteres_inverze he he' hP hP'
  refine ⟨P, P', hinv, ?_⟩
  have hPA : P * A' = A * P := matrixa_baziscsere hf he' hP hP hA hA'
  calc A' = 1 * A' := (one_mul A').symm
    _ = (P' * P) * A' := by rw [hinv.1]
    _ = P' * (P * A') := by rw [mul_assoc]
    _ = P' * (A * P) := by rw [hPA]
    _ = P' * A * P := by rw [mul_assoc]

/-! ## 13.6. Definíció, 13.7. Tétel -/

/-- **13.6. Definíció.** A `φ` lineáris leképezés *rangja* a képterének dimenziója:
`r(φ) = dim (Im φ)`. -/
def LekepezesRangja {f : U → V} (hf : LinearisLekepezes T f) (r : ℕ) : Prop :=
  Dimenzioja T (kepterAlter hf) r

/-- **13.7. Tétel.** Véges dimenziós vektorterek közötti lineáris leképezés rangja
megegyezik (bármely) bázisbeli mátrixának rangjával.

*Bizonyítás.* A `ψ : V → Tⁿ` koordinátaleképezés izomorfizmus (10.10. Tétel), és `Im φ`
képe `ψ` mellett éppen az `A` sorvektorai által generált altér; ezért
`dim (Im φ) = r_s(A) = r(A)`. -/
theorem lekepezesRangja_eq_rang {f : U → V} (hf : LinearisLekepezes T f)
    {e : Fin m → U} {fb : Fin n → V} (he : Bazis T e) (hfb : Bazis T fb)
    {A : Matrix' T m n} (hA : LekepezesMatrixa f e fb A) :
    LekepezesRangja hf (rang A) := by
  classical
  set Bf : Module.Basis (Fin n) T V := toModuleBasis hfb with hBfdef
  have hBf : ⇑Bf = fb := Module.Basis.coe_mk _ _
  haveI : Module.Finite T V := Module.Finite.of_basis Bf
  set psi : V ≃ₗ[T] (Fin n → T) := Bf.equivFun with hpsi
  have hpsi_apply : ∀ x : Fin n → T, psi (∑ j, x j • fb j) = x := by
    intro x
    have : (∑ j, x j • fb j) = Bf.equivFun.symm x := by
      rw [Module.Basis.equivFun_symm_apply, hBf]
    rw [this, hpsi, LinearEquiv.apply_symm_apply]
  have h1 : kepterAlter hf = Submodule.span T (Set.range fun i => f (e i)) := by
    rw [kepterAlter, LinearMap.range_eq_map, ← span_eq_top_of_generalja he.2,
      Submodule.map_span, ← Set.range_comp]
    rfl
  have h2 : Submodule.map (psi : V →ₗ[T] (Fin n → T)) (kepterAlter hf)
      = Submodule.span T (Set.range (sorRendszer A)) := by
    have hset : (fun i => psi (f (e i))) = sorRendszer A := by
      funext i
      rw [hA i, hpsi_apply]
      rfl
    rw [h1, Submodule.map_span, ← Set.range_comp]
    show Submodule.span T (Set.range fun i => psi (f (e i))) = _
    rw [hset]
  have h3 : Module.finrank T (kepterAlter hf)
      = Module.finrank T (Submodule.map (psi : V →ₗ[T] (Fin n → T)) (kepterAlter hf)) :=
    (Submodule.equivMapOfInjective (psi : V →ₗ[T] (Fin n → T)) psi.injective _).finrank_eq
  refine dimenzioja_of_finrank_eq ?_
  rw [h3, h2, rang_eq_sorRang]
  rfl

/-! ## 13.8. Következmény -/

/-- **13.8. Következmény.** A `φ` lineáris transzformáció pontosan akkor bijektív, ha
(bármely) bázisbeli mátrixa nemelfajuló.

*Bizonyítás.* Ha `φ` bijektív, akkor `dim (Im φ) = dim V = n`, tehát a 13.7. Tétel
szerint `r(A) = n`, azaz `|A| ≠ 0`. Megfordítva, `|A| ≠ 0` esetén `dim (Im φ) = n`,
így `Im φ = V`, tehát `φ` szürjektív, és a 10.4. Következmény szerint bijektív. -/
theorem bijektiv_iff_det_ne_zero {f : U → U} (hf : LinearisLekepezes T f)
    {e : Fin m → U} (he : Bazis T e) {A : Matrix' T m m}
    (hA : LekepezesMatrixa f e e A) : Function.Bijective f ↔ det' A ≠ 0 := by
  classical
  set Be : Module.Basis (Fin m) T U := toModuleBasis he with hBedef
  have hBe : ⇑Be = e := Module.Basis.coe_mk _ _
  set psi : U ≃ₗ[T] (Fin m → T) := Be.equivFun with hpsi
  have hpsi_apply : ∀ x : Fin m → T, psi (∑ j, x j • e j) = x := by
    intro x
    have : (∑ j, x j • e j) = Be.equivFun.symm x := by
      rw [Module.Basis.equivFun_symm_apply, hBe]
    rw [this, hpsi, LinearEquiv.apply_symm_apply]
  have hkonj : ∀ u : U, psi (f u) = Matrix.vecMul (psi u) A := by
    intro u
    have hu : u = ∑ i, psi u i • e i := by
      conv_lhs => rw [← LinearEquiv.symm_apply_apply psi u]
      rw [hpsi, Module.Basis.equivFun_symm_apply, hBe]
    rw [koordinata_transzformacio hf hA hu, hpsi_apply]
    rfl
  have hinj : Function.Injective f ↔
      Function.Injective (fun x : Fin m → T => Matrix.vecMul x A) := by
    constructor
    · intro h x y hxy
      have hfx : f (psi.symm x) = f (psi.symm y) := by
        apply psi.injective
        rw [hkonj, hkonj, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
        simpa using hxy
      simpa using congrArg psi (h hfx)
    · intro h u v huv
      apply psi.injective
      apply h
      show Matrix.vecMul (psi u) A = Matrix.vecMul (psi v) A
      rw [← hkonj, ← hkonj, huv]
  have hdim : Dimenzioja T U m := ⟨e, he⟩
  rw [Function.Bijective, ← injektiv_iff_szurjektiv hf hdim, and_self, hinj,
    Matrix.vecMul_injective_iff_isUnit, det'_eq_det]
  rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]

end Ch13
end SzaboLinAlg
