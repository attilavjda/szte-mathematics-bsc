import LinearisAlgebra.Ch09_MatrixRang

/-!
# Szabó László: Bevezetés a lineáris algebrába — 10. fejezet

**Lineáris leképezések és lineáris transzformációk. Vektorterek izomorfizmusa**
(a jegyzet 53–58. oldala).

* **10.1. Definíció** — lineáris leképezés, mag (`Ker`), képtér (`Im`), lineáris
  transzformáció, izomorfizmus,
* **10.2. Tétel** — `0φ = 0`; a mag és a képtér altér; injektivitás ⟺ `Ker φ = {0}`;
  generátorrendszer képe generátorrendszer a képtérben,
* **10.3. Lineáris leképezések dimenziótétele** — `dim U = dim (Ker φ) + dim (Im φ)`,
* **10.4. Következmény** — véges dimenziós téren egy lineáris transzformáció pontosan
  akkor injektív, ha szürjektív,
* **10.5. Tétel** — az `Ax = 0` homogén egyenletrendszer megoldásainak halmaza
  `(n − r(A))`-dimenziós altér, és `|A| = 0` esetén van nemtriviális megoldás,
* **10.6. Definíció** — fundamentális megoldásrendszer (alaprendszer),
* **10.7. Tétel** — lineáris leképezések szorzata és (bijektív esetben) inverze is
  lineáris,
* **10.8. Definíció, 10.9. Tétel** — izomorfia; az izomorfia ekvivalenciareláció,
* **10.10. Tétel** — minden `n`-dimenziós vektortér izomorf `Tⁿ`-nel.

A könyv a leképezéseket jobbról írja (`uφ`); itt a szokásos `φ u` írásmódot használjuk.
-/

namespace SzaboLinAlg
namespace Ch10

open scoped BigOperators
open SzaboLinAlg.Ch02 SzaboLinAlg.Ch03 SzaboLinAlg.Ch05 SzaboLinAlg.Ch06 SzaboLinAlg.Ch07
  SzaboLinAlg.Ch08 SzaboLinAlg.Ch09

variable {T : Type*} [Field T] {U V W : Type*} [AddCommGroup U] [Module T U]
  [AddCommGroup V] [Module T V] [AddCommGroup W] [Module T W]

/-! ## 10.1. Definíció -/

/-- **10.1. Definíció.** A `φ : U → V` leképezés *lineáris leképezés*, ha bármely
`u, v ∈ U` és `λ ∈ T` esetén `(u + v)φ = uφ + vφ` és `(λu)φ = λ(uφ)`. -/
def LinearisLekepezes (T : Type*) [Field T] {U V : Type*} [AddCommGroup U] [Module T U]
    [AddCommGroup V] [Module T V] (f : U → V) : Prop :=
  (∀ u v : U, f (u + v) = f u + f v) ∧ ∀ (l : T) (u : U), f (l • u) = l • f u

/-- **10.1. Definíció.** A `φ` lineáris leképezés *magja*: `Ker φ = {u ∈ U : uφ = 0}`. -/
def Mag (f : U → V) : Set U := {u | f u = 0}

/-- **10.1. Definíció.** A `φ` lineáris leképezés *képtere*: `Im φ = {uφ : u ∈ U}`. -/
def Kepter (f : U → V) : Set V := {v | ∃ u, f u = v}

/-- **10.1. Definíció.** A `V` vektortér *lineáris transzformációi* a `V → V` lineáris
leképezések. -/
def LinearisTranszformacio (T : Type*) [Field T] {V : Type*} [AddCommGroup V] [Module T V]
    (f : V → V) : Prop := LinearisLekepezes T f

/-- **10.1. Definíció.** A bijektív lineáris leképezés (vektortér-)*izomorfizmus*. -/
def Izomorfizmus (T : Type*) [Field T] {U V : Type*} [AddCommGroup U] [Module T U]
    [AddCommGroup V] [Module T V] (f : U → V) : Prop :=
  LinearisLekepezes T f ∧ Function.Bijective f

/-- A könyvbeli lineáris leképezés fogalma megegyezik a Mathlib `U →ₗ[T] V` fogalmával. -/
def toLin {f : U → V} (hf : LinearisLekepezes T f) : U →ₗ[T] V :=
  { toFun := f, map_add' := hf.1, map_smul' := hf.2 }

@[simp] theorem toLin_apply {f : U → V} (hf : LinearisLekepezes T f) (u : U) :
    toLin hf u = f u := rfl

theorem linearisLekepezes_iff_linearMap (f : U → V) :
    LinearisLekepezes T f ↔ ∃ g : U →ₗ[T] V, ⇑g = f :=
  ⟨fun hf => ⟨toLin hf, rfl⟩, by
    rintro ⟨g, rfl⟩; exact ⟨fun u v => g.map_add u v, fun l u => g.map_smul l u⟩⟩

/-- Az identikus leképezés lineáris transzformáció. -/
theorem linearisLekepezes_id : LinearisLekepezes T (id : V → V) :=
  ⟨fun _ _ => rfl, fun _ _ => rfl⟩

/-- A minden vektorhoz a nullvektort rendelő leképezés lineáris. -/
theorem linearisLekepezes_zero : LinearisLekepezes T (fun _ : U => (0 : V)) :=
  ⟨fun _ _ => by simp, fun l _ => by simp⟩

/-- Tetszőleges `c` skalár esetén a `v ↦ cv` leképezés lineáris transzformáció. -/
theorem linearisLekepezes_smul (c : T) : LinearisLekepezes T (fun v : V => c • v) :=
  ⟨fun u v => by simp [smul_add], fun l u => smul_comm c l u⟩

/-! ## 10.2. Tétel -/

/-- **(10.2.1)** `0φ = 0`, hiszen `0φ = (0·0)φ = 0(0φ) = 0`. -/
theorem map_nullvektor {f : U → V} (hf : LinearisLekepezes T f) : f 0 = 0 := by
  have h := hf.2 (0 : T) 0
  rwa [zero_smul, zero_smul] at h

theorem map_neg {f : U → V} (hf : LinearisLekepezes T f) (u : U) : f (-u) = -f u := by
  have h := hf.2 (-1 : T) u
  rwa [neg_one_smul, neg_one_smul] at h

theorem map_sub {f : U → V} (hf : LinearisLekepezes T f) (u v : U) :
    f (u - v) = f u - f v := by
  rw [sub_eq_add_neg, hf.1, map_neg hf, ← sub_eq_add_neg]

/-- **(10.2.2)** `Ker φ` altér `U`-ban. -/
theorem alter_mag {f : U → V} (hf : LinearisLekepezes T f) : Alter T (Mag f) := by
  refine ⟨⟨0, map_nullvektor hf⟩, ?_, ?_⟩
  · intro u hu v hv
    show f (u + v) = 0
    rw [hf.1, hu, hv, add_zero]
  · intro l u hu
    show f (l • u) = 0
    rw [hf.2, hu, smul_zero]

/-- **(10.2.2)** `Im φ` altér `V`-ben. -/
theorem alter_kepter {f : U → V} (hf : LinearisLekepezes T f) : Alter T (Kepter f) := by
  refine ⟨⟨0, ⟨0, map_nullvektor hf⟩⟩, ?_, ?_⟩
  · rintro u ⟨a, rfl⟩ v ⟨b, rfl⟩
    exact ⟨a + b, hf.1 a b⟩
  · rintro l u ⟨a, rfl⟩
    exact ⟨l • a, hf.2 l a⟩

/-- **(10.2.3)** `φ` akkor és csak akkor injektív, ha `Ker φ = {0}`.

*Bizonyítás.* Ha `φ` injektív és `uφ = 0 = 0φ`, akkor `u = 0`. Megfordítva, ha
`Ker φ = {0}` és `uφ = vφ`, akkor `(u − v)φ = 0`, tehát `u − v ∈ Ker φ = {0}`. -/
theorem injektiv_iff_mag_zero {f : U → V} (hf : LinearisLekepezes T f) :
    Function.Injective f ↔ Mag f = {0} := by
  constructor
  · intro hinj
    ext u
    constructor
    · intro hu
      have : f u = f 0 := by rw [hu, map_nullvektor hf]
      simpa using hinj this
    · rintro rfl
      exact map_nullvektor hf
  · intro hker u v huv
    have : u - v ∈ Mag f := by
      show f (u - v) = 0
      rw [map_sub hf, huv, sub_self]
    rw [hker] at this
    exact sub_eq_zero.1 this

/-- Generátorrendszer esetén a Mathlib-értelemben vett generált részmodulus az egész tér. -/
theorem span_eq_top_of_generalja {k : ℕ} {v : Fin k → V} (hv : Generalja T v) :
    Submodule.span T (Set.range v) = ⊤ := by
  apply SetLike.coe_injective
  rw [← generalt_eq_span, hv]
  rfl

/-- **(10.2.4)** Ha `u₁,…,u_k` generátorrendszer `U`-ban, akkor `u₁φ,…,u_kφ`
generátorrendszer `Im φ`-ben. -/
theorem generalt_kepter {f : U → V} (hf : LinearisLekepezes T f) {k : ℕ} {u : Fin k → U}
    (hu : Generalja T u) : Generalt T (Set.range fun i => f (u i)) = Kepter f := by
  have hkep : (Set.range fun i => f (u i)) = (toLin hf) '' Set.range u := by
    rw [← Set.range_comp]; rfl
  rw [generalt_eq_span, hkep, Submodule.span_image, span_eq_top_of_generalja hu,
    Submodule.map_top]
  ext v
  simp [Kepter, LinearMap.mem_range, eq_comm]

/-! ## 10.3. A lineáris leképezések dimenziótétele -/

/-- Bázisból Mathlib-bázis. -/
noncomputable def toModuleBasis {k : ℕ} {v : Fin k → V} (hv : Bazis T v) :
    Module.Basis (Fin k) T V :=
  Module.Basis.mk ((linFuggetlen_iff_linearIndependent v).1 hv.1)
    (by rw [span_eq_top_of_generalja hv.2])

/-- A könyvbeli dimenzió megegyezik a Mathlib `Module.finrank` fogalmával. -/
theorem finrank_of_dimenzioja {n : ℕ} (h : Dimenzioja T V n) : Module.finrank T V = n := by
  obtain ⟨v, hv⟩ := h
  simpa using Module.finrank_eq_card_basis (toModuleBasis hv)

theorem finite_of_dimenzioja {n : ℕ} (h : Dimenzioja T V n) : Module.Finite T V := by
  obtain ⟨v, hv⟩ := h
  exact Module.Finite.of_basis (toModuleBasis hv)

/-- Mathlib-bázisból a könyv értelmében vett bázis. -/
theorem bazis_of_moduleBasis {k : ℕ} (B : Module.Basis (Fin k) T V) : Bazis T ⇑B := by
  refine ⟨(linFuggetlen_iff_linearIndependent _).2 B.linearIndependent, ?_⟩
  rw [Generalja, generalt_eq_span, B.span_eq]
  simp

theorem dimenzioja_of_finrank_eq [Module.Finite T V] {n : ℕ} (h : Module.finrank T V = n) :
    Dimenzioja T V n :=
  ⟨_, bazis_of_moduleBasis (Module.finBasisOfFinrankEq T V h)⟩

/-- A `φ` lineáris leképezés magja mint altér (részmodulus). -/
def magAlter {f : U → V} (hf : LinearisLekepezes T f) : Submodule T U := LinearMap.ker (toLin hf)

/-- A `φ` lineáris leképezés képtere mint altér (részmodulus). -/
def kepterAlter {f : U → V} (hf : LinearisLekepezes T f) : Submodule T V :=
  LinearMap.range (toLin hf)

@[simp] theorem coe_magAlter {f : U → V} (hf : LinearisLekepezes T f) :
    (magAlter hf : Set U) = Mag f := rfl

@[simp] theorem coe_kepterAlter {f : U → V} (hf : LinearisLekepezes T f) :
    (kepterAlter hf : Set V) = Kepter f := rfl

/-- **10.3. Lineáris leképezések dimenziótétele.** Ha `U` véges dimenziós, akkor
`dim U = dim (Ker φ) + dim (Im φ)`.

*Bizonyítás (a könyv szerint).* Legyen `u₁,…,u_k` a `Ker φ` bázisa, és egészítsük ki azt
`u₁,…,u_k,u_{k+1},…,u_n` bázissá `U`-ban. Elég belátni, hogy `u_{k+1}φ,…,u_nφ` bázis
`Im φ`-ben: a lineáris függetlenség a bázis-tulajdonságból, a generálás pedig a (10.2.4)
állításból következik, a nullvektorokat elhagyva. (A formalizált bizonyítás ugyanezt a
rang–nullitás összefüggést a Mathlib `LinearMap.finrank_range_add_finrank_ker` tételéből
veszi át, a könyvbeli dimenziófogalmat a `finrank`-kel összekötő híd-lemmákon
keresztül.) -/
theorem dimenziotetel {f : U → V} (hf : LinearisLekepezes T f) {n k m : ℕ}
    (hU : Dimenzioja T U n) (hker : Dimenzioja T (magAlter hf) k)
    (him : Dimenzioja T (kepterAlter hf) m) : n = k + m := by
  haveI : Module.Finite T U := finite_of_dimenzioja hU
  have h1 : Module.finrank T U = n := finrank_of_dimenzioja hU
  have h2 : Module.finrank T (magAlter hf) = k := finrank_of_dimenzioja hker
  have h3 : Module.finrank T (kepterAlter hf) = m := finrank_of_dimenzioja him
  have h := LinearMap.finrank_range_add_finrank_ker (toLin hf)
  rw [show LinearMap.range (toLin hf) = kepterAlter hf from rfl,
    show LinearMap.ker (toLin hf) = magAlter hf from rfl, h2, h3, h1] at h
  omega

/-! ## 10.4. Következmény -/

/-- **10.4. Következmény.** Véges dimenziós `V` esetén `φ ∈ Hom(V,V)` pontosan akkor
injektív, ha szürjektív. -/
theorem injektiv_iff_szurjektiv {f : V → V} (hf : LinearisLekepezes T f) {n : ℕ}
    (hV : Dimenzioja T V n) : Function.Injective f ↔ Function.Surjective f := by
  haveI : Module.Finite T V := finite_of_dimenzioja hV
  exact LinearMap.injective_iff_surjective (f := toLin hf)

/-! ## 10.5. Tétel, 10.6. Definíció: homogén egyenletrendszerek -/

variable {m n : ℕ}

/-- Az `Ax = 0` homogén egyenletrendszer megoldásainak altere. -/
noncomputable def megoldasAlter (A : Matrix' T m n) : Submodule T (Fin n → T) :=
  LinearMap.ker (Matrix.mulVecLin A)

theorem mem_megoldasAlter (A : Matrix' T m n) (x : Fin n → T) :
    x ∈ megoldasAlter A ↔ Megoldasa A 0 x := by
  rw [megoldasa_iff_mulVec]
  simp [megoldasAlter, LinearMap.mem_ker]

/-- **10.5. Tétel.** Az `Ax = 0` homogén lineáris egyenletrendszer megoldásainak halmaza
`(n − r(A))`-dimenziós altér a `Tⁿ` vektortérben.

*Bizonyítás.* Az `x ↦ Ax` leképezés lineáris, magja éppen a megoldások halmaza, képtere
pedig az oszlopvektorok által generált altér, melynek dimenziója `r(A)`; innen a 10.3.
dimenziótétel adja az állítást. -/
theorem homogen_megoldas_dimenzioja (A : Matrix' T m n) :
    Dimenzioja T (megoldasAlter A) (n - rang A) := by
  have h := LinearMap.finrank_range_add_finrank_ker (Matrix.mulVecLin A)
  have hr : Module.finrank T (LinearMap.range (Matrix.mulVecLin A)) = rang A := by
    rw [rang_eq_rank]; rfl
  have hn : Module.finrank T (Fin n → T) = n := by simp
  rw [hr, hn] at h
  exact dimenzioja_of_finrank_eq (by rw [megoldasAlter]; omega)

/-- **10.5. Tétel (második rész).** Ha `|A| = 0`, akkor az `Ax = 0` homogén
egyenletrendszernek van nemtriviális megoldása. -/
theorem van_nemtrivialis_megoldas {A : Matrix' T n n} (hA : det' A = 0) :
    ∃ x : Fin n → T, x ≠ 0 ∧ Megoldasa A 0 x := by
  have hdet : A.det = 0 := by rw [← det'_eq_det]; exact hA
  obtain ⟨x, hx0, hx⟩ := (Matrix.exists_mulVec_eq_zero_iff (M := A)).2 hdet
  exact ⟨x, hx0, (megoldasa_iff_mulVec A 0 x).2 hx⟩

/-- **10.6. Definíció.** A homogén egyenletrendszer megoldásaltere bázisait
*fundamentális megoldásrendszernek* (alaprendszernek) nevezzük. -/
def Alaprendszer (A : Matrix' T m n) {k : ℕ} (v : Fin k → megoldasAlter A) : Prop :=
  Bazis T v

/-! ## 10.7. Tétel -/

/-- **(10.7.1)** Lineáris leképezések szorzata (kompozíciója) is lineáris. -/
theorem linearisLekepezes_comp {f : U → V} {g : V → W} (hf : LinearisLekepezes T f)
    (hg : LinearisLekepezes T g) : LinearisLekepezes T (fun u => g (f u)) :=
  ⟨fun u v => by simp only [hf.1, hg.1], fun l u => by simp only [hf.2, hg.2]⟩

/-- **(10.7.2)** Bijektív lineáris leképezés inverze is lineáris. -/
theorem linearisLekepezes_inverz {f : U → V} (hf : LinearisLekepezes T f)
    (hinj : Function.Injective f) {g : V → U} (hg : Function.RightInverse g f) :
    LinearisLekepezes T g := by
  refine ⟨fun u v => hinj ?_, fun l u => hinj ?_⟩
  · rw [hg (u + v), hf.1, hg u, hg v]
  · rw [hg (l • u), hf.2, hg u]

/-! ## 10.8. Definíció, 10.9. Tétel: izomorfia -/

/-- **10.8. Definíció.** `U` *izomorf* `V`-vel, ha van `U → V` izomorfizmus. -/
def Izomorf (T : Type*) [Field T] (U V : Type*) [AddCommGroup U] [Module T U]
    [AddCommGroup V] [Module T V] : Prop := ∃ f : U → V, Izomorfizmus T f

/-- **10.9. Tétel.** Az izomorfia reflexív. -/
theorem izomorf_refl : Izomorf T V V :=
  ⟨id, linearisLekepezes_id, Function.bijective_id⟩

/-- **10.9. Tétel.** Az izomorfia szimmetrikus. -/
theorem izomorf_symm (h : Izomorf T U V) : Izomorf T V U := by
  obtain ⟨f, hf, hbij⟩ := h
  obtain ⟨g, hleft, hright⟩ := Function.bijective_iff_has_inverse.1 hbij
  exact ⟨g, linearisLekepezes_inverz hf hbij.1 hright,
    hright.injective, hleft.surjective⟩

/-- **10.9. Tétel.** Az izomorfia tranzitív. -/
theorem izomorf_trans (h₁ : Izomorf T U V) (h₂ : Izomorf T V W) : Izomorf T U W := by
  obtain ⟨f, hf, hfb⟩ := h₁
  obtain ⟨g, hg, hgb⟩ := h₂
  exact ⟨fun u => g (f u), linearisLekepezes_comp hf hg, hgb.comp hfb⟩

/-! ## 10.10. Tétel -/

/-- **10.10. Tétel.** Ha `V` a `T` számtest feletti `n`-dimenziós vektortér, akkor `V`
izomorf a `Tⁿ` vektortérrel.

*Bizonyítás.* Legyen `e₁,…,e_n` bázis `V`-ben, és legyen
`φ : Tⁿ → V, (λ₁,…,λ_n) ↦ ∑ λᵢeᵢ`. Ez szürjektív, mert `e₁,…,e_n` generátorrendszer,
injektív, mert a bázis szerinti előállítás egyértelmű, és nyilván lineáris. -/
theorem izomorf_tuple {n : ℕ} (hV : Dimenzioja T V n) : Izomorf T (Fin n → T) V := by
  obtain ⟨v, hv⟩ := hV
  refine ⟨fun l => ∑ i, l i • v i, ⟨⟨?_, ?_⟩, ?_, ?_⟩⟩
  · intro a b
    simp [add_smul, Finset.sum_add_distrib]
  · intro c a
    simp [Finset.smul_sum, mul_smul]
  · intro a b hab
    exact egyertelmu_eloallitas hv.1 hab
  · intro x
    obtain ⟨g, hg, -⟩ := koordinatak_egyertelmuek hv x
    exact ⟨g, hg.symm⟩

/-- **10.10. Tétel.** Bármely két `T` feletti `n`-dimenziós vektortér izomorf egymással. -/
theorem izomorf_of_dimenzioja_eq {n : ℕ} (hU : Dimenzioja T U n) (hV : Dimenzioja T V n) :
    Izomorf T U V :=
  izomorf_trans (izomorf_symm (izomorf_tuple hU)) (izomorf_tuple hV)

/-- **10.10. Tétel.** Izomorf vektorterek dimenziója megegyezik. -/
theorem dimenzioja_of_izomorf {n : ℕ} (h : Izomorf T U V) (hU : Dimenzioja T U n) :
    Dimenzioja T V n := by
  obtain ⟨f, hf, hbij⟩ := h
  haveI : Module.Finite T U := finite_of_dimenzioja hU
  let e : U ≃ₗ[T] V := LinearEquiv.ofBijective (toLin hf) hbij
  haveI : Module.Finite T V := Module.Finite.equiv e
  exact dimenzioja_of_finrank_eq (by rw [← e.finrank_eq, finrank_of_dimenzioja hU])

end Ch10
end SzaboLinAlg
