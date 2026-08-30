import LinearisAlgebra.Ch05_Egyenletrendszerek

/-!
# Szabó László: Bevezetés a lineáris algebrába — 5. fejezet (folytatás): Gauss-elimináció

Ez a modul az 5. fejezet hiányzó részét, a **Gauss-kiküszöbölést (Gauss-eliminációt)**
formalizálja.

Az egyenletrendszert a **bővített mátrixa sorainak listájaként** ábrázoljuk: egy `n`
ismeretlenes egyenlet bővített sora egy `Fin (n+1) → T` vektor, melynek utolsó
koordinátája az egyenlet jobb oldalán álló konstans. Erre az ábrázolásra azért van
szükség, mert az **(5.2.1)** elemi átalakítás (a csupa nulla sor elhagyása) megváltoztatja
az egyenletek számát.

* **5.2. Definíció** — `ElemiLepes`: a négy elemi átalakítás (nulla sor elhagyása, sor
  szorzása nem nulla skalárral, egy sorhoz egy másik sor skalárszorosának hozzáadása,
  két sor felcserélése), valamint `ElemiAtalakitasok` ezek véges sorozata.
  A **5.2. Definíció** utáni észrevétel: az elemi átalakítások ekvivalens
  egyenletrendszerbe visznek át (`ElemiLepes.megoldas_iff`,
  `ElemiAtalakitasok.megoldas_iff`).
* **5.3. Definíció** — `Lepcsos`: lépcsős alakú egyenletrendszer (nincs csupa nulla sor;
  minden sorban az első nem nulla elem 1-es, és ezen 1-esek oszlopában a többi elem
  nulla; az első nem nulla elemek balról jobbra haladva egyre hátrébb vannak).
* **5.4. Tétel** — `letezik_lepcsos`: minden egyenletrendszer elemi átalakításokkal
  lépcsős alakra hozható. (A könyv a nullmátrix esetét kizárja; az itteni ábrázolásban
  a csupa nulla sorok elhagyhatók, így az üres — vagyis semmilyen megkötést nem
  tartalmazó — rendszer is lépcsős alakú, ezért a tétel kivétel nélkül kimondható.)
* **5.5. Gauss-elimináció** — `gauss_elimination`: minden egyenletrendszerhez van vele
  *ekvivalens* lépcsős alakú egyenletrendszer.
-/

namespace SzaboLinAlg
namespace Ch05

open scoped BigOperators

variable {T : Type*} [Field T] {n : ℕ}

/-! ## Az ábrázolás -/

/-- Egy `n` ismeretlenes lineáris egyenlet *bővített sora*: az együtthatók után az
utolsó koordináta az egyenlet jobb oldalán álló konstans. -/
abbrev Sor (T : Type*) (n : ℕ) := Fin (n + 1) → T

/-- Egyenletrendszer: a bővített mátrix sorainak listája. -/
abbrev Rendszer (T : Type*) (n : ℕ) := List (Sor T n)

/-- A `c` szám-`n`-es megoldása a bővített `r` sorral megadott egyenletnek. -/
def SorMegoldasa (r : Sor T n) (c : Fin n → T) : Prop :=
  ∑ j : Fin n, r j.castSucc * c j = r (Fin.last n)

/-- A `c` szám-`n`-es megoldása az `L` egyenletrendszernek, ha minden egyenletét
kielégíti. -/
def RendszerMegoldasa (L : Rendszer T n) (c : Fin n → T) : Prop := ∀ r ∈ L, SorMegoldasa r c

/-! ## 5.2. Definíció: elemi átalakítások -/

/-- **5.2. Definíció.** Az egyenletrendszer (bővített mátrixa sorain végrehajtott) elemi
átalakításai: (5.2.a) csupa nulla sor elhagyása, (5.2.b) egy sor szorzása nem nulla
skalárral, (5.2.c) egy sorhoz egy másik sor skalárszorosának hozzáadása (a másik sor
állhat lejjebb vagy feljebb is), (5.2.d) két sor felcserélése. -/
inductive ElemiLepes : Rendszer T n → Rendszer T n → Prop
  | nulla_sor (L₁ L₂ : Rendszer T n) : ElemiLepes (L₁ ++ (0 : Sor T n) :: L₂) (L₁ ++ L₂)
  | szoroz (L₁ L₂ : Rendszer T n) (r : Sor T n) {lam : T} (h : lam ≠ 0) :
      ElemiLepes (L₁ ++ r :: L₂) (L₁ ++ (lam • r) :: L₂)
  | hozzaad_le (L₁ L₂ L₃ : Rendszer T n) (r s : Sor T n) (lam : T) :
      ElemiLepes (L₁ ++ r :: (L₂ ++ s :: L₃)) (L₁ ++ (r + lam • s) :: (L₂ ++ s :: L₃))
  | hozzaad_fel (L₁ L₂ L₃ : Rendszer T n) (r s : Sor T n) (lam : T) :
      ElemiLepes (L₁ ++ s :: (L₂ ++ r :: L₃)) (L₁ ++ s :: (L₂ ++ (r + lam • s) :: L₃))
  | csere (L₁ L₂ L₃ : Rendszer T n) (r s : Sor T n) :
      ElemiLepes (L₁ ++ r :: (L₂ ++ s :: L₃)) (L₁ ++ s :: (L₂ ++ r :: L₃))

/-- Elemi átalakítások véges sorozata. -/
abbrev ElemiAtalakitasok : Rendszer T n → Rendszer T n → Prop := Relation.ReflTransGen ElemiLepes

/-! ## Az elemi átalakítások ekvivalens rendszerbe visznek -/

theorem sorMegoldasa_zero (c : Fin n → T) : SorMegoldasa (0 : Sor T n) c := by
  simp [SorMegoldasa]

theorem sorMegoldasa_smul {r : Sor T n} {c : Fin n → T} {lam : T} (h : SorMegoldasa r c) :
    SorMegoldasa (lam • r) c := by
  simp only [SorMegoldasa, Pi.smul_apply, smul_eq_mul] at *
  rw [← h, Finset.mul_sum]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem sorMegoldasa_smul_iff {r : Sor T n} {c : Fin n → T} {lam : T} (hlam : lam ≠ 0) :
    SorMegoldasa (lam • r) c ↔ SorMegoldasa r c := by
  refine ⟨fun h => ?_, sorMegoldasa_smul⟩
  have := sorMegoldasa_smul (lam := lam⁻¹) h
  rwa [smul_smul, inv_mul_cancel₀ hlam, one_smul] at this

theorem sorMegoldasa_add {r s : Sor T n} {c : Fin n → T} (hr : SorMegoldasa r c)
    (hs : SorMegoldasa s c) : SorMegoldasa (r + s) c := by
  simp only [SorMegoldasa, Pi.add_apply, add_mul, Finset.sum_add_distrib] at *
  rw [hr, hs]

theorem sorMegoldasa_add_smul_iff {r s : Sor T n} {c : Fin n → T} {lam : T}
    (hs : SorMegoldasa s c) : SorMegoldasa (r + lam • s) c ↔ SorMegoldasa r c := by
  refine ⟨fun h => ?_, fun h => sorMegoldasa_add h (sorMegoldasa_smul hs)⟩
  have := sorMegoldasa_add h (sorMegoldasa_smul (lam := -lam) hs)
  have heq : r + lam • s + (-lam) • s = r := by
    funext j; simp
  rwa [heq] at this

/-- **5.2. Definíció (észrevétel).** Az elemi átalakítások ekvivalens egyenletrendszerbe
viszik át az egyenletrendszert. -/
theorem ElemiLepes.megoldas_iff {L L' : Rendszer T n} (h : ElemiLepes L L') (c : Fin n → T) :
    RendszerMegoldasa L c ↔ RendszerMegoldasa L' c := by
  induction h with
  | nulla_sor L₁ L₂ =>
      simp only [RendszerMegoldasa, List.forall_mem_append, List.forall_mem_cons]
      exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, sorMegoldasa_zero c, h.2⟩⟩
  | szoroz L₁ L₂ r hlam =>
      simp only [RendszerMegoldasa, List.forall_mem_append, List.forall_mem_cons,
        sorMegoldasa_smul_iff hlam]
  | hozzaad_le L₁ L₂ L₃ r s lam =>
      simp only [RendszerMegoldasa, List.forall_mem_append, List.forall_mem_cons]
      constructor
      · rintro ⟨h1, h2, h3, h4, h5⟩
        exact ⟨h1, (sorMegoldasa_add_smul_iff h4).2 h2, h3, h4, h5⟩
      · rintro ⟨h1, h2, h3, h4, h5⟩
        exact ⟨h1, (sorMegoldasa_add_smul_iff h4).1 h2, h3, h4, h5⟩
  | hozzaad_fel L₁ L₂ L₃ r s lam =>
      simp only [RendszerMegoldasa, List.forall_mem_append, List.forall_mem_cons]
      constructor
      · rintro ⟨h1, h2, h3, h4, h5⟩
        exact ⟨h1, h2, h3, (sorMegoldasa_add_smul_iff h2).2 h4, h5⟩
      · rintro ⟨h1, h2, h3, h4, h5⟩
        exact ⟨h1, h2, h3, (sorMegoldasa_add_smul_iff h2).1 h4, h5⟩
  | csere L₁ L₂ L₃ r s =>
      simp only [RendszerMegoldasa, List.forall_mem_append, List.forall_mem_cons]
      tauto

theorem ElemiAtalakitasok.megoldas_iff {L L' : Rendszer T n} (h : ElemiAtalakitasok L L')
    (c : Fin n → T) : RendszerMegoldasa L c ↔ RendszerMegoldasa L' c := by
  induction h with
  | refl => rfl
  | tail _ hstep ih => exact ih.trans (hstep.megoldas_iff c)

/-! ## Segédállítások az elemi lépésekről -/

/-- Ha egy rendszert elemi lépéssel átalakítunk, akkor ugyanez érvényes egy elé írt
sorral kibővítve is. -/
theorem ElemiLepes.cons (a : Sor T n) {L L' : Rendszer T n} (h : ElemiLepes L L') :
    ElemiLepes (a :: L) (a :: L') := by
  induction h with
  | nulla_sor L₁ L₂ => exact ElemiLepes.nulla_sor (a :: L₁) L₂
  | szoroz L₁ L₂ r hlam => exact ElemiLepes.szoroz (a :: L₁) L₂ r hlam
  | hozzaad_le L₁ L₂ L₃ r s lam => exact ElemiLepes.hozzaad_le (a :: L₁) L₂ L₃ r s lam
  | hozzaad_fel L₁ L₂ L₃ r s lam => exact ElemiLepes.hozzaad_fel (a :: L₁) L₂ L₃ r s lam
  | csere L₁ L₂ L₃ r s => exact ElemiLepes.csere (a :: L₁) L₂ L₃ r s

theorem ElemiAtalakitasok.cons (a : Sor T n) {L L' : Rendszer T n} (h : ElemiAtalakitasok L L') :
    ElemiAtalakitasok (a :: L) (a :: L') := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact ih.tail (hstep.cons a)

/-- Az (5.2.c) átalakítás speciális esete: az első sorhoz hozzáadjuk egy alatta álló sor
skalárszorosát. -/
theorem ElemiLepes.head_add {a s : Sor T n} {M : Rendszer T n} (hs : s ∈ M) (lam : T) :
    ElemiLepes (a :: M) ((a + lam • s) :: M) := by
  obtain ⟨L₂, L₃, rfl⟩ := List.append_of_mem hs
  exact ElemiLepes.hozzaad_le [] L₂ L₃ a s lam

/-- Az (5.2.c) átalakítás ismételt alkalmazása: az első sor alkalmas skalárszorosait
levonva a többi sorból egyszerre „megtisztítjuk" a rendszert. -/
theorem letezik_oszlop_tisztitas (s : Sor T n) (lam : Sor T n → T) :
    ∀ (M P : Rendszer T n),
      ElemiAtalakitasok (s :: (P ++ M)) (s :: (P ++ M.map (fun t => t + lam t • s))) := by
  intro M
  induction M with
  | nil =>
      intro P
      simp only [List.map_nil, List.append_nil]
      exact Relation.ReflTransGen.refl
  | cons t M ih =>
      intro P
      have step : ElemiLepes (s :: (P ++ t :: M)) (s :: (P ++ (t + lam t • s) :: M)) :=
        ElemiLepes.hozzaad_fel [] P M t s (lam t)
      have rest := ih (P ++ [t + lam t • s])
      simp only [List.append_assoc, List.singleton_append] at rest
      simpa using Relation.ReflTransGen.head step rest

/-! ## 5.3. Definíció: lépcsős alak -/

/-- A `j` oszlopindex az `r` sor *vezető eleme*: `r j = 1`, és `j` előtt minden elem
nulla (az 5.3.2. és 5.3.3. feltételek alapfogalma). -/
def Vezeto (r : Sor T n) (j : Fin (n + 1)) : Prop := r j = 1 ∧ ∀ c, c < j → r c = 0

theorem Vezeto.unique {r : Sor T n} {j j' : Fin (n + 1)} (h : Vezeto r j) (h' : Vezeto r j') :
    j = j' := by
  rcases lt_trichotomy j j' with hlt | heq | hgt
  · exact absurd (h'.2 j hlt) (by rw [h.1]; exact one_ne_zero)
  · exact heq
  · exact absurd (h.2 j' hgt) (by rw [h'.1]; exact one_ne_zero)

/-- **5.3. Definíció.** Az egyenletrendszer *lépcsős alakú*, ha (5.3.1) nincs csupa nulla
sora, (5.3.2) minden sorban az első nem nulla elem 1-es, és ezen 1-esek oszlopában a
többi elem mind nulla, továbbá (5.3.3) minden sorban az első nem nulla elem hátrébb
van, mint a fölötte álló sor hasonló eleme. -/
def Lepcsos : Rendszer T n → Prop
  | [] => True
  | r :: L =>
      (∃ j : Fin (n + 1), Vezeto r j ∧ (∀ s ∈ L, s j = 0) ∧
        ∀ s ∈ L, ∀ js : Fin (n + 1), Vezeto s js → j < js ∧ r js = 0) ∧ Lepcsos L

theorem lepcsos_nil : Lepcsos ([] : Rendszer T n) := trivial

theorem lepcsos_cons_iff {r : Sor T n} {L : Rendszer T n} :
    Lepcsos (r :: L) ↔
      (∃ j : Fin (n + 1), Vezeto r j ∧ (∀ s ∈ L, s j = 0) ∧
        ∀ s ∈ L, ∀ js : Fin (n + 1), Vezeto s js → j < js ∧ r js = 0) ∧ Lepcsos L :=
  Iff.rfl

/-- Lépcsős rendszer minden sorának van vezető eleme. -/
theorem Lepcsos.exists_vezeto : ∀ {L : Rendszer T n}, Lepcsos L → ∀ r ∈ L, ∃ j, Vezeto r j := by
  intro L
  induction L with
  | nil => intro _ r hr; exact absurd hr (by simp)
  | cons a L ih =>
      rintro hL r hr
      rcases hL with ⟨⟨j, hj, -, -⟩, hLtail⟩
      rcases List.mem_cons.1 hr with h | h
      · exact ⟨j, h ▸ hj⟩
      · exact ih hLtail r h

/-- Lépcsős rendszerben egy sor a *többi* sor vezető 1-esének oszlopában nulla. -/
theorem Lepcsos.clean : ∀ {L : Rendszer T n}, Lepcsos L →
    ∀ s ∈ L, ∀ t ∈ L, s ≠ t → ∀ jt, Vezeto t jt → s jt = 0 := by
  intro L
  induction L with
  | nil => intro _; simp
  | cons r M ih =>
      intro hL
      obtain ⟨⟨j, hj, hz, hlt⟩, hM⟩ := hL
      intro s hs0 t ht0 hst jt hjt
      rcases List.mem_cons.1 hs0 with hs1 | hs1
      · rcases List.mem_cons.1 ht0 with ht1 | ht1
        · exact absurd (hs1.trans ht1.symm) hst
        · rw [hs1]
          exact (hlt t ht1 jt hjt).2
      · rcases List.mem_cons.1 ht0 with ht1 | ht1
        · have hje : jt = j := (ht1 ▸ hjt : Vezeto r jt).unique hj
          rw [hje]
          exact hz s hs1
        · exact ih hM s hs1 t ht1 hst jt hjt

/-! ## 5.4. Tétel: lépcsős alakra hozás -/

/-- Ha az `a` sor vezető eleme `q`, a `t` sor vezető eleme `jt`, és `a jt = 0`, akkor a
`t` sorból az `a` sor `t q`-szorosát levonva a vezető elem `jt` marad. -/
theorem vezeto_tisztitas {a t : Sor T n} {q jt : Fin (n + 1)} (hq : Vezeto a q)
    (ht : Vezeto t jt) (h : a jt = 0) : Vezeto (t + (-(t q)) • a) jt := by
  have hne : jt ≠ q := by
    intro h'
    rw [h'] at h
    rw [hq.1] at h
    exact one_ne_zero h
  constructor
  · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, ht.1, h]
    ring
  · intro c hc
    have h1 : t c = 0 := ht.2 c hc
    have h2 : (-(t q)) * a c = 0 := by
      rcases lt_or_gt_of_ne hne with hlt | hgt
      · rw [hq.2 c (hc.trans hlt)]; ring
      · rw [ht.2 q hgt]; ring
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, h1, h2]
    ring

/-- A megtisztított sor a `q` oszlopban nulla lesz. -/
theorem tisztitas_q {a t : Sor T n} {q : Fin (n + 1)} (hq : Vezeto a q) :
    (t + (-(t q)) • a) q = 0 := by
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hq.1]
  ring

/-- Ha az `a` sor vezető eleme `q`, és `a` a lépcsős `E` rendszer minden sorának vezető
oszlopában nulla, akkor `E` sorait `a` megfelelő többszöröseivel megtisztítva ismét
lépcsős rendszert kapunk. -/
theorem lepcsos_map_tisztitas {a : Sor T n} {q : Fin (n + 1)} (hq : Vezeto a q) :
    ∀ (E : Rendszer T n), Lepcsos E → (∀ s ∈ E, ∀ js, Vezeto s js → a js = 0) →
      Lepcsos (E.map (fun t => t + (-(t q)) • a)) := by
  intro E
  induction E with
  | nil => intro _ _; exact lepcsos_nil
  | cons t E' ih =>
      intro hE hcond
      obtain ⟨⟨jt, hjt, hz, hlt⟩, hE'⟩ := hE
      have hajt : a jt = 0 := hcond t (by simp) jt hjt
      rw [List.map_cons, lepcsos_cons_iff]
      refine ⟨⟨jt, vezeto_tisztitas hq hjt hajt, ?_, ?_⟩,
        ih hE' (fun s hs => hcond s (List.mem_cons_of_mem _ hs))⟩
      · rintro s hs
        obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hs
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hz u hu, hajt]
        ring
      · rintro s hs js hjs
        obtain ⟨u, hu, rfl⟩ := List.mem_map.1 hs
        obtain ⟨ju, hju⟩ := hE'.exists_vezeto u hu
        have haju : a ju = 0 := hcond u (List.mem_cons_of_mem _ hu) ju hju
        have hveq : js = ju := hjs.unique (vezeto_tisztitas hq hju haju)
        subst hveq
        refine ⟨(hlt u hu js hju).1, ?_⟩
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, (hlt u hu js hju).2, haju]
        ring

/-- Az első sorból a lépcsős `E` rendszer sorainak alkalmas többszöröseit levonva elérhető,
hogy az első sor `E` minden sorának vezető oszlopában nulla legyen. -/
theorem letezik_fejtisztitas {E : Rendszer T n} (hE : Lepcsos E) :
    ∀ (R : Rendszer T n), (∀ s ∈ R, s ∈ E) → ∀ a : Sor T n, ∃ a' : Sor T n,
      ElemiAtalakitasok (a :: E) (a' :: E) ∧ ∀ s ∈ R, ∀ js, Vezeto s js → a' js = 0 := by
  intro R
  induction R with
  | nil => intro _ a; exact ⟨a, Relation.ReflTransGen.refl, by simp⟩
  | cons s R ih =>
      intro hR a
      obtain ⟨a₁, h₁, h₂⟩ := ih (fun u hu => hR u (List.mem_cons_of_mem _ hu)) a
      have hsE : s ∈ E := hR s (by simp)
      obtain ⟨js, hjs⟩ := hE.exists_vezeto s hsE
      refine ⟨a₁ + (-(a₁ js)) • s,
        h₁.tail (ElemiLepes.head_add hsE (-(a₁ js))), ?_⟩
      have key : ∀ u, (u = s ∨ u ∈ R) → ∀ ju, Vezeto u ju →
          a₁ ju + (-(a₁ js)) * s ju = 0 := by
        rintro u (rfl | hu) ju hju
        · have h3 : ju = js := hju.unique hjs
          subst h3
          rw [hjs.1]; ring
        · by_cases hus : u = s
          · subst hus
            have h3 : ju = js := hju.unique hjs
            subst h3
            rw [hjs.1]; ring
          · rw [h₂ u hu ju hju,
              hE.clean s hsE u (hR u (List.mem_cons_of_mem _ hu)) (fun h => hus h.symm) ju hju]
            ring
      intro u hu ju hju
      simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] using
        key u (List.mem_cons.1 hu) ju hju

/-- A lépcsős rendszerbe egy alkalmas sort a helyére lehet vinni sorcserékkel. -/
theorem letezik_beszuras {a : Sor T n} {q : Fin (n + 1)} (hq : Vezeto a q) :
    ∀ (F : Rendszer T n), Lepcsos F →
      (∀ t ∈ F, ∀ jt : Fin (n + 1), Vezeto t jt → a jt = 0 ∧ t q = 0) →
      ∃ G : Rendszer T n, ElemiAtalakitasok (a :: F) G ∧ Lepcsos G ∧ G.Perm (a :: F) := by
  intro F
  induction F with
  | nil =>
      intro _ _
      exact ⟨[a], Relation.ReflTransGen.refl, ⟨⟨q, hq, by simp, by simp⟩, trivial⟩,
        List.Perm.refl _⟩
  | cons t F' ih =>
      intro hF hcond
      obtain ⟨⟨jt, hjt, hz, hlt⟩, hF'⟩ := hF
      obtain ⟨hajt, htq⟩ := hcond t (by simp) jt hjt
      have hne : q ≠ jt := by
        intro h
        rw [← h] at hajt
        rw [hq.1] at hajt
        exact one_ne_zero hajt
      rcases lt_or_gt_of_ne hne with hqlt | hqgt
      · -- q < jt : az `a` sor az élre kerül
        refine ⟨a :: t :: F', Relation.ReflTransGen.refl, ?_, List.Perm.refl _⟩
        refine ⟨⟨q, hq, ?_, ?_⟩, ⟨⟨jt, hjt, hz, hlt⟩, hF'⟩⟩
        · intro u hu
          rcases List.mem_cons.1 hu with rfl | hu
          · exact htq
          · exact (hcond u (List.mem_cons_of_mem _ hu)
              (Classical.choose (hF'.exists_vezeto u hu))
              (Classical.choose_spec (hF'.exists_vezeto u hu))).2
        · intro u hu ju hju
          rcases List.mem_cons.1 hu with rfl | hu
          · have : ju = jt := hju.unique hjt
            subst this
            exact ⟨hqlt, hajt⟩
          · refine ⟨hqlt.trans (hlt u hu ju hju).1,
              (hcond u (List.mem_cons_of_mem _ hu) ju hju).1⟩
      · -- jt < q : `a`-t egy sorcserével lejjebb visszük
        obtain ⟨G', hG'step, hG'lep, hG'perm⟩ :=
          ih hF' (fun u hu => hcond u (List.mem_cons_of_mem _ hu))
        have hswap : ElemiLepes (a :: t :: F') (t :: a :: F') :=
          ElemiLepes.csere [] [] F' a t
        refine ⟨t :: G', (Relation.ReflTransGen.single hswap).trans
          (ElemiAtalakitasok.cons t hG'step), ?_, ?_⟩
        · refine ⟨⟨jt, hjt, ?_, ?_⟩, hG'lep⟩
          · intro u hu
            rcases List.mem_cons.1 (hG'perm.mem_iff.1 hu) with rfl | hu'
            · exact hajt
            · exact hz u hu'
          · intro u hu ju hju
            rcases List.mem_cons.1 (hG'perm.mem_iff.1 hu) with rfl | hu'
            · have : ju = q := hju.unique hq
              subst this
              exact ⟨hqgt, htq⟩
            · exact hlt u hu' ju hju
        · exact (hG'perm.cons t).trans (List.Perm.swap a t F')

/-- **5.4. Tétel.** Minden egyenletrendszer elemi átalakításokkal lépcsős alakra
hozható.

*Bizonyítás.* Az egyenletek száma szerinti teljes indukció. Az üres rendszer lépcsős
alakú. Ha `m > 0` egyenletünk van, akkor az indukciós feltevés szerint az első egyenlet
elhagyásával kapott rendszer lépcsős alakra hozható; az első sorból a lépcsős rendszer
sorainak alkalmas többszöröseit levonva elérjük, hogy az első sor a vezető 1-esek
oszlopaiban nulla legyen. Ha így csupa nulla sort kapunk, elhagyjuk; egyébként az első
nem nulla elem reciprokával szorozva vezető 1-est készítünk, ennek oszlopát a többi
sorból kiküszöböljük, végül a sort sorcserékkel a helyére visszük. -/
theorem letezik_lepcsos (L : Rendszer T n) :
    ∃ E : Rendszer T n, ElemiAtalakitasok L E ∧ Lepcsos E := by
  classical
  induction L with
  | nil => exact ⟨[], Relation.ReflTransGen.refl, lepcsos_nil⟩
  | cons a L ih =>
      obtain ⟨E, hLE, hE⟩ := ih
      have h1 : ElemiAtalakitasok (a :: L) (a :: E) := ElemiAtalakitasok.cons a hLE
      obtain ⟨a', ha'step, ha'zero⟩ := letezik_fejtisztitas hE E (fun s hs => hs) a
      have h2 : ElemiAtalakitasok (a :: L) (a' :: E) := h1.trans ha'step
      by_cases hazero : a' = 0
      · refine ⟨E, h2.tail ?_, hE⟩
        subst hazero
        exact ElemiLepes.nulla_sor [] E
      · obtain ⟨q, hq0, hqmin⟩ : ∃ q : Fin (n + 1), a' q ≠ 0 ∧ ∀ c, c < q → a' c = 0 := by
          have hne : ∃ j : Fin (n + 1), a' j ≠ 0 := by
            by_contra hcon
            push_neg at hcon
            exact hazero (funext hcon)
          obtain ⟨j0, hj0⟩ := hne
          have hS : (Finset.univ.filter (fun j : Fin (n + 1) => a' j ≠ 0)).Nonempty :=
            ⟨j0, by simp [hj0]⟩
          refine ⟨(Finset.univ.filter (fun j : Fin (n + 1) => a' j ≠ 0)).min' hS, ?_, ?_⟩
          · have := Finset.min'_mem _ hS
            simpa using this
          · intro c hc
            by_contra hcc
            exact absurd (Finset.min'_le _ c (by simp [hcc])) (not_le.2 hc)
        have hstep2 : ElemiLepes (a' :: E) (((a' q)⁻¹ • a') :: E) :=
          ElemiLepes.szoroz [] E a' (inv_ne_zero hq0)
        set a'' : Sor T n := (a' q)⁻¹ • a' with ha''def
        have hVez : Vezeto a'' q := by
          constructor
          · simp only [ha''def, Pi.smul_apply, smul_eq_mul, inv_mul_cancel₀ hq0]
          · intro c hc
            simp only [ha''def, Pi.smul_apply, smul_eq_mul, hqmin c hc, mul_zero]
        have hzero2 : ∀ s ∈ E, ∀ js, Vezeto s js → a'' js = 0 := by
          intro s hs js hjs
          simp only [ha''def, Pi.smul_apply, smul_eq_mul, ha'zero s hs js hjs, mul_zero]
        have hstep3 : ElemiAtalakitasok (a'' :: E)
            (a'' :: E.map (fun t => t + (-(t q)) • a'')) := by
          have := letezik_oszlop_tisztitas a'' (fun t => -(t q)) E []
          simpa using this
        have hFlep : Lepcsos (E.map (fun t => t + (-(t q)) • a'')) :=
          lepcsos_map_tisztitas hVez E hE hzero2
        have hFcond : ∀ u ∈ E.map (fun t => t + (-(t q)) • a''), ∀ ju : Fin (n + 1),
            Vezeto u ju → a'' ju = 0 ∧ u q = 0 := by
          rintro u hu ju hju
          obtain ⟨v, hv, rfl⟩ := List.mem_map.1 hu
          obtain ⟨jv, hjv⟩ := hE.exists_vezeto v hv
          have hveq : ju = jv := hju.unique (vezeto_tisztitas hVez hjv (hzero2 v hv jv hjv))
          subst hveq
          exact ⟨hzero2 v hv ju hjv, tisztitas_q hVez⟩
        obtain ⟨G, hGstep, hGlep, -⟩ :=
          letezik_beszuras hVez (E.map (fun t => t + (-(t q)) • a'')) hFlep hFcond
        exact ⟨G, ((h2.tail hstep2).trans hstep3).trans hGstep, hGlep⟩

/-- **5.5. Gauss-elimináció.** Minden egyenletrendszerhez van vele ekvivalens lépcsős
alakú egyenletrendszer. -/
theorem gauss_elimination (L : Rendszer T n) :
    ∃ E : Rendszer T n, Lepcsos E ∧
      ∀ c : Fin n → T, RendszerMegoldasa L c ↔ RendszerMegoldasa E c := by
  obtain ⟨E, hE, hlep⟩ := letezik_lepcsos L
  exact ⟨E, hlep, fun c => hE.megoldas_iff c⟩

end Ch05
end SzaboLinAlg
