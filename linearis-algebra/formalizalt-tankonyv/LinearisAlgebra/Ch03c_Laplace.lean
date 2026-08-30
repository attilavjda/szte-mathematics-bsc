import LinearisAlgebra.Ch03b_DualitasVandermonde

/-!
# Szabó László: Bevezetés a lineáris algebrába — 3.14. Laplace-tétel

A jegyzet 3. fejezetének utolsó, bizonyítás nélkül közölt tétele:

* **3.14. Laplace-tétel** — a determináns kifejtése `r` kijelölt sora szerint,
* **3.15. Tétel** — ennek duálisa: kifejtés `r` kijelölt oszlop szerint.

A jegyzet a tételt bizonyítás nélkül mondja ki, ezért itt egy teljes bizonyítást adunk.
A bizonyítás vázlata:

1. **Kiürítés.** Rögzített `I` sorhalmaz mellett minden `J` oszlophalmazhoz tekintjük azt
   az `A_J` mátrixot, amely `A`-ból úgy keletkezik, hogy az `I`-beli sorokban a `J`-n
   kívüli oszlopok elemeit nullára cseréljük. A Leibniz-formulában minden `π`
   permutációhoz pontosan egy olyan `J` van (nevezetesen `J = π(I)`), amelyre a
   hozzá tartozó tag `A_J`-ben nem tűnik el, ezért `|A| = ∑_J |A_J|`.
2. **Blokkháromszög-alak.** Az `A_J` mátrix sorait az `I`, `Iᶜ`, oszlopait a `J`, `Jᶜ`
   sorrendbe rendezve blokk-háromszög mátrixot kapunk, melynek determinánsa a két
   átlós blokk determinánsának szorzata, azaz `M · D`.
3. **Előjel.** A rendező permutációk előjele `(-1)^(i₁+⋯+i_r)`, illetve
   `(-1)^(j₁+⋯+j_r)` (egy közös, a végén kiejtő konstans erejéig), így adódik a
   `(-1)^(i₁+⋯+i_r+j₁+⋯+j_r)` szorzótényező.

(A jegyzet 1-től indexel, a Lean-beli `Fin n` 0-tól; a két konvenció között az
előjelkitevő `2r`-rel tér el, ami páros, tehát az előjel ugyanaz.)
-/

namespace SzaboLinAlg
namespace Ch03

open scoped BigOperators
open Matrix Equiv Equiv.Perm Finset

variable {T : Type*} [CommRing T] {n r s : ℕ}

/-! ### Segédeszközök: a kijelölt sorokat előre rendező bijekció -/

/-- Ha `|I| = r` és `r + s = n`, akkor `|Iᶜ| = s`. -/
theorem compl_card_eq (h : r + s = n) {I : Finset (Fin n)} (hI : I.card = r) : Iᶜ.card = s := by
  rw [Finset.card_compl, hI, Fintype.card_fin]; omega

/-- A `Fin r ⊕ Fin s ≃ Fin n` bijekció, amely az első `r` indexet az `I` halmaz elemeire
(növekvő sorrendben), a maradék `s` indexet pedig `Iᶜ` elemeire (szintén növekvő
sorrendben) képezi. -/
noncomputable def rendezoEquiv (h : r + s = n) (I : Finset (Fin n)) (hI : I.card = r) :
    Fin r ⊕ Fin s ≃ Fin n :=
  Equiv.ofBijective (Sum.elim (I.orderEmbOfFin hI) (Iᶜ.orderEmbOfFin (compl_card_eq h hI))) (by
    rw [Fintype.bijective_iff_injective_and_card]
    refine ⟨?_, by simp [h]⟩
    rintro (k | k) (l | l) hkl <;> simp only [Sum.elim_inl, Sum.elim_inr] at hkl
    · simp [(I.orderEmbOfFin hI).injective hkl]
    · exact absurd (hkl ▸ Finset.orderEmbOfFin_mem Iᶜ _ l)
        (by simp [Finset.orderEmbOfFin_mem I hI k])
    · exact absurd (hkl ▸ Finset.orderEmbOfFin_mem I hI l)
        (by simpa using Finset.orderEmbOfFin_mem Iᶜ _ k)
    · simpa using (Iᶜ.orderEmbOfFin (compl_card_eq h hI)).injective hkl)

@[simp] theorem rendezoEquiv_inl (h : r + s = n) (I : Finset (Fin n)) (hI : I.card = r)
    (k : Fin r) : rendezoEquiv h I hI (Sum.inl k) = I.orderEmbOfFin hI k := rfl

@[simp] theorem rendezoEquiv_inr (h : r + s = n) (I : Finset (Fin n)) (hI : I.card = r)
    (k : Fin s) :
    rendezoEquiv h I hI (Sum.inr k) = Iᶜ.orderEmbOfFin (compl_card_eq h hI) k := rfl

/-- A referencia-bijekció: az `I = {0,1,…,r-1}` kezdőszelethez tartozó rendezés. -/
def refEquiv (h : r + s = n) : Fin r ⊕ Fin s ≃ Fin n := finSumFinEquiv.trans (finCongr h)

/-- A *rendező permutáció*: az a `Fin n → Fin n` permutáció, amely a `0,1,…,r-1`
pozíciókat az `I` halmaz elemeire, a többit `Iᶜ` elemeire képezi (mindkettőt növekvő
sorrendben). -/
noncomputable def rendezoPerm (h : r + s = n) (I : Finset (Fin n)) (hI : I.card = r) :
    Equiv.Perm (Fin n) := (refEquiv h).symm.trans (rendezoEquiv h I hI)

/-! ### A rendező permutáció előjele -/

/-- Szomszédos `a`, `b = a+1` elemek cseréje a halmazon: ha `S`-nek pontosan az egyike
eleme, akkor `S` növekvő felsorolása a `swap a b` képének felsorolásából a csere
alkalmazásával áll elő. -/
theorem orderEmbOfFin_swap_image {k : ℕ} {a b : Fin n} (hab : (a : ℕ) + 1 = (b : ℕ))
    (S : Finset (Fin n)) (hS : S.card = k)
    (hS' : (S.image (Equiv.swap a b)).card = k) (hex : a ∈ S ↔ b ∉ S) (t : Fin k) :
    S.orderEmbOfFin hS t = Equiv.swap a b ((S.image (Equiv.swap a b)).orderEmbOfFin hS' t) := by
  set Timg := S.image (Equiv.swap a b) with hT
  set v := fun t => Timg.orderEmbOfFin hS' t with hv
  have hmemT : ∀ x : Fin n, x ∈ Timg ↔ Equiv.swap a b x ∈ S := by
    intro x
    constructor
    · intro hx
      obtain ⟨y, hy, hyx⟩ := Finset.mem_image.1 hx
      rw [← hyx, Equiv.swap_apply_self]; exact hy
    · intro hx
      exact Finset.mem_image.2 ⟨Equiv.swap a b x, hx, Equiv.swap_apply_self _ _ _⟩
  have haT : a ∈ Timg ↔ b ∈ S := by rw [hmemT, Equiv.swap_apply_left]
  have hbT : b ∈ Timg ↔ a ∈ S := by rw [hmemT, Equiv.swap_apply_right]
  have hexT : a ∈ Timg ↔ b ∉ Timg := by
    rw [haT, hbT]
    exact ⟨fun h1 h2 => (hex.1 h2) h1, fun h1 => by by_contra h2; exact h1 (hex.2 h2)⟩
  have hvmem : ∀ t, v t ∈ Timg := fun t => Finset.orderEmbOfFin_mem _ _ _
  have hlt : ∀ t₁ t₂ : Fin k, t₁ < t₂ → v t₁ < v t₂ := fun t₁ t₂ h =>
    (Timg.orderEmbOfFin hS').strictMono h
  have key : (fun t => Equiv.swap a b (v t)) = ⇑(S.orderEmbOfFin hS) := by
    refine Finset.orderEmbOfFin_unique hS (fun t => (hmemT (v t)).1 (hvmem t)) ?_
    intro t₁ t₂ ht
    show Equiv.swap a b (v t₁) < Equiv.swap a b (v t₂)
    have h12 := hlt t₁ t₂ ht
    have hab' : (a : ℕ) < (b : ℕ) := by omega
    by_cases h1a : v t₁ = a
    · have hbnot : b ∉ Timg := hexT.1 (h1a ▸ hvmem t₁)
      have h2b : v t₂ ≠ b := fun hc => hbnot (hc ▸ hvmem t₂)
      have h2a : v t₂ ≠ a := fun hc => absurd (hc ▸ h12) (by simp [h1a])
      rw [h1a, Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne h2a h2b, Fin.lt_def]
      have h3 : (a : ℕ) < (v t₂ : ℕ) := by rw [← h1a]; exact h12
      have h4 : (v t₂ : ℕ) ≠ (b : ℕ) := fun hc => h2b (Fin.ext hc)
      omega
    · by_cases h1b : v t₁ = b
      · have hanot : a ∉ Timg := fun hc => (hexT.1 hc) (h1b ▸ hvmem t₁)
        have h2a : v t₂ ≠ a := fun hc => hanot (hc ▸ hvmem t₂)
        have h2b : v t₂ ≠ b := fun hc => absurd (hc ▸ h12) (by simp [h1b])
        rw [h1b, Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne h2a h2b, Fin.lt_def]
        have h3 : (b : ℕ) < (v t₂ : ℕ) := by rw [← h1b]; exact h12
        omega
      · rw [Equiv.swap_apply_of_ne_of_ne h1a h1b]
        by_cases h2a : v t₂ = a
        · rw [h2a, Equiv.swap_apply_left, Fin.lt_def]
          have h3 : (v t₁ : ℕ) < (a : ℕ) := by rw [← h2a]; exact h12
          omega
        · by_cases h2b : v t₂ = b
          · have hanot : a ∉ Timg := fun hc => (hexT.1 hc) (h2b ▸ hvmem t₂)
            have h1a' : v t₁ ≠ a := fun hc => hanot (hc ▸ hvmem t₁)
            rw [h2b, Equiv.swap_apply_right, Fin.lt_def]
            have h1 : (v t₁ : ℕ) < (b : ℕ) := by rw [← h2b]; exact h12
            have h2 : (v t₁ : ℕ) ≠ (a : ℕ) := fun hc => h1a' (Fin.ext hc)
            omega
          · rw [Equiv.swap_apply_of_ne_of_ne h2a h2b]; exact h12
  exact (congrFun key t).symm

/-- Az előző lemma alakja, amelyben a cserélt halmazt külön névvel adjuk meg. -/
theorem orderEmbOfFin_swap {k : ℕ} {a b : Fin n} (hab : (a : ℕ) + 1 = (b : ℕ))
    (S T : Finset (Fin n)) (hST : T = S.image (Equiv.swap a b))
    (hS : S.card = k) (hT : T.card = k) (hex : a ∈ S ↔ b ∉ S) (t : Fin k) :
    S.orderEmbOfFin hS t = Equiv.swap a b (T.orderEmbOfFin hT t) := by
  subst hST
  exact orderEmbOfFin_swap_image hab S hS hT hex t

theorem mem_image_swap {a b x : Fin n} {S : Finset (Fin n)} :
    x ∈ S.image (Equiv.swap a b) ↔ Equiv.swap a b x ∈ S := by
  constructor
  · intro hx
    obtain ⟨y, hy, hyx⟩ := Finset.mem_image.1 hx
    rw [← hyx, Equiv.swap_apply_self]; exact hy
  · intro hx
    exact Finset.mem_image.2 ⟨Equiv.swap a b x, hx, Equiv.swap_apply_self _ _ _⟩

@[simp] theorem refEquiv_inl_val (h : r + s = n) (k : Fin r) :
    ((refEquiv h (Sum.inl k) : Fin n) : ℕ) = (k : ℕ) := by simp [refEquiv]

@[simp] theorem refEquiv_inr_val (h : r + s = n) (l : Fin s) :
    ((refEquiv h (Sum.inr l) : Fin n) : ℕ) = r + (l : ℕ) := by simp [refEquiv]

/-- Ha `I` éppen a `{0,1,…,r-1}` kezdőszelet, akkor a rendező bijekció a referencia-
bijekció. -/
theorem rendezoEquiv_kezdoszelet (h : r + s = n) (I : Finset (Fin n)) (hI : I.card = r)
    (hmem : ∀ i : Fin n, i ∈ I ↔ (i : ℕ) < r) : rendezoEquiv h I hI = refEquiv h := by
  have h1 : (fun k : Fin r => (refEquiv h (Sum.inl k) : Fin n)) = ⇑(I.orderEmbOfFin hI) := by
    refine Finset.orderEmbOfFin_unique hI (fun k => (hmem _).2 (by simp)) ?_
    intro x y hxy
    rw [Fin.lt_def, refEquiv_inl_val, refEquiv_inl_val]
    exact hxy
  have h2 : (fun l : Fin s => (refEquiv h (Sum.inr l) : Fin n)) =
      ⇑(Iᶜ.orderEmbOfFin (compl_card_eq h hI)) := by
    refine Finset.orderEmbOfFin_unique (compl_card_eq h hI)
      (fun l => Finset.mem_compl.2 (fun hc => by
        have := (hmem _).1 hc
        rw [refEquiv_inr_val] at this
        omega)) ?_
    intro x y hxy
    rw [Fin.lt_def, refEquiv_inr_val, refEquiv_inr_val]
    have : (x : ℕ) < (y : ℕ) := hxy
    omega
  refine Equiv.ext fun y => ?_
  rcases y with k | l
  · exact (congrFun h1 k).symm
  · exact (congrFun h2 l).symm

theorem rendezoPerm_kezdoszelet (h : r + s = n) (I : Finset (Fin n)) (hI : I.card = r)
    (hmem : ∀ i : Fin n, i ∈ I ↔ (i : ℕ) < r) : rendezoPerm h I hI = 1 := by
  rw [rendezoPerm, rendezoEquiv_kezdoszelet h I hI hmem]
  ext x
  simp

/-- **A rendező permutáció előjele.** Az `I = {i₁ < … < i_r}` sorhalmazhoz tartozó rendező
permutáció előjele `(-1)^(i₁+⋯+i_r+(0+1+⋯+(r-1)))`. (A második, `I`-től független tag a
Laplace-kifejtésben kiejti önmagát, hiszen kétszer lép fel.) -/
theorem sign_rendezoPerm_aux (h : r + s = n) : ∀ N : ℕ, ∀ I : Finset (Fin n), ∀ hI : I.card = r,
    (∑ i ∈ I, (i : ℕ)) = N →
      Equiv.Perm.sign (rendezoPerm h I hI) = (-1 : ℤˣ) ^ (N + ∑ k ∈ Finset.range r, k) := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro I hI hsum
    by_cases hpair : ∃ a b : Fin n, (a : ℕ) + 1 = (b : ℕ) ∧ b ∈ I ∧ a ∉ I
    · obtain ⟨a, b, hab, hbI, haI⟩ := hpair
      have hne : a ≠ b := fun hc => by rw [hc] at hab; omega
      set I' := I.image (Equiv.swap a b) with hI'def
      have hI' : I'.card = r := by
        rw [hI'def, Finset.card_image_of_injective _ (Equiv.injective _), hI]
      have hswap_sum : ∑ i ∈ I', (i : ℕ) = ∑ i ∈ I, ((Equiv.swap a b i : Fin n) : ℕ) := by
        rw [hI'def, Finset.sum_image (fun x _ y _ hxy => Equiv.injective _ hxy)]
      have hsplit : ∑ i ∈ I, ((Equiv.swap a b i : Fin n) : ℕ) =
          (a : ℕ) + ∑ i ∈ I.erase b, (i : ℕ) := by
        rw [← Finset.add_sum_erase _ _ hbI, Equiv.swap_apply_right]
        congr 1
        refine Finset.sum_congr rfl fun x hx => ?_
        have hxb : x ≠ b := (Finset.mem_erase.1 hx).1
        have hxa : x ≠ a := fun hc => haI (hc ▸ (Finset.mem_erase.1 hx).2)
        rw [Equiv.swap_apply_of_ne_of_ne hxa hxb]
      have hsplitI : ∑ i ∈ I, (i : ℕ) = (b : ℕ) + ∑ i ∈ I.erase b, (i : ℕ) :=
        (Finset.add_sum_erase _ _ hbI).symm
      have hsum' : (∑ i ∈ I', (i : ℕ)) + 1 = ∑ i ∈ I, (i : ℕ) := by
        rw [hswap_sum, hsplit, hsplitI]; omega
      have hcompl : I'ᶜ = Iᶜ.image (Equiv.swap a b) := by
        ext x
        simp only [Finset.mem_compl, hI'def, mem_image_swap]
      have hexI : a ∈ I ↔ b ∉ I := ⟨fun hc => absurd hc haI, fun hc => absurd hbI hc⟩
      have hexIc : a ∈ Iᶜ ↔ b ∉ Iᶜ :=
        ⟨fun _ => by simpa using hbI, fun _ => Finset.mem_compl.2 haI⟩
      have hperm : rendezoPerm h I hI = (Equiv.swap a b) * rendezoPerm h I' hI' := by
        refine Equiv.ext fun x => ?_
        rw [Equiv.Perm.mul_apply]
        simp only [rendezoPerm, Equiv.trans_apply]
        generalize (refEquiv h).symm x = y
        rcases y with k | l
        · simp only [rendezoEquiv_inl]
          exact orderEmbOfFin_swap hab I I' hI'def hI hI' hexI k
        · simp only [rendezoEquiv_inr]
          exact orderEmbOfFin_swap hab Iᶜ I'ᶜ hcompl (compl_card_eq h hI)
            (compl_card_eq h hI') hexIc l
      rw [hperm, map_mul, Equiv.Perm.sign_swap hne,
        ih (∑ i ∈ I', (i : ℕ)) (by omega) I' hI' rfl]
      have hNeq : N + ∑ k ∈ Finset.range r, k = ((∑ i ∈ I', (i : ℕ)) + ∑ k ∈ Finset.range r, k) + 1 := by
        omega
      rw [hNeq, pow_succ]
      exact mul_comm _ _
    · push_neg at hpair
      have hrn : r ≤ n := by omega
      have dc : ∀ m : ℕ, ∀ b ∈ I, (b : ℕ) = m → ∀ j : Fin n, j ≤ b → j ∈ I := by
        intro m
        induction m using Nat.strong_induction_on with
        | _ m ihm =>
          intro b hbI hbm j hjb
          rcases eq_or_lt_of_le hjb with rfl | hlt
          · exact hbI
          · have hlt' : (j : ℕ) < (b : ℕ) := hlt
            have hm1 : m - 1 < n := by omega
            have haI : (⟨m - 1, hm1⟩ : Fin n) ∈ I := hpair _ b (by simp; omega) hbI
            exact ihm (m - 1) (by omega) ⟨m - 1, hm1⟩ haI rfl j (by rw [Fin.le_def]; show (j : ℕ) ≤ m - 1; omega)
      set K := Finset.image (Fin.castLE hrn) (univ : Finset (Fin r)) with hKdef
      have hKcard : K.card = r := by
        rw [hKdef, Finset.card_image_of_injective _ (Fin.castLE_injective hrn)]; simp
      have hKmem : ∀ i : Fin n, i ∈ K ↔ (i : ℕ) < r := by
        intro i
        rw [hKdef]
        simp only [Finset.mem_image, Finset.mem_univ, true_and]
        constructor
        · rintro ⟨k, rfl⟩; simp [k.2]
        · intro hi; exact ⟨⟨i, hi⟩, by ext; simp⟩
      have hsubset : I ⊆ K := by
        intro i hi
        rw [hKmem]
        have hsub : Finset.Iic i ⊆ I := fun j hj => dc _ i hi rfl j (Finset.mem_Iic.1 hj)
        have hcard := Finset.card_le_card hsub
        rw [Fin.card_Iic, hI] at hcard
        omega
      have hIK : I = K := Finset.eq_of_subset_of_card_le hsubset (by rw [hKcard, hI])
      have hmem : ∀ i : Fin n, i ∈ I ↔ (i : ℕ) < r := by rw [hIK]; exact hKmem
      have hNsum : N = ∑ k ∈ Finset.range r, k := by
        rw [← hsum, hIK, hKdef,
          Finset.sum_image (fun x _ y _ hxy => Fin.castLE_injective hrn hxy)]
        simp [Fin.sum_univ_eq_sum_range (fun i => i) r]
      rw [rendezoPerm_kezdoszelet h I hI hmem, map_one, hNsum, ← two_mul, pow_mul]
      simp

theorem sign_rendezoPerm (h : r + s = n) (I : Finset (Fin n)) (hI : I.card = r) :
    Equiv.Perm.sign (rendezoPerm h I hI) =
      (-1 : ℤˣ) ^ ((∑ i ∈ I, (i : ℕ)) + ∑ k ∈ Finset.range r, k) :=
  sign_rendezoPerm_aux h _ I hI rfl

/-! ### 1. lépés: kiürítés -/

/-- Az `A` mátrixból az `I`-beli sorok `J`-n kívüli elemeinek nullázásával kapott mátrix. -/
def kiuritett (A : Matrix (Fin n) (Fin n) T) (I J : Finset (Fin n)) :
    Matrix (Fin n) (Fin n) T := fun i j => if i ∈ I ∧ j ∉ J then 0 else A i j

/-- A determináns Leibniz-formulája sorok szerinti indexeléssel. -/
theorem det_apply_sorok (M : Matrix (Fin n) (Fin n) T) :
    M.det = ∑ σ : Equiv.Perm (Fin n), ((Equiv.Perm.sign σ : ℤ) : T) * ∏ i, M i (σ i) := by
  rw [← Matrix.det_transpose, Matrix.det_apply']
  rfl

theorem prod_kiuritett (A : Matrix (Fin n) (Fin n) T) {I J : Finset (Fin n)}
    (hJ : J.card = I.card) (σ : Equiv.Perm (Fin n)) :
    (∏ i, kiuritett A I J i (σ i)) = if I.image σ = J then ∏ i, A i (σ i) else 0 := by
  by_cases hIJ : I.image σ = J
  · rw [if_pos hIJ]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [kiuritett, if_neg]
    rintro ⟨hiI, hσi⟩
    exact hσi (hIJ ▸ Finset.mem_image_of_mem _ hiI)
  · rw [if_neg hIJ]
    have hcard : (I.image σ).card = I.card :=
      Finset.card_image_of_injective _ (Equiv.injective _)
    have hsub : ¬ I.image σ ⊆ J := fun hs =>
      hIJ (Finset.eq_of_subset_of_card_le hs (by rw [hcard, hJ]))
    obtain ⟨j, hj, hjJ⟩ := Finset.not_subset.1 hsub
    obtain ⟨i, hiI, rfl⟩ := Finset.mem_image.1 hj
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    rw [kiuritett, if_pos ⟨hiI, hjJ⟩]

theorem det_eq_sum_kiuritett (A : Matrix (Fin n) (Fin n) T) (I : Finset (Fin n)) :
    A.det = ∑ J ∈ Finset.univ.powersetCard I.card, (kiuritett A I J).det := by
  simp only [det_apply_sorok]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have : ∀ J ∈ Finset.univ.powersetCard I.card,
      ((Equiv.Perm.sign σ : ℤ) : T) * ∏ i, kiuritett A I J i (σ i) =
        if I.image σ = J then ((Equiv.Perm.sign σ : ℤ) : T) * ∏ i, A i (σ i) else 0 := by
    intro J hJ
    rw [prod_kiuritett A (Finset.mem_powersetCard_univ.1 hJ) σ]
    split <;> simp
  rw [Finset.sum_congr rfl this, Finset.sum_ite_eq, if_pos]
  exact Finset.mem_powersetCard_univ.2 (Finset.card_image_of_injective _ (Equiv.injective _))

/-! ### 2. lépés: blokkháromszög-alak -/

/-- A két rendező bijekcióból képzett `Fin r ⊕ Fin s`-permutáció előjele a két rendező
permutáció előjelének szorzata. -/
theorem sign_rendezoEquiv_trans (h : r + s = n) {I J : Finset (Fin n)}
    (hI : I.card = r) (hJ : J.card = r) :
    Equiv.Perm.sign ((rendezoEquiv h J hJ).trans (rendezoEquiv h I hI).symm) =
      Equiv.Perm.sign (rendezoPerm h I hI) * Equiv.Perm.sign (rendezoPerm h J hJ) := by
  set c := refEquiv (r := r) (s := s) h with hc
  set pI := rendezoPerm h I hI with hpI
  set pJ := rendezoPerm h J hJ with hpJ
  have hg : ((c.symm.symm.trans (pI⁻¹ * pJ)).trans c.symm) =
      (rendezoEquiv h J hJ).trans (rendezoEquiv h I hI).symm := by
    ext x
    simp only [hc, hpI, hpJ, rendezoPerm, Equiv.Perm.mul_apply, Equiv.trans_apply,
      Equiv.symm_trans_apply, Equiv.symm_symm, Equiv.Perm.inv_def, Equiv.symm_apply_apply]
  have := Equiv.Perm.sign_symm_trans_trans (pI⁻¹ * pJ) c.symm
  rw [hg] at this
  rw [this, map_mul, Equiv.Perm.sign_inv]

theorem det_kiuritett (h : r + s = n) (A : Matrix (Fin n) (Fin n) T)
    {I J : Finset (Fin n)} (hI : I.card = r) (hJ : J.card = r) :
    (kiuritett A I J).det =
      ((Equiv.Perm.sign (rendezoPerm h I hI) * Equiv.Perm.sign (rendezoPerm h J hJ) : ℤˣ) : ℤ) *
        ((A.submatrix (I.orderEmbOfFin hI) (J.orderEmbOfFin hJ)).det *
          (A.submatrix (Iᶜ.orderEmbOfFin (compl_card_eq h hI))
            (Jᶜ.orderEmbOfFin (compl_card_eq h hJ))).det) := by
  set eI := rendezoEquiv h I hI with heI
  set eJ := rendezoEquiv h J hJ with heJ
  set B := kiuritett A I J with hB
  set sg := eJ.trans eI.symm with hsg
  have hblock : B.submatrix eI eJ =
      Matrix.fromBlocks (A.submatrix (I.orderEmbOfFin hI) (J.orderEmbOfFin hJ)) 0
        (A.submatrix (Iᶜ.orderEmbOfFin (compl_card_eq h hI)) (J.orderEmbOfFin hJ))
        (A.submatrix (Iᶜ.orderEmbOfFin (compl_card_eq h hI))
          (Jᶜ.orderEmbOfFin (compl_card_eq h hJ))) := by
    ext a b
    have hIm : ∀ k, I.orderEmbOfFin hI k ∈ I := fun k => Finset.orderEmbOfFin_mem _ _ _
    have hIcm : ∀ k, Iᶜ.orderEmbOfFin (compl_card_eq h hI) k ∉ I := fun k =>
      Finset.mem_compl.1 (Finset.orderEmbOfFin_mem Iᶜ (compl_card_eq h hI) k)
    have hJm : ∀ l, J.orderEmbOfFin hJ l ∈ J := fun l => Finset.orderEmbOfFin_mem _ _ _
    have hJcm : ∀ l, Jᶜ.orderEmbOfFin (compl_card_eq h hJ) l ∉ J := fun l =>
      Finset.mem_compl.1 (Finset.orderEmbOfFin_mem Jᶜ (compl_card_eq h hJ) l)
    rcases a with k | k <;> rcases b with l | l <;>
      simp [hB, kiuritett, heI, heJ, hIm, hIcm, hJm, hJcm]
  have hsub : B.submatrix eI eJ = (B.submatrix eI eI).submatrix id sg := by
    ext a b; simp [hsg]
  have hdet1 : (B.submatrix eI eJ).det = ((Equiv.Perm.sign sg : ℤ) : T) * B.det := by
    rw [hsub, Matrix.det_permute', Matrix.det_submatrix_equiv_self]
  have hsq : ((Equiv.Perm.sign sg : ℤ) : T) * ((Equiv.Perm.sign sg : ℤ) : T) = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign sg) with hu | hu <;> rw [hu] <;> norm_num
  have hBdet : B.det = ((Equiv.Perm.sign sg : ℤ) : T) * (B.submatrix eI eJ).det := by
    rw [hdet1, ← mul_assoc, hsq, one_mul]
  rw [hBdet, hblock, Matrix.det_fromBlocks_zero₁₂, hsg, sign_rendezoEquiv_trans]

/-! ### 3. lépés: a 3.14. Laplace-tétel -/

/-- Az `orderEmbOfFin` átindexelése egy `Fin`-kasztolással. -/
theorem orderEmbOfFin_comp_cast {k m : ℕ} (S : Finset (Fin n)) (hk : S.card = k) (hm : m = k)
    (hS : S.card = m) :
    (fun t : Fin m => S.orderEmbOfFin hk (Fin.cast hm t)) = ⇑(S.orderEmbOfFin hS) :=
  Finset.orderEmbOfFin_unique hS (fun _ => Finset.orderEmbOfFin_mem _ _ _)
    (fun x y hxy => (S.orderEmbOfFin hk).strictMono (show Fin.cast hm x < Fin.cast hm y from hxy))

/-- A 3.13. Definícióbeli aldetermináns részmátrix-alakja. -/
theorem kijeloltAldeterminans_eq (A : Matrix (Fin n) (Fin n) T) {I J : Finset (Fin n)}
    (h : I.card = J.card) :
    kijeloltAldeterminans A I J h =
      (A.submatrix (I.orderEmbOfFin rfl) (J.orderEmbOfFin h.symm)).det := by
  rw [kijeloltAldeterminans, det'_eq_det, orderEmbOfFin_comp_cast J rfl h h.symm]

/-- A 3.13. Definícióbeli komplementer aldetermináns részmátrix-alakja. -/
theorem komplementerKijeloltAldeterminans_eq (A : Matrix (Fin n) (Fin n) T)
    {I J : Finset (Fin n)} (h : I.card = J.card) (hc : Iᶜ.card = Jᶜ.card) :
    komplementerKijeloltAldeterminans A I J h =
      (A.submatrix (Iᶜ.orderEmbOfFin rfl) (Jᶜ.orderEmbOfFin hc.symm)).det := by
  rw [komplementerKijeloltAldeterminans, det'_eq_det, orderEmbOfFin_comp_cast Jᶜ rfl hc hc.symm]

/-- A részmátrix determinánsa nem függ attól, hogy a sorokat/oszlopokat melyik (egyenlő
számosságú) indexhalmazzal soroljuk fel. -/
theorem det_submatrix_orderEmb_cast (A : Matrix (Fin n) (Fin n) T) {k k' : ℕ}
    (S S' : Finset (Fin n)) (hS : S.card = k) (hS' : S'.card = k)
    (hT : S.card = k') (hT' : S'.card = k') :
    (A.submatrix (S.orderEmbOfFin hS) (S'.orderEmbOfFin hS')).det =
      (A.submatrix (S.orderEmbOfFin hT) (S'.orderEmbOfFin hT')).det := by
  have hkk : k' = k := by omega
  have hsub : (A.submatrix (S.orderEmbOfFin hS) (S'.orderEmbOfFin hS')).submatrix
      (finCongr hkk) (finCongr hkk) =
      A.submatrix (S.orderEmbOfFin hT) (S'.orderEmbOfFin hT') := by
    ext x y
    exact congr_arg₂ A (congrFun (orderEmbOfFin_comp_cast S hS hkk hT) x)
      (congrFun (orderEmbOfFin_comp_cast S' hS' hkk hT') y)
  rw [← Matrix.det_submatrix_equiv_self (finCongr hkk)
    (A.submatrix (S.orderEmbOfFin hS) (S'.orderEmbOfFin hS')), hsub]

theorem sign_pow_cast (x y c : ℕ) :
    ((((-1 : ℤˣ) ^ (x + c) * (-1 : ℤˣ) ^ (y + c) : ℤˣ) : ℤ) : T) = (-1 : T) ^ (x + y) := by
  rw [← pow_add]
  have h2 : x + c + (y + c) = x + y + 2 * c := by ring
  rw [h2, pow_add, pow_mul]
  push_cast
  simp

/-- **3.14. Laplace-tétel.** Legyen `T` számtest, `A` egy `T` feletti `n × n`-es mátrix és
`I = {i₁ < i₂ < … < i_r}` a kijelölt sorok halmaza. Ekkor

`|A| = ∑_{J = {j₁ < … < j_r}} M_{i₁,…,i_r}^{j₁,…,j_r} · D_{i₁,…,i_r}^{j₁,…,j_r} ·
        (-1)^(i₁+⋯+i_r+j₁+⋯+j_r)`,

ahol az összegzés az összes `r` elemű `J` oszlophalmazra megy. A fenti összeget a
determináns `i₁,…,i_r` sorai szerinti kifejtésének nevezzük.

*Bizonyítás.* A jegyzet a tételt bizonyítás nélkül közli. Az itteni bizonyítás három
lépésből áll: (1) a determináns felbomlik a „kiürített” mátrixok determinánsainak
összegére (`det_eq_sum_kiuritett`), (2) a kiürített mátrix a sorok és oszlopok
átrendezésével blokk-háromszög alakú, így determinánsa a két aldetermináns szorzata
(`det_kiuritett`), végül (3) az átrendező permutációk előjele `(-1)^(i₁+⋯+i_r)`, illetve
`(-1)^(j₁+⋯+j_r)` egy közös, kiejtő tényező erejéig (`sign_rendezoPerm`). -/
theorem laplace_kifejtes (A : Matrix (Fin n) (Fin n) T) (I : Finset (Fin n)) :
    det' A = ∑ J ∈ ((Finset.univ : Finset (Fin n)).powersetCard I.card).attach,
      (-1 : T) ^ ((∑ i ∈ I, (i : ℕ)) + ∑ j ∈ J.1, (j : ℕ)) *
        (kijeloltAldeterminans A I J.1 (Finset.mem_powersetCard_univ.1 J.2).symm *
          komplementerKijeloltAldeterminans A I J.1
            (Finset.mem_powersetCard_univ.1 J.2).symm) := by
  have hn : I.card + Iᶜ.card = n := by simp [Finset.card_add_card_compl I]
  rw [det'_eq_det, det_eq_sum_kiuritett A I,
    ← Finset.sum_attach (Finset.univ.powersetCard I.card) (fun J => (kiuritett A I J).det)]
  refine Finset.sum_congr rfl fun J _ => ?_
  obtain ⟨J, hJmem⟩ := J
  have hJ : J.card = I.card := Finset.mem_powersetCard_univ.1 hJmem
  have hJc : Jᶜ.card = Iᶜ.card := by
    rw [Finset.card_compl, Finset.card_compl, hJ]
  rw [det_kiuritett hn A (rfl : I.card = I.card) hJ, sign_rendezoPerm, sign_rendezoPerm,
    kijeloltAldeterminans_eq A hJ.symm, komplementerKijeloltAldeterminans_eq A hJ.symm hJc.symm,
    sign_pow_cast]

/-- **3.15. Tétel (a Laplace-tétel duálisa).** Legyen `T` számtest, `A` egy `T` feletti
`n × n`-es mátrix és `J = {j₁ < j₂ < … < j_r}` a kijelölt oszlopok halmaza. Ekkor

`|A| = ∑_{I = {i₁ < … < i_r}} M_{i₁,…,i_r}^{j₁,…,j_r} · D_{i₁,…,i_r}^{j₁,…,j_r} ·
        (-1)^(i₁+⋯+i_r+j₁+⋯+j_r)`,

ahol az összegzés az összes `r` elemű `I` sorhalmazra megy. A fenti összeget a determináns
`j₁,…,j_r` oszlopai szerinti kifejtésének nevezzük.

*Bizonyítás.* A 3.7. dualitási elv szerint elég a 3.14. Tételt az `Aᵀ` mátrixra
alkalmazni. -/
theorem laplace_kifejtes_oszlop (A : Matrix (Fin n) (Fin n) T) (J : Finset (Fin n)) :
    det' A = ∑ I ∈ ((Finset.univ : Finset (Fin n)).powersetCard J.card).attach,
      (-1 : T) ^ ((∑ i ∈ I.1, (i : ℕ)) + ∑ j ∈ J, (j : ℕ)) *
        (kijeloltAldeterminans A I.1 J (Finset.mem_powersetCard_univ.1 I.2) *
          komplementerKijeloltAldeterminans A I.1 J
            (Finset.mem_powersetCard_univ.1 I.2)) := by
  rw [← det_transzponalt A, laplace_kifejtes Aᵀ J]
  refine Finset.sum_congr rfl fun I _ => ?_
  obtain ⟨I, hImem⟩ := I
  have hI : I.card = J.card := Finset.mem_powersetCard_univ.1 hImem
  have hIc : Iᶜ.card = Jᶜ.card := by rw [Finset.card_compl, Finset.card_compl, hI]
  rw [kijeloltAldeterminans_eq, kijeloltAldeterminans_eq,
    komplementerKijeloltAldeterminans_eq _ _ hIc.symm,
    komplementerKijeloltAldeterminans_eq _ hI hIc,
    ← Matrix.det_transpose (Aᵀ.submatrix (J.orderEmbOfFin rfl) (I.orderEmbOfFin hI)),
    ← Matrix.det_transpose (Aᵀ.submatrix (Jᶜ.orderEmbOfFin rfl) (Iᶜ.orderEmbOfFin hIc))]
  rw [add_comm (∑ i ∈ I, (i : ℕ))]
  simp only [Matrix.transpose_submatrix, Matrix.transpose_transpose]
  rw [det_submatrix_orderEmb_cast A I J hI rfl rfl hI.symm,
    det_submatrix_orderEmb_cast A Iᶜ Jᶜ hIc rfl rfl hIc.symm]

end Ch03
end SzaboLinAlg
