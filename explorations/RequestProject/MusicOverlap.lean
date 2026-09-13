/-
# Where *The Topos of Music* meets Kalkulus I and Lineáris algebra I

Mazzola's *The Topos of Music* is built on one very simple starting point, which is
also a `Tárgytematika` element of both Szeged courses:

* **pitch classes are a cyclic group** `ZMod 12` (octave equivalence = a quotient
  homomorphism `ℤ → ℤ/12ℤ`), and
* the musical operations *transposition* and *inversion* are exactly the
  **affine maps** `x ↦ ±x + n` of that group — the same "elemi transzformációs
  lépések" `x ↦ a·x + b` that Kalkulus gyakorló 2.16 asks you to draw, and the
  same *inverse-with-respect-to-composition* of 2.3–2.9.

Everything Mazzola does with topoi sits on top of this; this file keeps only the
part that is elementary, and only the part that is genuinely shared with the two
syllabi. Each section names the syllabus item and the musical fact, and every
claim is proved.

The companion write-up `music/MusicOverlap.tex` explains how to *play* these
patterns at the piano or on a drum kit.
-/
import Mathlib

namespace MusicOverlap

open Finset

/-! ## 1. Pitch = logarithm of frequency

Kalkulus I: *"exponenciális függvények és inverzeik"*, `lg`, the functional
equation `log (xy) = log x + log y` (gyakorló 2.1 e, 2.13 c).

Music: the ear hears frequency *ratios*, the keyboard is spaced *additively*.
The logarithm is precisely the translation between the two, and equal
temperament is the statement that the semitone is the twelfth root of two. -/

/-- MIDI pitch of a frequency (A4 = 440 Hz is note 69). -/
noncomputable def pitch (f : ℝ) : ℝ := 69 + 12 * Real.logb 2 (f / 440)

/-- **Octave = +12.** Doubling the frequency adds twelve semitones: the
multiplicative group of frequencies is carried by `log` onto the additive group
of pitches. -/
theorem pitch_octave {f : ℝ} (hf : 0 < f) : pitch (2 * f) = pitch f + 12 := by
  unfold pitch
  have h : (2 * f) / 440 = 2 * (f / 440) := by ring
  rw [h, Real.logb_mul (by norm_num) (by positivity), Real.logb_self_eq_one (by norm_num)]
  ring

/-- A pitch *difference* only depends on the frequency *ratio* — the reason a
melody keeps its shape when it is transposed. -/
theorem pitch_sub {f g : ℝ} (hf : 0 < f) (hg : 0 < g) :
    pitch f - pitch g = 12 * Real.logb 2 (f / g) := by
  unfold pitch
  have h : f / 440 = (f / g) * (g / 440) := by field_simp
  rw [h, Real.logb_mul (by positivity) (by positivity)]
  ring

/-- **Equal temperament.** Twelve equal semitones make an octave. -/
theorem semitone_pow_twelve : ((2 : ℝ) ^ ((1 : ℝ) / 12)) ^ (12 : ℕ) = 2 := by
  rw [← Real.rpow_natCast ((2 : ℝ) ^ ((1 : ℝ) / 12)) 12, ← Real.rpow_mul (by norm_num)]
  norm_num

/-- One semitone up = multiply the frequency by `2^(1/12)`. -/
theorem pitch_semitone {f : ℝ} (hf : 0 < f) :
    pitch ((2 : ℝ) ^ ((1 : ℝ) / 12) * f) = pitch f + 1 := by
  unfold pitch
  have h : ((2 : ℝ) ^ ((1 : ℝ) / 12) * f) / 440 = (2 : ℝ) ^ ((1 : ℝ) / 12) * (f / 440) := by
    ring
  rw [h, Real.logb_mul (by positivity) (by positivity), Real.logb_rpow (by norm_num) (by norm_num)]
  ring

/-! ## 2. Octave equivalence = the quotient homomorphism `ℤ → ZMod 12`

Lineáris algebra I: homomorphisms and quotients; Kalkulus I: periodic functions
(`sin`, `cos`, gyakorló 2.16 g). "C is C, in whatever octave" is the single
sentence `(n + 12 : ℤ) ≡ n`. -/

/-- Pitch classes: the twelve notes of the keyboard, `0 = C`, `1 = C♯`, … -/
abbrev PC := ZMod 12

/-- Naming the white keys, so the statements below can be read as music. -/
def C : PC := 0
def D : PC := 2
def E : PC := 4
def F : PC := 5
def G : PC := 7
def A : PC := 9
def B : PC := 11

/-- **Octave equivalence.** Adding twelve semitones does not change the note. -/
theorem pc_octave (n : ℤ) : ((n + 12 : ℤ) : PC) = (n : PC) := by
  push_cast
  simp [show (12 : PC) = 0 by decide]

/-- The quotient map is additive: intervals in `ℤ` become intervals mod 12. -/
theorem pc_add (m n : ℤ) : ((m + n : ℤ) : PC) = (m : PC) + (n : PC) := by push_cast; ring

/-! ## 3. Transposition and inversion = the affine maps `x ↦ ±x + n`

Kalkulus gyakorló 2.16 ("elemi transzformációs lépések": shift and reflect a
graph) and 2.7 (`f ∘ f = id`, a self-inverse map) are the same two operations,
one course over `ℝ`, the other over `ZMod 12`. -/

/-- Transposition by `n` semitones, `T n`. -/
def T (n : PC) (x : PC) : PC := x + n

/-- Inversion around `n`, `I n` (reflection of the keyboard). -/
def Inv (n : PC) (x : PC) : PC := n - x

@[simp] theorem T_apply (n x : PC) : T n x = x + n := rfl
@[simp] theorem Inv_apply (n x : PC) : Inv n x = n - x := rfl

/-- Transposing twice = transposing once by the sum. -/
theorem T_comp (m n : PC) : T m ∘ T n = T (m + n) := by
  funext x; simp [T]; ring

/-- **Inversion is an involution** — the exact analogue of gyakorló 2.7,
where `f (x) = (x+1)/(x−1)` satisfies `f⁻¹ = f`. -/
theorem Inv_involutive (n : PC) : Function.Involutive (Inv n) := by
  intro x; simp

/-- Two inversions compose to a transposition: the reflections generate the
rotations. This is why "invert twice" is a way to modulate. -/
theorem Inv_comp_Inv (m n : PC) : Inv m ∘ Inv n = T (m - n) := by
  funext x; simp [T]; ring

/-- Transposition is a bijection of the twelve notes. -/
theorem T_bijective (n : PC) : Function.Bijective (T n) :=
  ⟨fun x y h => by simpa [T] using h, fun y => ⟨y - n, by simp [T]⟩⟩

/-- Inversion is a bijection of the twelve notes. -/
theorem Inv_bijective (n : PC) : Function.Bijective (Inv n) :=
  (Inv_involutive n).bijective

/-! ### The affine group over `ZMod 12`

Lineáris algebra I: a map `x ↦ a·x + b` is invertible exactly when the
"determinant" `a` is invertible. Mazzola's symmetries of a musical space are
exactly these affine maps of a module; music theory's `T` and `I` are the two
cases `a = 1` and `a = -1`. -/

/-- The affine map `x ↦ a·x + b` of the twelve-note space. -/
def affine (a b : PC) (x : PC) : PC := a * x + b

theorem T_eq_affine (n : PC) : T n = affine 1 n := by funext x; simp [T, affine]

theorem Inv_eq_affine (n : PC) : Inv n = affine (-1) n := by
  funext x; simp [Inv, affine]; ring

/-- Affine maps compose to affine maps. -/
theorem affine_comp (a b c d : PC) : affine a b ∘ affine c d = affine (a * c) (a * d + b) := by
  funext x; simp [affine]; ring

/-- An affine map is invertible exactly when its linear part is a unit — the
modular version of `det ≠ 0`. -/
theorem affine_bijective {a : PC} (b : PC) (ha : IsUnit a) : Function.Bijective (affine a b) := by
  obtain ⟨u, rfl⟩ := ha
  constructor
  · intro x y h
    have : (u : PC) * x = (u : PC) * y := by simpa [affine] using h
    have h2 := congrArg (fun z => (↑u⁻¹ : PC) * z) this
    simpa [← mul_assoc, ← Units.val_mul] using h2
  · intro y
    exact ⟨(↑u⁻¹ : PC) * (y - b), by
      simp [affine, ← mul_assoc, ← Units.val_mul]⟩

/-- There are exactly four invertible "multipliers" mod 12 — `1, 5, 7, 11` — so
the full affine group of the twelve-note space has `4 * 12 = 48` elements, of
which the `24` transpositions and inversions (`a = ±1`) are the musically
familiar half. -/
theorem units_card : Fintype.card (ZMod 12)ˣ = 4 := by decide

/-- Transposition as a permutation of the twelve notes. -/
def Tperm (n : PC) : Equiv.Perm PC := Equiv.addRight n

/-- Inversion as a permutation of the twelve notes. -/
def Invperm (n : PC) : Equiv.Perm PC :=
  ⟨Inv n, Inv n, Inv_involutive n, Inv_involutive n⟩

@[simp] theorem Tperm_apply (n x : PC) : Tperm n x = x + n := rfl
@[simp] theorem Invperm_apply (n x : PC) : Invperm n x = n - x := rfl

/-- The `T/I` group as a homomorphism from the dihedral group of order 24:
rotations of the twelve-note clock face are transpositions, reflections are
inversions. (The rotation `r i` is sent to `T (-i)`, which is the sign
convention that matches Mathlib's dihedral multiplication.) -/
def TIhom : DihedralGroup 12 →* Equiv.Perm PC where
  toFun g := match g with
    | DihedralGroup.r i => Tperm (-i)
    | DihedralGroup.sr i => Invperm i
  map_one' := by
    show Tperm (-(0 : ZMod 12)) = 1
    apply Equiv.ext; intro x; simp [Tperm]
  map_mul' := by
    rintro (i | i) (j | j) <;> apply Equiv.ext <;> intro x <;>
      simp [Tperm, Invperm, Equiv.Perm.mul_apply, DihedralGroup.r_mul_r,
        DihedralGroup.r_mul_sr, DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr, Inv] <;> ring

/-- The `T/I` group really is the dihedral group: the homomorphism is injective. -/
theorem TIhom_injective : Function.Injective TIhom := by
  rw [injective_iff_map_eq_one]
  rintro (i | i) h
  · have h0 := congrArg (fun e => (e : Equiv.Perm PC) 0) h
    simp [TIhom, Tperm] at h0
    have : i = 0 := by simpa using congrArg Neg.neg h0
    rw [this]; rfl
  · have h0 := congrArg (fun e => (e : Equiv.Perm PC) 0) h
    have h1 := congrArg (fun e => (e : Equiv.Perm PC) 1) h
    simp [TIhom, Invperm, Inv] at h0 h1
    rw [h0] at h1
    exact absurd h1 (by decide)

/-- The group generated by all transpositions and inversions has exactly
**24** elements. -/
theorem TI_card : Nat.card (TIhom.range) = 24 := by
  rw [Nat.card_congr (MonoidHom.ofInjective TIhom_injective).toEquiv.symm]
  simp [Nat.card_eq_fintype_card, DihedralGroup.card]

/-! ## 4. The interval vector: the invariant preserved by `T` and `I`

This is the "invariant of the group action" in the sense of the linear algebra
course, and the one number-list music theory uses to say that two chords *sound
alike*. -/

/-- How many ordered pairs of notes of `S` are `i` semitones apart. -/
def ivec (S : Finset PC) (i : PC) : ℕ :=
  ((S ×ˢ S).filter fun p => p.2 - p.1 = i).card

/-- **Transposition preserves the interval content**: moving a chord up the
keyboard does not change how it sounds. -/
theorem ivec_T (S : Finset PC) (n i : PC) : ivec (S.image (T n)) i = ivec S i := by
  unfold ivec
  apply Finset.card_bij' (fun p _ => (p.1 - n, p.2 - n)) (fun p _ => (p.1 + n, p.2 + n))
  · rintro ⟨a, b⟩ hp
    simp only [mem_filter, mem_product, mem_image] at hp ⊢
    obtain ⟨⟨⟨a', ha', rfl⟩, ⟨b', hb', rfl⟩⟩, hi⟩ := hp
    refine ⟨⟨by simpa [T] using ha', by simpa [T] using hb'⟩, ?_⟩
    simp only [T] at hi ⊢
    linear_combination hi
  · rintro ⟨a, b⟩ hp
    simp only [mem_filter, mem_product, mem_image] at hp ⊢
    obtain ⟨⟨ha, hb⟩, hi⟩ := hp
    exact ⟨⟨⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩⟩, by linear_combination hi⟩
  · rintro ⟨a, b⟩ _; simp
  · rintro ⟨a, b⟩ _; simp

/-- **Inversion reverses the interval content**: turning a chord upside down
sends `i`-semitone gaps to `−i`-semitone gaps, so the *unordered* interval
content is unchanged. -/
theorem ivec_Inv (S : Finset PC) (n i : PC) : ivec (S.image (Inv n)) i = ivec S (-i) := by
  unfold ivec
  apply Finset.card_bij' (fun p _ => (n - p.1, n - p.2)) (fun p _ => (n - p.1, n - p.2))
  · rintro ⟨a, b⟩ hp
    simp only [mem_filter, mem_product, mem_image] at hp ⊢
    obtain ⟨⟨⟨a', ha', rfl⟩, ⟨b', hb', rfl⟩⟩, hi⟩ := hp
    refine ⟨⟨by simpa using ha', by simpa using hb'⟩, ?_⟩
    simp only [Inv] at hi ⊢
    linear_combination -hi
  · rintro ⟨a, b⟩ hp
    simp only [mem_filter, mem_product, mem_image] at hp ⊢
    obtain ⟨⟨ha, hb⟩, hi⟩ := hp
    exact ⟨⟨⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩⟩, by linear_combination -hi⟩
  · rintro ⟨a, b⟩ _; simp
  · rintro ⟨a, b⟩ _; simp

/-! ## 5. Simple things to play: scales and chords from the group

All of these are finite checks, so Lean settles them by `decide`. -/

/-- The circle of fifths: `C G D A E B F♯ …`. -/
def fifths (k : ℕ) : PC := (7 * k : ℕ)

/-- **Playing fifths visits all twelve notes** (because `gcd (7,12) = 1`): the
circle of fifths is a single cycle, not several. -/
theorem fifths_surjective : (range 12).image fifths = univ := by decide

/-- The C major scale. -/
def diatonic : Finset PC := {0, 2, 4, 5, 7, 9, 11}

/-- The black-key pentatonic scale (transposed to start at C). -/
def pentatonic : Finset PC := {0, 2, 4, 7, 9}

/-- **The major scale is seven consecutive fifths** — stack `C G D A E B F♯`,
sort them, and you have a scale. This is the "generated scale" fact. -/
theorem diatonic_eq_seven_fifths : (range 7).image (fun k => fifths k + 5) = diatonic := by
  decide

/-- **The pentatonic scale is five consecutive fifths.** -/
theorem pentatonic_eq_five_fifths : (range 5).image fifths = pentatonic := by decide

/-- The major scale has no transpositional symmetry: shifting it always gives a
*different* set of notes, which is why all twelve major keys sound distinct. -/
theorem diatonic_asymmetric (n : PC) (h : diatonic.image (T n) = diatonic) : n = 0 := by
  revert h; revert n; decide

/-- The whole-tone scale. -/
def wholeTone : Finset PC := {0, 2, 4, 6, 8, 10}

/-- **Messiaen's limited transposition.** The whole-tone scale is unchanged by
transposition by a whole step, so it has only two transpositions in total. -/
theorem wholeTone_T2 : wholeTone.image (T 2) = wholeTone := by decide

theorem wholeTone_two_transpositions :
    (univ.image fun n : PC => wholeTone.image (T n)).card = 2 := by decide

/-- The major and the minor triad. -/
def majorTriad : Finset PC := {0, 4, 7}
def minorTriad : Finset PC := {0, 3, 7}

/-- **Major and minor are mirror images**: inverting the major triad around
`G` gives the minor triad. One hand movement, two moods. -/
theorem minor_eq_inverted_major : majorTriad.image (Inv 7) = minorTriad := by decide

/-- Consequently the two triads have the same interval content: same intervals,
different order. -/
theorem triads_same_interval_content (i : PC) : ivec minorTriad i = ivec majorTriad (-i) := by
  rw [← minor_eq_inverted_major, ivec_Inv]

/-- The three notes of the augmented triad are the orbit of `C` under
transposition by a major third: `C E G♯`, and back to `C`. -/
theorem augmented_orbit : (range 3).image (fun k => ((4 * k : ℕ) : PC)) = {0, 4, 8} := by decide

/-! ## 6. Rhythm: the same group, used for time instead of pitch

Mazzola's point is that pitch and onset-time are two coordinates of *one*
mathematical object. Concretely: a one-bar drum pattern of `n` equal slots is a
subset of `ZMod n`, and "start the loop somewhere else" is rotation — the same
`T` as transposition. -/

/-- A one-bar pattern of `n` sixteenths (or eighths) is a set of onsets. -/
abbrev Pattern (n : ℕ) := Finset (ZMod n)

/-- Rotating a drum pattern by `k` slots. -/
def rot {n : ℕ} (k : ZMod n) (x : ZMod n) : ZMod n := x + k

/-- **Transposition of a melody and rotation of a drum loop are literally the
same operation.** -/
theorem transposition_eq_rotation (n x : PC) : T n x = rot n x := rfl

/-- The *tresillo* / "3–3–2" pattern in eight eighth-notes: the backbone of
half the popular music on earth. -/
def tresillo : Pattern 8 := {0, 3, 6}

/-- The *son clave* pattern in sixteen sixteenths. -/
def clave : Pattern 16 := {0, 3, 6, 10, 12}

/-- The Euclidean rhythm `E(k, n)`: spread `k` onsets as evenly as possible over
`n` slots. -/
def euclid (k n : ℕ) : Finset (ZMod n) := (range k).image fun i => ((i * n / k : ℕ) : ZMod n)

/-- `E(3,8)` is the tresillo (up to where you start counting). -/
theorem euclid_3_8 : euclid 3 8 = {0, 2, 5} := by decide

/-- `E(5,8)` is the *cinquillo*. -/
theorem euclid_5_8 : euclid 5 8 = {0, 1, 3, 4, 6} := by decide

/-- `E(5,16)` is the son clave, rotated. -/
theorem euclid_5_16 : euclid 5 16 = {0, 3, 6, 9, 12} := by decide

/-- The tresillo has no rotational symmetry: it always tells you where beat one
is. (A pattern like `{0,2,4,6}` would not.) -/
theorem tresillo_asymmetric (k : ZMod 8) (h : tresillo.image (rot k) = tresillo) : k = 0 := by
  revert h; revert k; decide

/-- A pattern that *is* symmetric: four-on-the-floor is unchanged by rotating a
beat, which is exactly why it gives no sense of where the bar starts. -/
theorem fourOnFloor_symmetric : ({0, 2, 4, 6} : Pattern 8).image (rot 2) = {0, 2, 4, 6} := by
  decide

/-! ## 7. Polyrhythm = a product (the Chinese remainder theorem)

The 3-against-4 cross-rhythm: two hands, one playing every 3 slots, the other
every 4. They coincide exactly every 12 slots, and — this is the product
universal property of the earlier `ProductOverlap.lean` file — a position in the
12-slot bar is *the same data as* a pair (where you are in the 3-cycle, where
you are in the 4-cycle). -/

/-- **Hands meet every 12 slots.** -/
theorem polyrhythm_3_4 (t : ℕ) : (3 ∣ t ∧ 4 ∣ t) ↔ 12 ∣ t := by
  constructor
  · rintro ⟨h3, h4⟩; omega
  · rintro h; omega

/-- **3-against-4 is a product decomposition**: `ZMod 12 ≃ ZMod 3 × ZMod 4`. -/
noncomputable def polyIso : ZMod 12 ≃+* ZMod 3 × ZMod 4 :=
  ZMod.chineseRemainder (show Nat.Coprime 3 4 by decide)

/-- Reading the isomorphism concretely: a slot in the bar is determined by the
pair of positions inside the two cycles. -/
theorem polyIso_injective : Function.Injective polyIso := polyIso.injective

/-- The 12-slot bar is exactly the 3-cycle times the 4-cycle, as a count:
`12 = 3 * 4` independent choices. -/
theorem poly_card : Fintype.card (ZMod 3 × ZMod 4) = 12 := by decide

end MusicOverlap
