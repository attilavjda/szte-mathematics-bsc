# Music ↔ Kalkulus I ↔ Lineáris algebra I

**`MusicOverlap.pdf`** (source `MusicOverlap.tex`) — the write-up: the simple
overlaps between *The Topos of Music*, the two `Tárgytematika` documents and
`kalkulus_gyakorlo.pdf`, and the patterns that realise them at the piano or on
the drums.

**`../RequestProject/MusicOverlap.lean`** — every mathematical claim the write-up
makes, proved in Lean (no `sorry`).

## The seven overlaps in one screen

| Shared object | Syllabus item | Music | Play it |
|---|---|---|---|
| `log` / `exp` inverse pair | Kalkulus: exponential functions and their inverses (gy. 2.1e, 2.3, 2.13c) | pitch = log₂ of frequency; semitone = 2^(1/12) | octaves; hear that an interval is a *ratio* |
| quotient `ℤ → ℤ/12`, periodicity | Kalkulus: periodic functions (2.16g); Lin. alg.: homomorphism, kernel | octave equivalence, pitch classes | re-voice a triad: C–E–G, E–G–C, G–C–E |
| affine maps `x ↦ ±x + n` | Kalkulus gy. 2.16 (shift/reflect a graph), 2.7 (`f⁻¹ = f`) | transposition `T n`, inversion `Inv n` | transpose a riff; play it in mirror image |
| group, composition, inverse | Lin. alg.: inverse matrices; Kalkulus gy. 2.18 | the T/I group, 24 elements (dihedral) | two mirrors = one transposition |
| group action + invariant | Lin. alg.: linear maps, invariants | interval content of a chord | major → minor by moving one finger (`Inv 7`) |
| the cyclic group, for time | Lin. alg.: `ℤ/n`; Kalkulus: periodicity | rhythms as subsets of `ℤ/n` | tresillo `x..x..x.`, son clave, Euclidean rhythms |
| product / CRT `ℤ/12 ≅ ℤ/3 × ℤ/4` | Lin. alg.: direct product; Kalkulus gy. 1.4d | time–pitch coordinates | the 3-against-4 polyrhythm |

## Four things to play today

1. **Piano, circle of fifths** — C G D A E B F♯ C♯ G♯ D♯ A♯ F C. It closes up
   into one cycle because gcd(7,12)=1 (`fifths_surjective`).
2. **Piano, mirror** — right hand up `x` semitones, left hand down `x`. Two such
   mirrors, around C and around G, equal a transposition by a fifth
   (`Inv_comp_Inv`).
3. **Piano, one-finger mood change** — C–E–G → C–E♭–G is the inversion `Inv 7`
   (`minor_eq_inverted_major`); the interval content is unchanged
   (`triads_same_interval_content`).
4. **Drums, tresillo** — kick on `x..x..x.` (3–3–2) over eight eighths, snare on
   2 and 4. It has no rotational symmetry, so it tells you where beat one is
   (`tresillo_asymmetric`) — unlike four-on-the-floor (`fourOnFloor_symmetric`).

## Building the PDF

```
tectonic -X compile MusicOverlap.tex     # or: pdflatex MusicOverlap.tex (twice)
```
