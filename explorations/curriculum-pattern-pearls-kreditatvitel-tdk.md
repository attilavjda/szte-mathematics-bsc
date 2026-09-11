# Curriculum pattern pearls: turning "common themes of linear algebra and analysis" into credit, a TDK paper, and a mobility case

*Context: SZTE BSc (likely levelező), wanting to use **kreditelismerés / kreditátvitel**,
aiming at **TDK → OTDK**, and to publish short "verification pearl" preprints built from
Lean 4 formalisations of patterns shared by the linear algebra and analysis strands of the
curriculum.*

> **Please read this caveat.** I cannot browse the live web, and university rules
> (Tanulmányi és Vizsgaszabályzat, kreditátviteli eljárás, TDK deadlines, mobility calls)
> are set locally and change every year. Everything about administration below is
> **orientation to verify** with (1) the **SZTE TTIK Tanulmányi Osztály / Kreditátviteli
> Bizottság**, (2) your **intézeti TDK-felelős**, and (3) the **SZTE Nemzetközi Mobilitási
> Iroda**. The **Lean part is different**: it is machine-checked and is in this repository.

---

## 0. The one-paragraph answer

Your idea is sound, and its strongest form is narrow, not broad. Do **not** try to "map
category theory onto the whole BSc". Instead pick **one pattern per paper**, show it
*literally is* two named theorems from two different courses by proving the abstract
statement once in Lean 4 and deriving both named theorems as instances, and keep each
paper to 4–8 pages. That is a *verification pearl*: a small, complete, reproducible
artifact. It is exactly the kind of object that (a) a kreditátviteli/„egyéni tanulmányi
teljesítés" request can be attached to, (b) a TDK jury can evaluate in 15 minutes, and
(c) a foreign host can read before deciding to invite you for ten days.

**Pearl #1 already exists and compiles in this repository** — see §1.

---

## 1. What is already machine-checked here (`CurriculumPatterns/`)

The new Lean library `CurriculumPatterns/` is the first pearl, fully proved, no `sorry`,
no extra axioms. Its content is one sentence:

> **The triangle inequality of analysis and submultiplicativity of the operator norm of
> linear algebra are the same axiom** — laxness of a *cost* for *composition* — read in
> two different ordered monoids; and the determinant is that same axiom made *strict*.

Concretely:

| Module | Curriculum item | Ordered monoid | Theorem recovered |
|---|---|---|---|
| `LaxCost.lean` | — (the pattern) | any preorder + monotone `op` | `LaxCost.cost_chain` (lax), `LaxCost.cost_chain_eq` (strict) |
| `MetricPearl.lean` | Analízis: metric spaces | `(ℝ≥0, +, 0)` | polygon inequality `dist (x 0) (x n) ≤ ∑ dist (x i) (x (i+1))` |
| `OperatorPearl.lean` | Lineáris algebra / funkcionálanalízis: operator norm | `(ℝ≥0, ·, 1)` | `‖fⁿ‖ ≤ ‖f‖ⁿ` |
| `LipschitzPearl.lean` | Analízis: contractions, Banach fixed point | `(ℝ≥0, ·, 1)` | `LipschitzWith (Kⁿ) f^[n]` |
| `DeterminantPearl.lean` | Lineáris algebra: determinant | `(ℝ≥0, ·, 1)`, strict | `|det (Aⁿ)| = |det A|ⁿ` |
| `Functoriality.lean` | both | pullback of a cost along a functor | `LipschitzWith K g` **is** a comparison of two costs |

Why this is a real result and not a slogan:

- The abstract lemma `LaxCost.cost_chain` is proved **once**, by induction on composition
  alone. It never mentions ℝ, metrics or norms.
- The four curriculum theorems are then obtained *from it*, each in a few lines, by
  choosing (i) the composition system and (ii) the ordered monoid. Nothing else changes.
- The linear-algebra/analysis split turns out to be **only the choice of monoid**:
  `(ℝ≥0, +, 0)` gives triangle-type sums, `(ℝ≥0, ·, 1)` gives submultiplicative products.
  That is Lawvere's reading of a metric space as an enriched category, made executable.
- The strict/lax distinction (`IsStrict`) explains, in one predicate, why determinants
  satisfy an *equality* and norms only an *inequality*: strict = functor, lax = lax functor.

This is the shape every later pearl should copy: **one abstract lemma, two courses, no
new mathematics required to state it, all of it checked**.

---

## 2. A roadmap of further pearls (each 4–8 pages, each one abstract lemma)

Ordered by (low risk × high curriculum coverage). Each row is one paper + one Lean module.

| # | Pattern | Linear algebra side | Analysis / calculus side | Categorical name |
|---|---|---|---|---|
| 1 ✅ | cost is lax for composition | `‖AB‖ ≤ ‖A‖‖B‖`, `det` multiplicative | triangle inequality, `Lip(g∘f) ≤ Lip g · Lip f` | enrichment over an ordered monoid |
| 2 | universal property of a kernel | kernel of a linear map | solution set of a homogeneous ODE / null space of a differential operator | equalizer / limit |
| 3 | bilinear = linear from a tensor | matrix of a bilinear form | integral pairing `⟨f,g⟩ = ∫ fg` | adjunction `⊗ ⊣ Hom` |
| 4 | limits are preserved by continuous maps | linear maps preserve finite sums | continuity as preservation of limits of sequences | functor preserving (co)limits |
| 5 | direct sum = product = biproduct | `V ⊕ W` in finite dimension | `ℓ²`-type splittings, orthogonal decomposition | biproducts in an additive category |
| 6 | invariance under change of basis / coordinates | trace, determinant, rank | chain rule, substitution in an integral | invariants = functors; naturality square |
| 7 | dual space and transpose | `Aᵀ`, dual basis | integration by parts as adjointness | duality functor, adjoint pair |

Two honest warnings, so you do not lose a semester:

- **Row 6 is the ambitious one.** "Naturality of the chain rule" is genuinely nice
  (the derivative is a functor from pointed spaces to linear maps), but the formalisation
  cost in Mathlib is markedly higher than rows 1–5. Do it *after* two easy pearls exist.
- **Do not restate Mathlib.** The value is not "this theorem is now in Lean" (most of
  rows 1–7 are already in Mathlib somewhere). The value is **the derivation direction**:
  the abstract pattern first, the curriculum theorems as corollaries. Make sure every
  pearl's headline theorem is *derived from your abstract lemma*, not proved directly and
  decorated afterwards. In pearl #1 that is why, for example, `nnnorm_det_pow` is proved
  via `cost_chain_eq` even though `simp` could close it alone.

---

## 3. Packaging for kreditátvitel / kreditelismerés

Credit transfer normally recognises *learning outcomes* (tanulási eredmények), not effort.
So do not submit "I wrote Lean code"; submit a mapping table. For each targeted course:

1. Take the official **tárgytematika** and extract its listed topics verbatim.
2. Build a three-column table: **topic in the tematika → theorem in my artifact →
   file + theorem name (machine-checked)**. For pearl #1 that table already exists as the
   table in §1, and every right-hand cell is a real, compiling Lean name.
3. Add a one-page cover note stating: the artifact builds with `lake build`, contains no
   `sorry`, and depends only on Lean's standard axioms (`propext`, `Classical.choice`,
   `Quot.sound`) — which is checkable by a third party in one command.

Realistic expectations, in order of likelihood of a "yes":

- **Most likely:** recognition as **szakmai gyakorlat / önálló projektmunka / választható
  tárgy** credit, or as the substance of a **szakdolgozat** or an individual study contract
  (egyéni tanrend / egyéni teljesítés) agreed with a supervisor.
- **Plausible:** partial exemption from a *specific* course whose tematika your table
  covers largely (rare for core Analízis/Lineáris algebra — those are usually examined in
  a fixed way).
- **Unlikely:** blanket exemption from a core course based on research output.

The lever that actually moves this is a **supervisor (témavezető)** inside the relevant
intézet who signs the mapping table. Pick the person whose course the pearl touches, not
the most famous person.

---

## 4. TDK → OTDK, concretely

- **TDK** is institutional and runs (usually) once or twice a year with an autumn or
  spring house conference; **OTDK is biennial**, and entry to it is normally via a
  qualifying result at the institutional TDK. So the practical sequence is
  *artifact → institutional TDK → OTDK section* — you cannot skip the first step.
  Verify the current section (Matematika és Informatika Tudományi Szekció is the natural
  one) and its deadline with your intézeti TDK-felelős; deadlines are typically many
  months before the conference.
- **Format that wins in this genre:** a 15–20 page dolgozat around **one** pearl, a live
  demo where you `lake build` in front of the jury and hover a theorem in the editor, and
  a claim stated so it can be falsified ("every theorem in the table is derived from the
  single abstract lemma"). A jury cannot check a 200-page survey; it can check a green
  build.
- **Reusability:** the same document body becomes the arXiv preprint (cs.LO or math.CT,
  cross-list math.HO) with an artifact link. One writing effort, three outputs
  (TDK dolgozat, preprint, mobility work plan).

---

## 5. Why this project also *is* the mobility application

A ten-day visit needs a work plan that a host can accept in one reading. Yours can be:

> "I have a compiling Lean 4 library in which the triangle inequality and operator-norm
> submultiplicativity are instances of one enrichment lemma. In ten days at your group I
> want to add the *kernel-as-equalizer* pearl (row 2), with your feedback on the
> categorical formulation, and leave with a joint short preprint draft."

That is falsifiable, small, and finishable in ten days — the three properties that make a
short-visit request easy to say yes to. See the companion note
`category-theory-itp-mobility-eu-eea-uk.md` for who to send it to and which funding rail
carries a ten-day trip.

---

## 6. Next actions

- [ ] Run `lake build CurriculumPatterns` yourself and skim the six modules; you must be
      able to explain `LaxCost.cost_chain` from memory in two minutes.
- [ ] Choose the **one** course whose tematika you will map first, and download the
      official tematika PDF.
- [ ] Identify a **témavezető** in that intézet; send the §1 table plus a two-paragraph
      note. Ask explicitly: "what would you need for this to count as X credits?"
- [ ] Ask the Tanulmányi Osztály the exact procedural questions: what documents does a
      kreditátviteli kérelem need, what is the deadline, and can research output count
      toward a választható/projekt course.
- [ ] Ask the intézeti TDK-felelős for this year's institutional TDK deadline and the
      dolgozat format requirements.
- [ ] Start pearl #2 (kernel as equalizer) as a `sorry`-skeleton before the visit request
      goes out, so the work plan describes something already begun.
