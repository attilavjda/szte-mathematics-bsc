# Paper Mathematics Bridge Guide
## Cross-Domain Proof Patterns for University Exams

*Based on the Caramello bridge technique applied to the Kalkulus 1 workbook (kalkulus_gyakorlo.pdf) and its structural analogues across mathematics.*

---

## Table of Contents

1. [Philosophy: The Bridge Principle on Paper](#1-philosophy)
2. [Pattern 1: ε-δ Arguments ↔ Neighbourhood / Open Set / Filter](#2-pattern-epsilon-delta)
3. [Pattern 2: Induction ↔ Well-Ordering ↔ Minimal Counterexample ↔ Recursion](#3-pattern-induction)
4. [Pattern 3: Squeeze / Comparison ↔ Sandwiching in Any Ordered Structure](#4-pattern-squeeze)
5. [Pattern 4: Injective / Surjective / Bijective ↔ Dimension ↔ Counting ↔ Graphs](#5-pattern-injectivity)
6. [Pattern 5: Factoring & Cancellation ↔ Quotient Structures](#6-pattern-factoring)
7. [Pattern 6: Supremum & Completeness ↔ Compactness ↔ Finite Subcover](#7-pattern-supremum)
8. [Pattern 7: L'Hôpital & Asymptotic Comparison ↔ Growth Rates Everywhere](#8-pattern-lhopital)
9. [Pattern 8: Mean Value Theorem ↔ Fixed Points ↔ Pigeonhole](#9-pattern-mvt)
10. [Pattern 9: Convexity ↔ Inequalities ↔ Optimization](#10-pattern-convexity)
11. [Pattern 10: Intermediate Value Theorem ↔ Connectedness ↔ Parity](#11-pattern-ivt)
12. [Quick Reference: Proof Strategy Selector](#12-quick-reference)
13. [Worked Cross-Domain Examples from the Workbook](#13-worked-examples)

---

<a name="1-philosophy"></a>
## 1. Philosophy: The Bridge Principle on Paper

### The Core Idea

Every proof has a **structural skeleton** — a pattern that is independent of the specific objects involved. The same skeleton appears across calculus, algebra, combinatorics, topology, and more. Recognising the skeleton lets you:

1. **Import intuition**: If you've seen a proof pattern in calculus, you can deploy it in algebra.
2. **Choose the easiest context**: Prove in the domain where the argument is simplest, then translate.
3. **Check your work**: If two domains give different answers for the "same" pattern, something is wrong.

### How to Use This Guide on an Exam

```
Step 1: Read the problem → identify the PROOF PATTERN (not just the topic)
Step 2: Ask: "Have I seen this pattern somewhere easier?"
Step 3: If yes: solve there mentally, then translate back
Step 4: If stuck: try reformulating in another domain for intuition
```

### Notation

Throughout this guide:
- 🔵 **Analysis/Calculus** — the home domain (from the workbook)  
- 🟢 **Algebra** — groups, rings, linear algebra  
- 🟡 **Combinatorics/Graphs** — counting, discrete structures  
- 🔴 **Topology** — open sets, continuity, connectedness  
- 🟣 **Logic** — formal statements, contrapositive, quantifiers  
- 🟤 **Geometry** — metric spaces, convexity, distance

---

<a name="2-pattern-epsilon-delta"></a>
## 2. Pattern 1: ε-δ Arguments

### The Calculus Version (Workbook §3.1)

> *Prove by definition that* lim_{x→1} 1/(x³+2) = 1/3.

The ε-δ proof:
- **Goal**: ∀ε > 0, ∃δ > 0: |x − 1| < δ ⟹ |1/(x³+2) − 1/3| < ε
- **Method**: Bound |1/(x³+2) − 1/3| in terms of |x − 1|, solve for δ.

### The Abstract Pattern: "Controlled Approximation"

> For every desired output tolerance, there exists an input tolerance that guarantees it.

This pattern is:
```
∀ ε > 0,  ∃ δ > 0,  (input within δ) ⟹ (output within ε)
```

### Equivalent Contexts

#### 🟢 Linear Algebra: Stability of Linear Systems

> *Given Ax = b, show that small perturbations in b cause small changes in x.*

If A is invertible: ‖x₁ − x₂‖ ≤ ‖A⁻¹‖ · ‖b₁ − b₂‖.

Set δ = ε / ‖A⁻¹‖. Same structure as ε-δ!

**Why it's easier here**: The bound is *linear* — no fiddling with polynomial estimates. The "δ" is explicitly computable from the operator norm.

#### 🔴 Topology: Preimage of Open Sets

> *f is continuous iff f⁻¹(U) is open for every open U.*

The ε-δ game becomes: "the preimage of every open ball is open." No quantifiers over ε needed — just one clean set-theoretic condition.

**Why it's easier here**: Composition of continuous functions is trivial: f⁻¹(g⁻¹(U)) = (g∘f)⁻¹(U), and preimage of open is open. Compare this to the ε-δ proof of composition (workbook §2.18 gives the injective version, but continuous composition is harder by ε-δ).

#### 🟡 Combinatorics: Approximation in Discrete Metrics

> *In a graph, show that vertices within distance δ of v all have property P.*

Same pattern but with δ ∈ ℕ. Often trivial because there are finitely many cases within distance δ.

#### 🟣 Logic: The Quantifier Game

The ε-δ definition is a two-player game:
- **Adversary** picks ε > 0 (the challenge)
- **Prover** responds with δ > 0 (the strategy)
- **Prover wins** if the implication holds

This is exactly a **Σ₂ sentence** in the arithmetical hierarchy: ∀∃-form. Recognising this helps with negation (the limit does NOT exist iff ∃ε∀δ the bound fails — a concrete witness).

### Beautiful Structural Solution

**Problem** (Workbook 3.1a): Show lim_{x→1} 1/(x³+2) = 1/3.

**Bridge to topology**: The function f(x) = 1/(x³+2) is a composition of continuous functions (polynomial, reciprocal away from zero). Since x³+2 > 0 for all real x, f is continuous everywhere. A continuous function satisfies f(a) = lim_{x→a} f(x) automatically. So:

> lim_{x→1} 1/(x³+2) = 1/(1³+2) = 1/3. ∎

The ε-δ proof required careful estimation. The topological proof is one line once you know composition preserves continuity. *This is the bridge in action.*

---

<a name="3-pattern-induction"></a>
## 3. Pattern 2: Induction

### The Calculus Version (Workbook §1.14–1.17)

> *Prove by induction*: Σᵢ₌₁ⁿ i = n(n+1)/2.

The standard proof:
- **Base**: n = 1: 1 = 1·2/2 ✓
- **Step**: Assume for n, prove for n+1: Σᵢ₌₁ⁿ⁺¹ i = n(n+1)/2 + (n+1) = (n+1)(n+2)/2 ✓

### The Abstract Pattern: "Reduce to a Smaller Case"

> To prove P(n) for all n, reduce P(n) to P(smaller).

### Equivalent Contexts

#### 🟢 Algebra: Structural Induction on Polynomials

> *Prove that a degree-n polynomial has at most n roots.* (Workbook §2.19)

**Induction on degree**: If p(a) = 0, write p(x) = (x − a)q(x) where deg(q) = n − 1. By induction, q has ≤ n−1 roots, so p has ≤ n roots.

**Beautiful alternative — Linear Algebra bridge**: The roots of p are eigenvalues of its companion matrix (an n×n matrix). An n×n matrix has at most n eigenvalues. ∎

This is cleaner because the dimension bound does the counting automatically.

#### 🟡 Combinatorics: Double Counting Instead of Induction

> *Prove*: Σᵢ₌₁ⁿ i = n(n+1)/2.

**Without induction**: Count the lattice points in {(i,j) : 1 ≤ i ≤ n, 1 ≤ j ≤ i}. 
- Column by column: Σᵢ₌₁ⁿ i.  
- These form a staircase that's exactly half of an n × (n+1) rectangle (the staircase plus its 180°-rotation fill the rectangle).
- So the count is n(n+1)/2. ∎

*This is the "proof without words" approach from Workbook §1.16!*

#### 🟡 Combinatorics: The Binomial Identity (Workbook §1.19)

> *Prove*: C(n-1, k-1) + C(n-1, k) = C(n, k).

**Induction**: Painful and unilluminating.

**Combinatorial bridge**: C(n,k) counts k-element subsets of {1,...,n}. Split by whether element n is included:
- Contains n: choose remaining k-1 from {1,...,n-1} → C(n-1, k-1) ways
- Doesn't contain n: choose all k from {1,...,n-1} → C(n-1, k) ways ∎

**Why this is beautiful**: The algebraic identity becomes a *tautology* about partitioning a set. No computation needed.

#### 🟢 Algebra: Well-Ordering Instead of Induction

> *Prove*: Every natural number ≥ 2 has a prime factor.

**By induction**: If n is prime, done. Otherwise n = ab with 1 < a < n, and a has a prime factor by induction.

**By well-ordering (equivalent, sometimes cleaner)**: Let S = {n ≥ 2 : n has no prime factor}. If S ≠ ∅, let m = min(S). Then m is not prime (else m is its own prime factor), so m = ab, 1 < a < m. But a ∉ S (since a < m), so a has a prime factor p. Then p | a | m, contradiction. ∎

**Why well-ordering can be cleaner**: You get a *concrete* minimal counterexample to work with, rather than a general induction hypothesis.

#### 🟡 Graph Theory: Induction on Edges

Many graph theory proofs use induction on |E| rather than |V|:

> *Prove*: A connected graph on n vertices has at least n−1 edges.

**Induction on n**: Remove a leaf (exists by tree structure), apply induction.

**Induction on |E|**: Start with n isolated vertices (0 edges, n components). Each edge reduces components by at most 1. To reach 1 component, need ≥ n−1 edges. ∎

### Strong Induction ↔ Minimal Counterexample ↔ Infinite Descent

These are all the same pattern in different clothing:

| Method | Flavour |
|--------|---------|
| Strong induction | Assume P(k) for all k < n, prove P(n) |
| Minimal counterexample | Assume ∃ counterexample, take smallest |
| Infinite descent | Assume counterexample, produce a smaller one → contradiction |

**Workbook §1.9** (√2 is irrational): Classic infinite descent on the denominator of p/q.

---

<a name="4-pattern-squeeze"></a>
## 4. Pattern 3: Squeeze / Comparison

### The Calculus Version (Workbook §3.3i, §3.6)

> lim_{x→∞} sin(2x)/x = 0.

**Squeeze**: −1/x ≤ sin(2x)/x ≤ 1/x, and both bounds → 0.

### The Abstract Pattern: "Bound Above and Below by Things You Understand"

> If L ≤ f ≤ U and L → c, U → c, then f → c.

### Equivalent Contexts

#### 🟢 Linear Algebra: Eigenvalue Bounds

> *Bound the eigenvalues of A + B.*

Weyl's inequality: λₖ(A) + λ_min(B) ≤ λₖ(A+B) ≤ λₖ(A) + λ_max(B).

Same squeeze structure: the eigenvalues of the sum are trapped between known bounds.

#### 🟡 Combinatorics: Counting by Bounds

> *How many edges in a planar graph on n vertices?*

Lower bound (if connected): ≥ n − 1. Upper bound (Euler): ≤ 3n − 6.

For triangle-free: ≤ 2n − 4. The "squeeze" narrows possibilities.

#### 🟤 Geometry: Comparison Theorems

> *In a metric space, squeeze with triangle inequality.*

d(x,z) − d(y,z) ≤ d(x,y) ≤ d(x,z) + d(y,z).

This is the geometric version of |f| ≤ g, and gives the **reverse triangle inequality** (Workbook §1.11):
> ||x| − |y|| ≤ |x − y|

#### 🟢 Algebra: Norm Bounds

> ‖AB‖ ≤ ‖A‖·‖B‖ (submultiplicativity)

This squeeze-style bound lets you estimate products of matrices. Series of matrices Σ Aⁿ converges if ‖A‖ < 1 (geometric series — exact same proof as for real numbers!).

### Beautiful Structural Solution

**Problem** (Workbook 1.15c): Prove 2√(n+1) − 2 < Σᵢ₌₁ⁿ 1/√i < 2√n − 1.

**Analysis approach**: Induction with careful algebraic manipulation.

**Bridge to geometry/integration**: Compare the sum with the integral:

∫₁ⁿ⁺¹ 1/√x dx < Σᵢ₌₁ⁿ 1/√i < 1 + ∫₁ⁿ 1/√x dx

Since ∫ 1/√x dx = 2√x, this gives:
- Lower: 2√(n+1) − 2
- Upper: 1 + 2√n − 2 = 2√n − 1 ∎

*The integral comparison replaces the induction entirely.* This is a bridge from discrete (sum) to continuous (integral).

---

<a name="5-pattern-injectivity"></a>
## 5. Pattern 4: Injective / Surjective / Bijective

### The Calculus Version (Workbook §2.2, §2.6, §2.17–2.18)

> *Show that g(x) = x³ + x + 2 is injective.* (§2.6b)

**Calculus proof**: g'(x) = 3x² + 1 > 0 always, so g is strictly increasing, hence injective.

> *Show that f∘g is injective if f, g are injective.* (§2.18)

**Direct proof**: f(g(x₁)) = f(g(x₂)) ⟹ g(x₁) = g(x₂) (f injective) ⟹ x₁ = x₂ (g injective). ∎

### The Abstract Pattern: "Structure-Preserving Maps and Their Properties"

### Equivalent Contexts

#### 🟢 Linear Algebra: Injectivity = Trivial Kernel

> *Show that T: V → W is injective.*

**Calculus approach**: Show T(v₁) = T(v₂) ⟹ v₁ = v₂.

**Linear algebra bridge**: ker(T) = {0}. Often much easier — just solve Tx = 0!

Even better: if dim(V) = dim(W) < ∞, then **injective ⟺ surjective ⟺ bijective**. This is the rank-nullity theorem. So to show a square matrix is invertible, you only need to check *one* of injective/surjective.

**Workbook connection**: For f: ℝ → ℝ, this finite-dimensional shortcut doesn't apply (ℝ is infinite-dimensional as a ℚ-vector space). But for f: {1,...,n} → {1,...,n}, injective ⟺ surjective ⟺ bijective!

#### 🟡 Combinatorics: Pigeonhole Principle

> *f: A → B with |A| > |B|. Then f is not injective.*

This is the contrapositive of: injective ⟹ |A| ≤ |B|.

**Application** (relates to Workbook §2.19): A polynomial of degree n defines a map p: ℝ → ℝ. The fibres p⁻¹(c) have size ≤ n (at most n roots). This is a "bounded fibres" condition — the combinatorial version of "at most n-to-one."

#### 🟡 Graph Theory: Matchings

Injectivity of f: A → B corresponds to a **matching** from A into B in the complete bipartite graph K_{A,B}. Hall's marriage theorem gives necessary and sufficient conditions.

#### 🟣 Logic: Function Properties as Quantifier Patterns

| Property | Logical form | Negation |
|----------|-------------|----------|
| Injective | ∀x∀y (f(x)=f(y) → x=y) | ∃x∃y (x≠y ∧ f(x)=f(y)) |
| Surjective | ∀y∃x f(x)=y | ∃y∀x f(x)≠y |
| Bijective | Both | Either negation |

The negation patterns are crucial for disproofs (Workbook §2.17: "Is f+g injective if f,g are?")

**Disproof strategy**: Find a concrete counterexample. f(x) = x, g(x) = −x are both injective, but (f+g)(x) = 0 is not. ∎

### Beautiful Structural Solution

**Problem** (Workbook §2.7): Let f: ℝ\{1} → ℝ\{1}, f(x) = (x+1)/(x−1). Show f is bijective and f = f⁻¹.

**Direct computation**: Solve y = (x+1)/(x−1) for x: x = (y+1)/(y−1) = f(y). So f∘f = id.

**Bridge to group theory**: f is an *involution* in the group of Möbius transformations. As a matrix: f ↔ [[1,1],[1,−1]]. Then f² ↔ [[1,1],[1,−1]]² = [[2,0],[0,2]] = 2·I, which acts as the identity on projective space. Any involution is its own inverse and is automatically bijective. ∎

---

<a name="6-pattern-factoring"></a>
## 6. Pattern 5: Factoring & Cancellation

### The Calculus Version (Workbook §3.4)

> *Compute* lim_{x→2} (x−2)/(x²−4).

**Factor**: (x−2)/(x²−4) = (x−2)/((x−2)(x+2)) = 1/(x+2) for x ≠ 2. Limit = 1/4.

### The Abstract Pattern: "Remove the Common Obstruction"

> When a numerator and denominator both vanish, factor out the common zero and cancel.

### Equivalent Contexts

#### 🟢 Algebra: Quotient by an Ideal

Factoring (x−2) from both numerator and denominator is *exactly* working in the quotient ring ℝ[x]/(x−2), i.e., evaluating at x = 2 after removing the common factor.

> The 0/0 indeterminate form = trying to evaluate in a ring where you've divided by zero. The fix = work in the quotient, or equivalently, cancel the common factor.

#### 🟢 Linear Algebra: Rank Reduction

> Simplify the matrix (A − λI) when λ is an eigenvalue.

The determinant det(A − λI) = 0 (the "0/0" situation). The resolution: instead of inverting, study ker(A − λI) — the eigenspace. This is "cancellation" in the matrix world.

#### 🟡 Combinatorics: Cancellation in Binomial Coefficients

> Simplify C(n,k)/C(n,k−1).

C(n,k)/C(n,k−1) = (n−k+1)/k.

The "common factors" n! cancel, leaving a simple ratio. This is exactly the polynomial limit technique applied to factorial expressions.

#### 🟡 Graph Theory: Edge Contraction

When two vertices are identified (contracted), the resulting graph "cancels" the edge between them — analogous to factoring out (x − a) when f(a) = 0.

### Beautiful Structural Solution

**Problem** (Workbook §3.4d): Compute lim_{x→1} (x³−2x²+x)/(x³−3x+2).

**Direct factoring**: 
- Numerator: x(x−1)² 
- Denominator: (x−1)²(x+2) [since 1 is a double root]
- Cancel (x−1)²: limit = x/(x+2)|_{x=1} = 1/3. ∎

**Bridge to algebra**: Both polynomials have x = 1 as a root of multiplicity 2. The "order of vanishing" (valuation at x = 1) is 2 for both. After subtracting valuations (i.e., cancelling), we get a well-defined evaluation. This is the *p-adic valuation* perspective — the limit exists iff the numerator vanishes to at least the same order as the denominator.

---

<a name="7-pattern-supremum"></a>
## 7. Pattern 6: Supremum & Completeness

### The Calculus Version (Workbook §1.4, §1.5, §3.14)

> *Show that the supremum is unique.* (§1.5)

> *A bounded monotone function on (a,b) has a limit at b⁻.* (§3.14)

### The Abstract Pattern: "Every Bounded Monotone Net Converges"

This relies on **completeness** — the defining property of ℝ.

### Equivalent Contexts

#### 🔴 Topology: Compactness

> *Every sequence in [a,b] has a convergent subsequence.* (Bolzano-Weierstrass)

In topology: [a,b] is **compact**. This single word encodes: every open cover has a finite subcover, every sequence has a convergent subsequence, every continuous function attains its bounds.

**The bridge**: "bounded + closed in ℝⁿ" = "compact" (Heine-Borel). Once you know this equivalence, many analysis theorems become one-liners:

| Analysis theorem | Topological version |
|-----------------|-------------------|
| Extreme value theorem | Continuous image of compact is compact; compact ⊂ ℝ is bounded and has max/min |
| Uniform continuity on [a,b] | Continuous on compact = uniformly continuous |
| Bolzano-Weierstrass | Compact = sequentially compact (in metric spaces) |

#### 🟢 Algebra: Ascending Chain Condition

> *In a Noetherian ring, every ascending chain of ideals stabilises.*

I₁ ⊆ I₂ ⊆ I₃ ⊆ ... eventually becomes constant. This is the algebraic analogue of "bounded monotone sequences converge." The completeness of ℝ becomes the Noetherian property.

#### 🟡 Combinatorics: Finite Sets Are "Complete"

> Every subset of a finite totally ordered set has a maximum.

No axiom of completeness needed — just finiteness! This is why combinatorial arguments often avoid the subtleties of analysis.

#### 🟣 Logic: The Completeness Theorem

> Every consistent first-order theory has a model.

Gödel's completeness theorem is the logical analogue of "every bounded set has a supremum." The sup is the model; boundedness is consistency.

### Beautiful Structural Solution

**Problem** (Workbook §3.14): If f is bounded and monotone increasing on (a,b), show lim_{x→b⁻} f(x) exists.

**Analysis proof**: Let L = sup{f(x) : x ∈ (a,b)}. For any ε > 0, ∃x₀ with f(x₀) > L − ε. For x₀ < x < b: L − ε < f(x₀) ≤ f(x) ≤ L. So |f(x) − L| < ε. ∎

**Bridge to topology**: The image f((a,b)) is a bounded subset of ℝ, hence has compact closure. The monotonicity forces the net {f(x) : x → b⁻} to be eventually in any neighbourhood of sup. This is the "every net in a compact space has a cluster point, and monotone nets can have at most one" argument. ∎

The bridge doesn't simplify this particular proof, but it *explains* why the result is true: it's a consequence of compactness + order, which work the same way in any complete lattice.

---

<a name="8-pattern-lhopital"></a>
## 8. Pattern 7: L'Hôpital & Asymptotic Comparison

### The Calculus Version (Workbook §4.10)

> *Compute* lim_{x→0} (eˣ − 1 − x)/x².

**L'Hôpital** (twice): → lim (eˣ − 1)/(2x) → lim eˣ/2 = 1/2.

### The Abstract Pattern: "Compare Growth Rates via Derivatives"

> When f(a) = g(a) = 0, the ratio f/g near a is determined by their rates of vanishing.

### Equivalent Contexts

#### 🟢 Algebra: Taylor Expansion ↔ Power Series Ring

The "real" L'Hôpital is secretly about comparing **orders of vanishing**:
- eˣ − 1 − x = x²/2 + x³/6 + ... has order 2
- x² has order 2
- Ratio of leading coefficients: (1/2)/1 = 1/2.

**In the formal power series ring ℝ[[x]]**: this is just "divide and read off the constant term." No limits needed!

> L'Hôpital's rule is the analytic shadow of algebraic division in the power series ring.

#### 🟡 Combinatorics: Asymptotic Analysis

> Compare f(n) and g(n) as n → ∞.

Same pattern: f(n) ~ g(n) means f(n)/g(n) → 1. Stirling's approximation n! ~ √(2πn)(n/e)ⁿ is the discrete analogue of Taylor expansion.

| Analysis | Combinatorics |
|----------|--------------|
| Taylor expansion | Asymptotic expansion |
| L'Hôpital for 0/0 | Ratio of leading terms |
| L'Hôpital for ∞/∞ | Growth rate comparison |

#### 🟢 Linear Algebra: Perturbation Theory

> How do eigenvalues of A + εB behave as ε → 0?

λ(ε) = λ₀ + ε·λ₁ + ε²·λ₂ + ... — a power series in ε. The "leading term" determines the first-order perturbation. Same structure as L'Hôpital: the ratio of changes is determined by the first non-vanishing term.

### Beautiful Structural Solution

**Problem** (Workbook §4.10c): Compute lim_{x→0} 10(sin x − x)/x³.

**L'Hôpital** (3 applications): Tedious but works, gives −10/6 = −5/3.

**Bridge to power series**: sin x = x − x³/6 + ..., so sin x − x = −x³/6 + .... Therefore:
> 10(sin x − x)/x³ → 10·(−1/6) = −5/3. ∎

One line, no derivatives needed. *The Taylor series IS the bridge.*

---

<a name="9-pattern-mvt"></a>
## 9. Pattern 8: Mean Value Theorem ↔ Fixed Points ↔ Pigeonhole

### The Calculus Version

> *If f is continuous on [a,b] and differentiable on (a,b), then ∃c ∈ (a,b): f'(c) = (f(b)−f(a))/(b−a).*

### The Abstract Pattern: "An Average Must Be Achieved Somewhere"

> If a quantity has a certain average over an interval, it must achieve that average at some point.

### Equivalent Contexts

#### 🟡 Combinatorics: Pigeonhole Principle

> *If n+1 pigeons are in n holes, some hole has ≥ 2 pigeons.*

Equivalently: if the average is > 1, the maximum is > 1. This is the *discrete MVT*.

More precisely: if f: {1,...,n} → ℝ and Σf(i)/n = A, then max f(i) ≥ A and min f(i) ≤ A.

#### 🟡 Graph Theory: Average Degree

> *In a graph with m edges and n vertices, average degree = 2m/n. So ∃ vertex with degree ≥ 2m/n.*

This is pigeonhole = discrete MVT applied to the degree sequence.

#### 🟢 Algebra: Fixed Point Theorem (Contraction)

Consider g(x) = f(x) − ((f(b)−f(a))/(b−a))·x. Then g(a) = g(b), so by Rolle's theorem (MVT with slope 0), g'(c) = 0 somewhere.

In functional analysis, the **Banach fixed point theorem** is the infinite-dimensional generalisation: if T is a contraction, then T has a unique fixed point. The proof is by iteration — the *same* idea as Newton's method from calculus!

#### 🔴 Topology: The Borsuk-Ulam Theorem

> *There exist antipodal points on Earth with the same temperature and pressure.*

This is a topological generalisation of IVT/MVT: continuous functions on spheres must have "coincidence points." The MVT says a function's derivative must sometimes equal the average slope; Borsuk-Ulam says continuous functions on Sⁿ must have "averaging" coincidences.

### Beautiful Structural Solution

**Problem** (Workbook §1.10b): For irrational x, show infinitely many rationals r/s satisfy |x − r/s| < 1/s².

**Analysis approach**: Pigeonhole on fractional parts (Dirichlet's theorem).

**Bridge**: Consider n+1 numbers {0, {x}, {2x}, ..., {nx}} in [0,1). Divide [0,1) into n equal intervals. By pigeonhole, two numbers {jx} and {kx} land in the same interval of length 1/n. So |{jx} − {kx}| < 1/n, which gives |x − r/s| < 1/(ns) ≤ 1/s² where s = |j−k| ≤ n.

*The same pigeonhole principle that counts pigeons proves a deep result in Diophantine approximation.*

---

<a name="10-pattern-convexity"></a>
## 10. Pattern 9: Convexity ↔ Inequalities ↔ Optimization

### The Calculus Version (Workbook §4.8–4.9, §4.11–4.15)

> *Decompose 20 into two parts maximising their product.* (§4.11a)

**Calculus**: f(x) = x(20−x), f'(x) = 20−2x = 0 at x = 10. Max = 100. 

> *Midpoint convexity ⟹ convexity for continuous functions.* (§4.13)

### The Abstract Pattern: "Convex Functions Are Controlled by Their Boundary Values"

### Equivalent Contexts

#### 🟢 Linear Algebra: Positive Definite Matrices

> A matrix is positive definite iff xᵀAx > 0 for all x ≠ 0.

The function q(x) = xᵀAx is convex iff A is positive semidefinite. Convex functions on compact sets attain minima at the boundary or at critical points — the same as in calculus!

**AM-GM as a matrix inequality**: For positive definite A, B:
det((A+B)/2) ≥ √(det(A)·det(B))

This is the matrix AM-GM, proved via convexity of − log det.

#### 🟡 Combinatorics: Jensen's Inequality

> If f is convex: f(Σ λᵢxᵢ) ≤ Σ λᵢf(xᵢ).

This is the master inequality behind:
- AM-GM: f(x) = −log x is convex
- Power mean inequalities
- Cauchy-Schwarz (f(x) = x²)
- Many competition inequalities

#### 🟤 Geometry: Supporting Hyperplanes

> A convex function lies above every tangent line.

f(y) ≥ f(x) + f'(x)(y − x) for all x, y.

This is the geometric content of convexity. In higher dimensions, tangent lines become **supporting hyperplanes**, and convex sets are intersections of half-spaces.

**Workbook §4.13** (midpoint convexity + continuity ⟹ convexity): 

The bridge is to see this as: "a measurable midpoint-convex function is convex" — a deep result in real analysis that connects the algebraic property (midpoint convexity) to the analytic property (full convexity) via the topological property (continuity/measurability).

### Beautiful Structural Solution

**Problem** (Workbook §4.11a): Decompose 20 = a + b, maximise ab.

**Calculus**: Derivative, critical point, second derivative test.

**Bridge to AM-GM**: For any a, b ≥ 0:
> ab ≤ ((a+b)/2)² = 100 (AM-GM)

Equality iff a = b = 10. ∎

One line, no calculus needed. The AM-GM inequality IS the optimality condition.

**Problem** (Workbook §4.12): Among circular sectors with given perimeter, find the one with maximum area.

**Calculus**: Set up A = rθ/2, perimeter 2r + rθ = P, eliminate, differentiate.

**Bridge to AM-GM**: A = r(P − 2r)/2. By AM-GM: r(P − 2r) ≤ ((r + P − 2r)/2)² = (P/2)²·... Wait, more carefully: A = rθ/2 and P = 2r + rθ, so θ = (P − 2r)/r and A = (P − 2r)/2 · r/1 = r(P − 2r)/2. Maximise r(P − 2r) subject to r > 0, P − 2r > 0. By AM-GM on {r, P − 2r}: r(P−2r) ≤ (P/2)²/... Actually let's use: for fixed sum r + (P/2 − r) = P/2, the product r(P/2 − r) is maximised when r = P/4. Then θ = (P − P/2)/(P/4) = 2. So the optimal sector has θ = 2 radians. ∎

---

<a name="11-pattern-ivt"></a>
## 11. Pattern 10: Intermediate Value Theorem ↔ Connectedness ↔ Parity

### The Calculus Version (Workbook §2.19, §2.20)

> *Odd-degree polynomials have at least one real root.*

**Proof**: lim_{x→∞} p(x) = +∞ and lim_{x→−∞} p(x) = −∞ (for positive leading coefficient). By IVT, p(c) = 0 for some c.

### The Abstract Pattern: "Connected Sets Cannot Be Split"

> If f is continuous and f takes values on both sides of a threshold, it must cross the threshold.

### Equivalent Contexts

#### 🔴 Topology: Connectedness

> *A space is connected iff every continuous function to {0,1} is constant.*

The IVT says: ℝ (and all intervals) are connected. A continuous function on a connected space has connected image, which in ℝ means an interval.

**Why this matters**: Connectedness arguments work in *any* topological space. You can prove:
- "The general linear group GL(n,ℝ) has exactly 2 connected components" (det > 0 and det < 0)
- "The orthogonal group O(n) has 2 components" (det = ±1)
- "SL(n,ℝ) is connected" — continuous path from any A to I

#### 🟡 Graph Theory: Graph Connectivity

> *A graph is connected iff there is a path between any two vertices.*

The discrete IVT: if f: V → ℤ assigns values to vertices of a connected graph, and f(u) < 0 < f(v), then some edge {x,y} has f(x) ≤ 0 ≤ f(y).

**Application**: Sperner's lemma (the combinatorial IVT) proves the Brouwer fixed point theorem!

#### 🟡 Combinatorics: Parity Arguments

> *In any sequence of n² + 1 distinct numbers, there is a monotone subsequence of length n + 1.*

This is proved by a pigeonhole/parity argument that is structurally identical to IVT: assign to each element its "longest increasing subsequence length." If none reaches n+1, then by pigeonhole, two elements share the same length, and a decreasing subsequence of length n+1 emerges.

#### 🟢 Algebra: Sign Changes

> *A polynomial changes sign ⟹ it has a root.*

More generally, in any ordered field that satisfies IVT (= real-closed field), odd-degree polynomials have roots. This characterises the real numbers among ordered fields!

### Beautiful Structural Solution

**Problem**: Show that any continuous function f: [0,1] → [0,1] has a fixed point.

**IVT proof**: Let g(x) = f(x) − x. Then g(0) = f(0) ≥ 0 and g(1) = f(1) − 1 ≤ 0. By IVT, g(c) = 0, so f(c) = c. ∎

**Bridge to topology**: [0,1] has the fixed point property because it is a retract of the disk D², which has the fixed point property by Brouwer's theorem, which follows from the non-retractability of D² onto S¹, which is a consequence of π₁(S¹) = ℤ ≠ 0.

The IVT proof is obviously simpler here! But the topological perspective explains *why* the result generalises to higher dimensions (Brouwer) and *why* it fails for open intervals (0,1) (not compact) and circles S¹ (not simply connected).

---

<a name="12-quick-reference"></a>
## 12. Quick Reference: Proof Strategy Selector

### Given a Problem Type, Choose the Best Domain

| Problem Type | Best Domain for Proof | Why |
|---|---|---|
| lim_{x→a} f(x) with f a composition | 🔴 Topology (continuous = preimage of open) | Composition is trivial |
| lim_{x→a} f(x)/g(x), both → 0 | 🟢 Algebra (Taylor/power series) | Read off ratio of leading coefficients |
| Prove identity Σᵢf(i) = g(n) | 🟡 Combinatorics (double counting) | Often gives proof without induction |
| Show f is injective | 🟢 Linear Algebra (ker = 0) | Reduces to solving one equation |
| Show n-to-1 map | 🟡 Combinatorics (pigeonhole) | Counting argument |
| Optimise f on [a,b] | 🟤 Geometry (AM-GM, Cauchy-Schwarz) | Often one-line inequality |
| Show ∃ root of polynomial | 🔴 Topology (connectedness/IVT) | Avoids explicit construction |
| Show uniqueness | 🟣 Logic (assume two, derive contradiction) | Universal pattern |
| Show convergence of sequence | 🔵 Analysis (monotone + bounded → complete) | ℝ completeness |
| Show convergence rate | 🟢 Algebra (Taylor/asymptotic) | Order of vanishing |
| Bound a sum | 🔵 Analysis → 🟤 Geometry (integral comparison) | Continuous relaxation |

### The Contrapositive Bridge (Logic ↔ Everything)

For ANY proof, you can try the contrapositive:

| Original | Contrapositive |
|----------|---------------|
| P ⟹ Q | ¬Q ⟹ ¬P |
| "If f is differentiable, then f is continuous" | "If f is not continuous, then f is not differentiable" |
| "If the series converges, then aₙ → 0" | "If aₙ ↛ 0, then the series diverges" |

The contrapositive is especially useful when ¬Q gives you concrete information to work with.

### The Proof by Contradiction Bridge

| Domain | "Assume not" gives you... |
|--------|--------------------------|
| Analysis | A sequence that doesn't converge → extract a subsequence (compactness!) |
| Algebra | An element not in the ideal → construct a maximal ideal containing it (Zorn) |
| Combinatorics | A counterexample graph → minimal counterexample (well-ordering) |
| Topology | A space that's not connected → a clopen set → continuous function to {0,1} |

---

<a name="13-worked-examples"></a>
## 13. Worked Cross-Domain Examples from the Workbook

### Example A: Generalised Triangle Inequality (§1.13)

> *Show*: |a₁ + a₂ + ... + aₙ| ≤ |a₁| + |a₂| + ... + |aₙ|.

**Workbook approach**: Induction on n using |x + y| ≤ |x| + |y|.

**Bridge to linear algebra**: The absolute value is a **norm** on ℝ. The triangle inequality for norms says ‖Σvᵢ‖ ≤ Σ‖vᵢ‖. This holds in ANY normed space (ℝⁿ, function spaces, matrix spaces). The 1D case is a special case of a universal principle.

**Bridge to geometry**: |a₁ + ... + aₙ| is the length of the sum-vector. Laying vectors end-to-end, the straight-line distance (left side) is ≤ the path length (right side). The geometric picture makes the inequality *obvious*.

### Example B: Sum of Cubes (§1.14b)

> *Show*: 1³ + 2³ + ... + n³ = (n(n+1)/2)².

**Workbook approach**: Induction.

**Bridge to combinatorics**: (n(n+1)/2)² = (1 + 2 + ... + n)² = (Σi)². So the identity says Σi³ = (Σi)². 

**Elegant proof via double counting**: Consider the n×n multiplication table. The entry in row i, column j is ij. The sum of all entries is (Σi)² (by factoring rows and columns). But also, group entries by their value... Actually, the slickest proof:

Consider the identity k³ = k² · k. Observe that k³ counts the number of ordered pairs (a,b) with 1 ≤ a ≤ k and 1 ≤ b ≤ k, weighted by k. A beautiful bijective proof exists using "L-shaped" regions (gnomons) in an n×n grid, where the k-th gnomon has exactly k² + (k-1)·k + ... wait, let me give the clean version:

**Proof without words**: In the n×n grid, tile with L-shaped gnomons. The k-th gnomon consists of row k and column k (minus the corner counted twice). It contains 2k−1 cells, but we weight by... Actually the simplest combinatorial proof:

> Σ_{k=1}^n k³ = Σ_{k=1}^n k · k² = number of triples (i, j, k) with 1 ≤ j ≤ i ≤ n and 1 ≤ k ≤ i... 

The cleanest bridge: note that k³ = (1+2+...+k)² − (1+2+...+(k−1))² (telescoping!). Summing gives (1+2+...+n)². ∎

### Example C: Continuous Functions Agreeing on ℚ (§3.15)

> *If f, g are continuous on ℝ and f(q) = g(q) for all q ∈ ℚ, show f = g everywhere.*

**Analysis proof**: For any x ∈ ℝ, take rationals qₙ → x. Then f(x) = lim f(qₙ) = lim g(qₙ) = g(x).

**Bridge to topology**: ℚ is **dense** in ℝ. A continuous function is determined by its values on a dense subset. This is because two continuous functions f, g: X → Y (Y Hausdorff) that agree on a dense subset agree everywhere — the agreement set {x : f(x) = g(x)} is closed (preimage of the diagonal, which is closed in Y × Y), and a closed set containing a dense subset is the whole space. ∎

**Why the topology proof is better**: It immediately generalises to any Hausdorff space and any dense subset, not just ℚ ⊂ ℝ.

### Example D: The "Frog Problem" (§1.6)

> *A frog starts at 0, jumps 1/2, then 1/4, then 1/8, ... Does it reach 1?*

**Analysis**: Σ_{n=1}^∞ 1/2ⁿ = 1. The partial sums converge to 1 but never reach it.

**Bridge to binary representation**: 0.111...₂ = 1. Each jump adds the next binary digit. The sum IS the binary representation of 1.

**Bridge to geometry**: The interval [0,1] is repeatedly halved. After n jumps, the remaining distance is 1/2ⁿ → 0. The frog gets arbitrarily close but (in finitely many jumps) never arrives. This illustrates the difference between a limit and achieving the limit — a key conceptual point.

### Example E: (1 + 1/n)ⁿ < (1 + 1/(n+1))ⁿ⁺¹ (§3.16b)

**Workbook approach**: Use §3.16a with appropriate a, b.

**Bridge to AM-GM**: Let's prove (1 + 1/n)ⁿ is increasing using the AM-GM inequality.

Consider n+1 numbers: n copies of (1 + 1/n) and one copy of 1. By AM-GM:

> [(1+1/n)ⁿ · 1]^{1/(n+1)} ≤ [n(1+1/n) + 1]/(n+1) = (n+2)/(n+1) = 1 + 1/(n+1)

So (1+1/n)^{n/(n+1)} ≤ 1 + 1/(n+1), hence (1+1/n)ⁿ ≤ (1+1/(n+1))^{n+1}. ∎

*AM-GM gives the monotonicity of eₙ = (1+1/n)ⁿ for free!*

### Example F: Irrationality of √2 (§1.9)

**Workbook approach**: Classic proof by contradiction with even/odd parity.

**Bridge to algebra**: In ℤ, the prime factorisation of a² has even exponents for every prime. If (p/q)² = 2, then p² = 2q², but the left side has even exponent of 2, and the right has odd. Contradiction by unique factorisation. ∎

**Bridge to linear algebra**: √2 is irrational iff the polynomial x² − 2 is irreducible over ℚ. By Eisenstein's criterion with p = 2: 2 | 0 (leading coeff is 1, so this doesn't apply directly). By the rational root theorem: possible rational roots are ±1, ±2, none satisfy x² = 2. ∎

**Bridge to geometry**: If √2 = p/q, then the isosceles right triangle with legs q has hypotenuse p. Scale the triangle so that p, q are minimal integers. Fold the triangle to create a smaller isosceles right triangle with integer sides — contradiction with minimality. (This is the geometric version of infinite descent.)

---

## Appendix: The Master Table of Structural Analogies

| Calculus/Analysis | Linear Algebra | Combinatorics | Topology | Algebra | Geometry |
|---|---|---|---|---|---|
| Limit | Eigenvalue | Asymptotic growth | Cluster point | Completion | Accumulation point |
| Continuity | Bounded operator | Graph homomorphism | Preimage of open | Ring homomorphism | Lipschitz map |
| Derivative | Jacobian/linear map | Finite difference | Tangent space | Derivation on algebra | Tangent vector |
| Integral | Trace | Counting | Measure | Character sum | Area/Volume |
| Convergence | Spectral convergence | Eventual property | Filter convergence | Cauchy sequence | Metric convergence |
| Bounded | Bounded operator | Finite set | Compact | Finitely generated | Bounded diameter |
| Monotone | Positive operator | Monotone graph property | Order-preserving | Homomorphism | Non-decreasing distance |
| Supremum | Operator norm | Maximum | Least upper bound | Maximal ideal | Farthest point |
| Completeness | Hilbert space | N/A (always complete) | Compactness | Noetherian | Geodesic completeness |
| IVT | Eigenvalue interlacing | Sperner's lemma | Connectedness | Real-closed field | Jordan curve theorem |
| MVT | Mean trace | Average degree | — | — | Chord vs arc |
| Convexity | PSD matrices | Matroids | — | — | Convex bodies |
| Taylor series | Matrix exponential | Generating functions | — | Formal power series | Local approximation |

---

## Final Thought: The Bridge Mindset

The deepest skill in mathematics is not knowing many theorems — it is **recognising when two problems have the same proof**. This guide maps out the most common structural isomorphisms between proof patterns in different domains.

On an exam, when you're stuck:
1. **Name the pattern** (not the topic).
2. **Ask: where have I seen this pattern succeed easily?**
3. **Translate** the easy proof into the required language.

The mathematical content — the "truth" — lives in the pattern, not in any particular domain. You are free to prove it wherever it is easiest, then bridge the result back.

> *"The same theorem, seen from different angles, is understood in its full depth."*

---

*This guide accompanies `AnalysisBridges.lean` and `AnalysisBridges_Guide.md`. See those files for formally verified Lean proofs of the key bridge theorems.*
