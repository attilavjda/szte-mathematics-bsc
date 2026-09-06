# Ten tiny LEGO blocks for a first calculus exam

*Structural / diagrammatic moves — not algebra. Draw first, compute last.*

Running example (from `SUMMARY.md`):  `f(x) = arctan( 3 / (x³+1)^(1/3) ) + e^π`.
Machine-checked companion: `RequestProject/CalcBlocks.lean` (each block is one
lemma, plus the block "clicked onto" this `f`).

---

## The universal first move: **draw the arrows**

Any exam formula is a *path in a category of maps*. Write it as one elementary
arrow per box, and reserve a second row underneath for the linearisations:

```
   x ──(·)³+1──▶ t ──t^(−1/3)──▶ u ──3·(−)──▶ v ──arctan──▶ w ──+e^π──▶ f(x)
   │             │               │            │             │
 D ▼             ▼               ▼            ▼             ▼
   1 ── 3x² ───▶ 1 ─(−1/3)t^(−4/3)▶ 1 ── 3 ──▶ 1 ─1/(1+v²)─▶ 1 ── 0 ──▶ f′(x)
```

Everything below is a rule for **reading rows of this picture** instead of
manipulating symbols. Each block is small, composable, and reusable.

---

### Block 1 — ARROW ▸ ARROW  (chain rule = functoriality)
`D(g∘f) = Dg ∘ Df`. On the line, composing `1×1` matrices = **multiplying the
labels**. So you never differentiate the whole formula; you multiply the bottom row.
*Cost:* one line per box. *Payoff:* no product/quotient-rule bookkeeping at all.
→ `block_compose_arrows`

### Block 2 — TERMINAL ARROW  (constants are invisible)
A box with no incoming wire dies under `D`. `e^π ≈ 23.14` looks scary and
contributes exactly `0`. **Cross out every constant before starting.**
→ `block_kill_constant`, `exam_const_is_dead`

### Block 3 — SCALARS SLIDE  (linearity)
A number on a wire slides straight through the `D` box: `D(c·f) = c·Df`.
Pull all constants to the front *before* differentiating; they never re-enter.
→ `block_scalar_slides`

### Block 4 — ISO ▸ ISO  (invertible arrow ⇒ invertible label)
If `g∘f = id`, then along the bottom row `g′(f(x))·f′(x) = 1`. This *regenerates*
forgotten formulas under exam stress: from `(tan)′ = 1+tan²` you get
`(arctan)′ = 1/(1+x²)` with no algebra; likewise `log` from `exp`, `ⁿ√` from `xⁿ`.
→ `block_inverse_labels`

### Block 5 — SIGN ▸ ORDER  (the sign of the label is a functor)
You rarely need the *value* of `f′`, only its **sign**. Count minus signs along
the diagram. One negative label on a connected piece ⇒ the graph falls there ⇒
strictly antitone ⇒ injective ⇒ at most one solution of `f(x)=y`.
For our `f` on `x>0`: the only negative label is `−1/3`, so `f` decreases.
→ `block_sign_to_order`, `exam_strictAntiOn`, `exam_injOn`

### Block 6 — SYMMETRY  (fold the paper)
`f` even ⇒ `f′` odd; `f` odd ⇒ `f′` even. Halves the work on a symmetric problem
and is a free 5-second **sanity check** on any derivative you just computed:
if the parity of your answer is wrong, the answer is wrong.
→ `block_even_deriv_odd`, `block_odd_deriv_even`

### Block 7 — ZERO LABEL ▸ ONE POINT  (identities without algebra)
To show `F = G` on an interval: show `F′ = G′` and check **one** value.
(Vanishing derivative on a connected domain ⇒ the map factors through a point.)
This is the standard weapon for `arctan`/`log` identities, e.g.
`arctan x + arctan(1/x) = π/2` for `x > 0`.
→ `block_identity_by_deriv`, `arctan_add_arctan_inv`

### Block 8 — CODOMAIN ▸ BOUND  (read the target, not the formula)
`arctan` lands in `(−π/2, π/2)` no matter what you feed it. So `arctan(mess)+c`
is trapped in a horizontal strip: boundedness, horizontal asymptotes and
"does `f(x)=0` have a solution?" are settled by the **type** of the arrow.
Here `|f(x) − e^π| < π/2`, and since `e^π > π+1 > π/2`, `f` is never `0`.
→ `block_codomain_bound`, `exam_in_strip`, `exam_ne_zero`

### Block 9 — LIMITS COMPOSE  (push `lim` along the chain)
Block 1 one level down: walk the arrows and push the limit through each
continuous box. `x³+1 → +∞ ⟹ (x³+1)^(−1/3) → 0 ⟹ arctan(3·0) = 0`, so
`f(x) → e^π` as `x → +∞`. The asymptote is *read*, not computed.
→ `block_push_limit`, `exam_tendsto_atTop`

### Block 10 — CONNECTEDNESS ▸ EXISTENCE  (solve nothing, still find a root)
IVT = "a continuous arrow preserves connectedness". Two sample values straddling
`y` give you a solution you can never write down. Snap it to Block 5 and the
solution is **unique**.
→ `block_ivt`, `block_ivt_anti`, `exam_attains_between`

---

## How to snap them together on an unseen exercise

1. **Draw** the arrow chain (universal first move).
2. **Block 2 + 3**: delete constants, pull scalars out front.
3. **Block 1**: multiply the labels — that's the derivative, done.
4. **Block 6**: parity check on your answer.
5. **Block 5**: signs of the labels ⇒ monotonicity, injectivity, extrema.
6. **Block 8 + 9**: the codomain and the two limits ⇒ the range and the asymptotes.
7. **Block 10 (+5)**: existence and uniqueness of solutions of `f(x) = y`.
8. **Block 4 / 7**: recover a forgotten derivative; prove an identity without expanding.
9. Only now, if the question insists, **simplify** — and change coordinates first
   (`a = (x³+1)^(1/3)`, so `t = a³`) so fractional powers become polynomials.

*Rule of thumb:* if you are manipulating symbols for more than three lines, you
skipped a block.
