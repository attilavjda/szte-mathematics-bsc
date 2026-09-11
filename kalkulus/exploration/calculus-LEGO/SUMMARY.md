# Tiny summary — "category-theory moves" for a calculus exam

Exercise: differentiate  `f(x) = arctan( 3 / (x³+1)^(1/3) ) + e^π`.

## The picture (draw this first, on paper)

Write `f` as a **chain of arrows**, one elementary map per arrow:

```
        x ──(·)³+1──▶ t ──t^(−1/3)──▶ u ──3·(−)──▶ v ──arctan──▶ w ──+e^π──▶ f(x)

  D ↓          ↓              ↓             ↓            ↓            ↓
        1 ─── 3x² ──▶ 1 ─(−1/3)t^(−4/3)▶ 1 ── 3 ──▶ 1 ─1/(1+v²)─▶ 1 ── id ──▶ f′(x)
```

## The three moves

1. **Chain rule = functoriality.** `D` sends a composite to the composite of the
   linearisations: `D(g∘h) = Dg ∘ Dh`. On the line, "compose 1×1 matrices" = multiply
   the labels. So you never differentiate the whole formula: you read the bottom row.
2. **Constants are the terminal arrow.** `e^π` is a constant map, `D(const) = 0`.
   Numbers that *look* scary (`e^π ≈ 23.14`) contribute nothing; don't touch them.
   Same for the scalar `3`: multiplication by a scalar is linear, so it *is* its own derivative.
3. **Change coordinates before simplifying.** Put `a = (x³+1)^{1/3}`, so `t = a³`.
   All rpow bookkeeping becomes polynomial algebra in `a`, and the answer collapses.

## The pen-and-paper computation

Labels multiplied, with `t = x³+1`:

```
f′(x) = 1/(1 + (3 t^(−1/3))²) · 3 · (−1/3) t^(−4/3) · 3x²
      = −3x² t^(−4/3) / (1 + 9 t^(−2/3))            (multiply top & bottom by t^(4/3))
      = −3x² / ( t^(2/3) · ( t^(2/3) + 9 ) ).
```

**Answer** (valid where `x³+1 > 0`, so the cube root is single-valued):

```
f′(x) = −3x² / ( (x³+1)^(2/3) · ((x³+1)^(2/3) + 9) )
```

Sign check straight off the diagram: for `x > 0` every label is positive except `−1/3`,
so `f′ < 0` — `f` decreases.

## The tiny Lean file

`RequestProject/CalcExam.lean` — machine-checked, no `sorry`:

* `fExam` — the function;
* `hasDerivAt_fExam` / `deriv_fExam` — the boxed answer above;
* `deriv_const_exp_pi` — move 2 (`e^π` differentiates to `0`);
* `deriv_fExam_neg` — the sign check for `x > 0`.

The Lean proof is literally the diagram: one `HasDerivAt` per arrow, composed with
`.rpow_const`, `.const_mul`, `.arctan`, `.add_const`.
