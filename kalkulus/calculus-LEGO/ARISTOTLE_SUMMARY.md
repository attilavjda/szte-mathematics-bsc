# Summary of changes for run 404ca96f-f1b3-45f7-9286-964b04a17559
I added a reusable toolkit of ten small, structural "LEGO blocks" for first-exam calculus — diagrammatic/logical moves rather than algebraic manipulation — as a one-page cheat sheet plus a machine-checked Lean file, both snapped onto the running example f(x) = arctan(3/(x³+1)^(1/3)) + e^π.

**`BLOCKS.md`** — the pen-and-paper page. Universal first move: draw the formula as a chain of arrows with a second row underneath for the linearisations. Then ten blocks:
1. ARROW ▸ ARROW — chain rule is functoriality; multiply the labels along the bottom row instead of differentiating a formula.
2. TERMINAL ARROW — constants are invisible to D; cross out `e^π` before starting.
3. SCALARS SLIDE — numbers pass straight through D.
4. ISO ▸ ISO — an invertible arrow has an invertible label (`g′(f x)·f′(x)=1`): regenerate a forgotten `arctan`/`log`/root derivative from its inverse.
5. SIGN ▸ ORDER — count minus signs on the diagram: sign of the derivative ⇒ falling graph ⇒ injectivity ⇒ at most one solution.
6. SYMMETRY — even ⇒ odd derivative and conversely; halves symmetric problems and is a free parity sanity check on any answer.
7. ZERO LABEL ▸ ONE POINT — prove identities by equal derivatives plus one value (the arctan/log trick), no expansion.
8. CODOMAIN ▸ BOUND — read the target of the arrow: `arctan(mess)+c` is trapped in a strip, settling boundedness/asymptotes/solvability.
9. LIMITS COMPOSE — push `lim` along the chain through continuous boxes.
10. CONNECTEDNESS ▸ EXISTENCE — IVT (rising and falling forms) gives roots you can never write down; with block 5 they become unique.
It ends with a recipe for snapping the blocks together on an unseen exercise.

**`RequestProject/CalcBlocks.lean`** — every block stated once in general form and proved, with no `sorry` (verified by a full build and an axiom check: only the standard `propext`/`Classical.choice`/`Quot.sound`). Generic blocks: `block_compose_arrows`, `block_kill_constant`, `block_scalar_slides`, `block_inverse_labels`, `block_sign_to_order`, `block_even_deriv_odd`/`block_odd_deriv_even`, `block_identity_by_deriv`, `block_codomain_bound`, `block_push_limit`, `block_ivt`/`block_ivt_anti`. Applied to the exam function (reusing the earlier `fExam` and its derivative): `exam_const_is_dead`, `exam_strictAntiOn` and `exam_injOn` (strictly decreasing on [0,∞)), `exam_in_strip` and `exam_ne_zero` (never vanishes), `exam_tendsto_atTop` (horizontal asymptote `e^π`), and `exam_attains_between` (blocks 10 + 5: every value between f(1) and f(0) is attained on [0,1] exactly once).

The earlier files (`SUMMARY.md`, `RequestProject/CalcExam.lean`) are untouched; everything is committed and pushed.

# Summary of changes for run 2318a496-66b0-4f98-b9f4-7116dd6126cc
Added two small files.

**`SUMMARY.md`** — a one-page, pen-and-paper "category-theory moves" cheat sheet for the exercise `f(x) = arctan(3/(x³+1)^(1/3)) + e^π`:
- an ASCII diagram of `f` as a chain of arrows `x ↦ x³+1 ↦ t^(−1/3) ↦ 3·(−) ↦ arctan ↦ +e^π`, with the linearisation of each arrow drawn underneath;
- three moves: (1) chain rule = functoriality of `D`, so you just multiply the labels along the bottom row; (2) constants (`e^π`) are killed by `D`, scalars (`3`) pass through; (3) substitute `a = (x³+1)^{1/3}` (so `t = a³`) to turn fractional-power bookkeeping into polynomial algebra;
- the resulting answer, valid where `x³+1 > 0`:  `f′(x) = −3x² / ( (x³+1)^{2/3} · ((x³+1)^{2/3} + 9) )`, plus the sign reading `f′ < 0` for `x > 0`.

**`RequestProject/CalcExam.lean`** — the tiny Lean companion, built cleanly with no `sorry`:
- `fExam` — the function (with `3/(x³+1)^{1/3}` written as `3·(x³+1)^{−1/3}`);
- `hasDerivAt_fExam` and `deriv_fExam` — the boxed derivative formula, assuming `x³+1 > 0` so the real cube root is the intended branch;
- `deriv_const_exp_pi` — the `e^π` term differentiates to `0`;
- `deriv_fExam_neg` — `deriv fExam x < 0` for `x > 0`.

The Lean proof mirrors the drawing exactly: one `HasDerivAt` fact per arrow, composed with `.rpow_const`, `.const_mul`, `.arctan`, `.add_const`. Everything is committed and pushed.