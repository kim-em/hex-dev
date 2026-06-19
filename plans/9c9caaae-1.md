## Current state

`HexArith/Barrett/Reduce.lean` (the executable `UInt64` Barrett reduction
layer for `HexArith`; imports only `HexArith.Barrett.ReduceNat`) packages
the modulus and its reciprocal in `BarrettCtx`, defines the single-word
`barrettReduce` step, and states the equations relating the `UInt64` code
to `barrettReduceNat`. It carries three public `@[simp]` characterising
lemmas, none of which are tagged `@[grind =]` — the file currently has zero
`grind` annotations, so downstream `grind` goals over `pinv`/`barrettReduce`
cannot close without an explicit lemma list. This is the same asymmetry the
ongoing Phase 6 "grind automation coverage" sweep removes file by file (cf.
the sibling `HexArith/Barrett/Context.lean` pass in #8032, plus #8034,
#8035).

The `@[simp]`-only candidates (re-read each before promoting):

- `BarrettCtx.toNat_pinv` (46) — `ctx.pinv.toNat = barrettRadix / p.toNat`
  (unconditional literal `lhs = rhs`).
- `toNat_barrettReduce_eq_mod` (140) —
  `(barrettReduce ctx T).toNat = T.toNat % p.toNat`, conditional on
  `hT : T.toNat < p.toNat * p.toNat`.
- `barrettReduce_eq_self_of_lt` (163) — `barrettReduce ctx T = T`,
  conditional on `hT : T < p`.

All three are equation-shaped; the latter two are *conditional* equations
(they carry a side hypothesis). `grind =` accepts conditional rewrites and
discharges the side condition as a subgoal, so they remain eligible — but
re-read each at the current line numbers before promoting, since the file
may have shifted.

## Deliverables

1. Promote the equation-shaped `@[simp]` lemmas listed above to
   `@[simp, grind =]`, matching the convention used across the Phase 6
   sweep. Only promote literal/conditional `lhs = rhs` forms; if any turns
   out on re-reading to be an iff/inequality/proof-valued, leave it
   `@[simp]`-only and say which and why in the PR body.
2. Confirm the new oriented `grind =` rewrites are sound and do not loop.
   The two `barrettReduce` rewrites have distinct LHS head patterns
   (`(barrettReduce …).toNat` vs `barrettReduce …`) and reduce to
   `barrettReduce`-free RHSs, so no cycle is expected; verify and note in
   the PR body. If any lemma loops, leave it `@[simp]`-only and explain.
3. Confirm no `grind` loop or build-time regression in the module.

## Context

One file in the ongoing Phase 6 "grind automation coverage" sweep: one
`.lean` file per issue, promoting the equation-shaped public `@[simp]`
characterising lemmas to `@[simp, grind =]` so downstream `grind` goals
close without an explicit lemma list. Scope is confined to
`HexArith/Barrett/Reduce.lean`; do not touch other files. `HexArith` is a
Mathlib-free executable library — do not introduce any Mathlib dependency.
No existing issue or PR covers this file (#8032 covers the sibling
`Barrett/Context.lean`, not `Reduce.lean`).

## Verification

- `lake build HexArith` → `Build completed successfully`, and
  `HexArith.Barrett.Reduce` builds without a grind-loop slowdown.
- `python3 scripts/check_dag.py` → exit 0.
- `git diff --check` clean; no added-line `sorry`/`axiom`/`native_decide`/
  `TODO`/`FIXME`.
