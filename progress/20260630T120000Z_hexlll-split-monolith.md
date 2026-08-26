# Split HexLLL/Basic.lean monolith (PR 1 of LLL release prep)

## Accomplished

Split the 2633-line `HexLLL/Basic.lean` monolith into nine
dependency-ordered modules, isolating the three reduction algorithms and
their shared helpers:

- `Lattice` — `memLattice`, `independent`, and the row-operation lattice
  lemmas (`rowSwap`/`rowAdd` preserve `memLattice`).
- `Certificate` — the packed same-lattice certificate.
- `Reduced` — `isLLLReduced` and `short_vector_bound_of_size_bound`.
- `Interval` — the dyadic interval-arithmetic kernel (`Ival`, `IntervalGS`).
- `Checker` — `lllReducedInt`/`lllReducedInterval`/`lllReducedCheck`/`certCheck`.
- `Native` — the exact integer reducer (`LLLState`, `lllNative`).
- `Steered` — the float-steered reducer (`SteeredState`, `lllSteered`).
- `Provider` — the external FFI provider (`LLLProvider`, `dispatch`).
- `Dispatch` — the public `lll` entry points.

The `HexLLL` umbrella aggregates the nine in order; `HexLLL/Basic.lean`
is now a one-line compatibility re-export (`public import HexLLL`), so
every existing `import HexLLL.Basic` consumer is untouched.

Pure move except the four row-operation lattice lemmas, which were
`private` in `namespace LLLState` but called by both Native and Steered;
they move to `namespace Matrix` in `Lattice`, become public, and their
four call sites are requalified. No proof bodies change; declaration
count is 172 before and after.

Verified: full `lake build` green (2817 jobs), 0 sorries in `HexLLL/`;
`HexLLLMathlib`, `HexConformance`, `hexlll_bench`,
`hexlll_provider_probe`, and `hexlll_emit_fixtures` all build via the
shim.

## Current frontier

PR 1 (mechanical split) complete and green. PR 2 is next: the
`HexLLLMathlib` full re-split (Bridge / Interval / Checker / State /
Reducer / ShortVector) and the two README rewrites (HexLLL three
algorithms + magic constants; HexLLLMathlib short-vector headline).

## Next step

Open PR 1, then start PR 2 on a fresh branch.

## Blockers

None.
