# HexLLL release polish: READMEs + HexLLLMathlib re-split (PR 2)

## Accomplished

Builds on PR 1 (the HexLLL monolith split). Two pieces:

**README rewrites.**
- `HexLLL/README.md`: now explains the one-entry / three-reducer design
  (external provider -> steered -> native, all certified to `(δ, 11/20)`),
  names the surface by group, and adds a "size-reduction bound and its
  constants" treatment: `121/400 = (11/20)²= η²`, why `11/20` and not the
  classical `1/2`, the honest dimension-compounding cost (at `δ = 3/4` the
  per-vector length factor is ~5.7% larger per dimension), and what
  tightening would take. Quickstart type-checked.
- `HexLLLMathlib/README.md`: now headlines the short-vector approximation
  guarantee — the reduced first row is at most `(1/(δ−121/400))^((n−1)/2)`
  times the length of any nonzero lattice vector, hence of the shortest —
  quoting `lll_first_row_norm_sq_le_unconditional` with the squared-norm to
  length translation, and the native classical companion. Quickstart
  type-checked.

**HexLLLMathlib full re-split** into honest layers (declaration count 102
before and after; pure move):
- `Bridge.lean` — `latticeSubmodule`, the `EuclideanSpace` embeddings + norm
  transport, the conditional Euclidean bound.
- `Interval.lean` — interval checker soundness (unchanged).
- `Checker.lean` — exact/dispatched checker soundness (`lllReducedInt_sound`,
  `lllReducedCheck_sound`, `certCheck_sound`); imports `Interval`.
- `State.lean` — `LLLState` validity glue (`ofBasis_valid`, `ν_eq_coeffs`,
  the Lovász-test equivalence).
- `Reducer.lean` — the `namespace Hex` reducer correctness development plus the
  rational capstones (formerly the misnamed `Independent.lean`).
- `ShortVector.lean` — the Euclidean headline capstones and submodule
  lattice-preservation transfers.

The old `Basic.lean` and `Independent.lean` are removed; the umbrella imports
the six in dependency order (Interval, State, Bridge, Checker, Reducer,
ShortVector). No external file imported the submodules directly, so no shim is
needed.

## Current frontier

HexLLLMathlib re-split build verification in progress.

## Next step

Confirm green, commit PR 2, open it stacked on PR 1.

## Blockers

None.
