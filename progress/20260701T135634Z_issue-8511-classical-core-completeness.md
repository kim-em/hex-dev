# Issue #8511 classical-core completeness structural lemmas

## Accomplished

Delivered the classical-core completeness trio and the residual-arm
reassembly discharger, mirroring the exhaustive-tier analogs.

In `HexBerlekampZassenhaus/Basic.lean` (Mathlib-free layer):
- Two new smart-core mutual-recursion families over the size-ordered
  search (`Aux` / `SizeLoop` / `CandLoop`), siblings of the existing
  `scaledRecombinationSmartAux_shouldRecord`:
  - `scaledRecombinationSmartAux_normalizeFactorSign` — each emitted
    factor is `normalizeFactorSign`-fixed (candidate is
    `normalizeFactorSign …`, closed by `normalizeFactorSign_idem`).
  - `scaledRecombinationSmartAux_primitive` — each emitted factor is
    primitive (record gate forces the candidate nonzero, so the inner
    `primitivePart` argument has nonzero content).
- `classicalCoreFactorsWithBound_spec`, a private structural case-split:
  every `some cf` result is either the short-circuit singleton `#[core]`
  (`B = 0`, budget-`none`, empty-result all return `#[core]`) or a
  nonempty recombination whose product reconstructs `core` with each
  factor sign-fixed, primitive, and recorded. Destructures via
  `generalize` (no Mathlib `set` in this layer).
- The public trio consuming the spec:
  `classicalCoreFactorsWithBound_polyProduct`,
  `_normalizeFactorSign` (needs `0 < leadingCoeff core`),
  `_degree_pos` (needs `0 < core.degree?.getD 0`; the singleton arm
  emits `core`, so core-degree positivity is genuinely required —
  unlike the exhaustive-trial analog).

In `HexBerlekampZassenhausMathlib/IntReductionMod.lean`:
- `reassemblyExpansionComplete_classicalCore_of_ne_zero`, the classical
  analog of `reassemblyExpansionComplete_exhaustiveIntegerTrial_of_ne_zero`:
  wires the trio + #8510's
  `classicalCoreFactorsWithBound_squareFreeCore_factor_zpolyIrreducible`
  into `reassemblyExpansionComplete_of_irreducible_squarefree_cover_of_pos_lc`
  (per-factor positive leading coefficient and the fuel bound follow
  generically, exactly as in the exhaustive analog).

`lake build HexBerlekampZassenhausMathlib` green; no new `sorry`/`axiom`;
no new warnings in the touched files. Second opinion (Codex) found no
soundness issues; its one low-severity note (unused `hcore_prim` /
`hcore_pos` on `_degree_pos`) was addressed by trimming the signature to
the sole needed hypothesis `hcore_deg`.

## Current frontier

Both classical-residual ingredients now exist: #8510's per-factor
irreducibility and this issue's completeness side condition.

## Next step

#8414 residual arm consumes
`reassemblyExpansionComplete_classicalCore_of_ne_zero` (with #8510) to
drop the `factor_irreducible_of_nonUnit` classical-branch `sorry`.

## Blockers

None.
