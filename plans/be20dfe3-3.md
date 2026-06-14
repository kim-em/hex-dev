## Current state

`HexConway/Basic.lean` exposes a systematic family of `private`
irreducibility wrappers `luebeckConwayPolynomialOfCoeffs_{p}_{n}_irreducible`
(36 in total, for p ∈ {2,3,5,7,11,13} and n ∈ 1..6). Each wrapper
proves `FpPoly.Irreducible (luebeckConwayPolynomialOfCoeffs p coeffs)`
by rewriting through the `luebeckConwayPolynomial?_hit_{p}_{n}`
lookup-table hit to the named literal and discharging via that
literal's `_irreducible` proof. The wrappers are currently
**undocumented**. This is part of the library's Phase 6 (proof
polishing) docstring-coverage exit criterion.

This issue covers **only the p ∈ {2, 3} subset** (12 wrappers,
currently lines ~2305–2436):

- `luebeckConwayPolynomialOfCoeffs_2_1_irreducible` … `_2_6_irreducible`
- `luebeckConwayPolynomialOfCoeffs_3_1_irreducible` … `_3_6_irreducible`

The p ∈ {5,7,11,13} wrappers are deliberately left for a separate
batch to keep this edit bounded and to avoid two workers colliding in
the same region.

## Deliverables

1. Add a one-sentence `/-- … -/` docstring to each of the 12 p∈{2,3}
   wrappers above. A uniform template is appropriate, e.g. "The
   coefficient-list constructor for the committed `C(p, n)` Conway
   entry yields an irreducible `FpPoly`, via the
   `luebeckConwayPolynomial?` table hit and the literal's
   irreducibility proof." Vary `p`/`n` per declaration.
2. Doc-only change: do **not** touch any signature, statement, proof,
   declaration order, or `private` modifier. Additions must be
   docstring lines only. Do **not** touch the p ∈ {5,7,11,13}
   wrappers.

## Context

- This matches the established "Phase 6 docstrings" issue pattern
  (cf. the merged `cert_p_n_incremental_check` Conway batch).
- Phase 6 doc rule: `SPEC/design-principles.md`; `PLAN/Phase6.md`.
- If the subset has already been documented by a racing PR,
  `coordination skip` with that note.

## Verification

- `lake build HexConway.Basic`: green.
- `git diff --numstat -- HexConway/Basic.lean`: additions only
  (`12 0`).
- `git diff --check`: clean.
- Added-line grep finds no `sorry` / `axiom` / `native_decide` /
  `TODO` / `FIXME`.
- `python3 scripts/check_dag.py`: exit 0.
