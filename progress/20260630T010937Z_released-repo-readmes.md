# Released-repo READMEs + Phase 7 README process

## Accomplished

- Added a README contract and wired it into the SPEC/PLAN/publish processes:
  - `SPEC/readme.md`: the five-section contract (intro, Quickstart,
    Functionality, Verification, Contributing), the build-checked quickstart
    rule, the bridge-library adaptation, and the "headline theorem as a Lean
    signature" guidance for Verification.
  - `SPEC/SPEC.md`: linked the new doc in Navigation.
  - `PLAN/Phase7.md`: README is now a per-library Phase 7 deliverable and exit
    criterion for any library published as a split repo.
  - `scripts/release/released.yml` + `scripts/release/sync_released.py`:
    `<Lib>/README.md` is now a managed publish path -> released repo root
    `README.md` (excluded from the lib-dir rsync; opt-out via `readme: false`).
    Verified with `sync_released.py --dry-run`.
- Wrote root READMEs for all 13 released repos (source at `<Lib>/README.md`):
  HexMatrix, HexDeterminant, HexRowReduce, HexBareiss, HexGramSchmidt, HexLLL,
  Hex (hex-test-kit), and the six `*-mathlib` bridges. Every quickstart snippet
  was build-checked (`lake env lean`, or `#check` where an `@[extern]` op such
  as `Matrix.exactDiv` blocks interpreter `#eval`).
- HexDeterminant README Verification now states column linearity
  (`det_setCol_add`) and Laplace (`det_eq_foldl_laplace_row`) as full Lean
  signatures, with Cauchy-Binet / adjugate / Plücker named in prose.
- Added the matrix-level adjugate identity to the library:
  `HexDeterminant/Adjugate.lean` now has
  `mul_adjugate : M * adjugate M = det M • 1`, so the README cites it without
  "stated entrywise". Full `lake build` is green.

## Current frontier

- All 13 READMEs are drafted, build-checked, and pass a structural lint
  (five sections, correct require name, no banned words/em-dashes).
- The `*-mathlib` bridge libraries are NOT default `lake build` targets, so
  their oleans go stale after `HexMatrix` is rebuilt; verifying their snippets
  needs an explicit `lake build <BridgeLib>` first. The agents' "toolchain
  mismatch" reports were a misread of the batteries `v4.30.0-rc2` pin plus this
  stale-olean effect, not a real version conflict.

## Next step

- Kim to review the drafts. Two minor stylistic choices left open:
  HexGramSchmidt mixes `#check` (Bareiss-backed, extern) and `#eval` (pure-data
  ops) in its quickstart; hex-bareiss-mathlib shows inline `-- @foo : ...`
  type comments that the other bridge quickstarts omit.
- Once approved, the publish sync will carry the READMEs to the released repos.

## Blockers

- None.
