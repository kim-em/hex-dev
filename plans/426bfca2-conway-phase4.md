## Current state

`scripts/status.py` reports `HexConway -> Phase 4 (performance &
benchmarking)` ready, with `libraries.yml` recording
`HexConway.done_through: 3` and no `status/hex-conway.benchmarks-reviewed`
token yet (only `status/hex-conway.scaffolding-reviewed` from #1078 exists).

The Phase 4 surface is already in place:

- `HexConway/Bench.lean` exists with one parametric registration
  (`runLuebeckConwayPolynomialLookupChecksum` with
  `tier1LookupComplexity _ := 1`) and seven fixed registrations
  (`runConwayPolySupported_2_1Checksum`,
  `runTier1Irreducibility_{2_1,2_6,3_6,5_6,7_6,11_6,13_6}Checksum`).
- `lakefile.lean:211` registers `lean_exe hexconway_bench`.
- `.github/workflows/ci.yml:62-63` already runs
  `lake exe hexconway_bench list` and `lake exe hexconway_bench verify`.
- Closed Phase 4 issues #2180, #2193, #2209, #2216 added the Tier 1 lookup
  harness and the fixed irreducibility benchmarks.

The remaining Phase 4 work is an audit/run/bump pass: confirm the benchmark
surface covers the Tier 1 SPEC API (the only tier this slice promises),
run the parametric registration so the `tier1LookupComplexity` constant
model gets a `consistent` verdict, and either bump
`HexConway.done_through` to `4` and write `status/hex-conway.benchmarks-reviewed`
or file a narrow follow-up if a missing Tier 1 deliverable is found.

Phase 4 here is intentionally Tier-1 only: `SPEC/Libraries/hex-conway.md`
documents Tier 2 (full Conway verification of imported entries) and Tier 3
(on-demand Conway search) as separate, slower features whose Phase 4 work
is not promised by this bump. Do not extend coverage to Tier 2 or Tier 3
in this issue.

## Deliverables

1. Verify `HexConway/Bench.lean` against `SPEC/Libraries/hex-conway.md`,
   `SPEC/benchmarking.md`, and `PLAN/Phase4.md`. Confirm every Tier 1
   advertised operation is registered and that the `tier1LookupComplexity`
   constant-time textbook model is the right declaration for committed-table
   lookup.
2. Run the `runLuebeckConwayPolynomialLookupChecksum` parametric scientific
   benchmark and record the verdict in the PR body. Re-run the seven fixed
   registrations under their declared `repeats` and confirm
   `expectedHash` agreement.
3. If the artifacts are coherent and the parametric verdict is consistent
   with the declared model, bump `libraries.yml` so
   `HexConway.done_through: 4` and add a `status/hex-conway.benchmarks-reviewed`
   token referencing this issue. If verification finds a missing Tier 1
   deliverable or an inconsistent verdict, leave `libraries.yml` and
   `status/` unchanged and file a narrow follow-up `agent-plan` issue with
   the observed evidence.

## Library placement

- File path: `libraries.yml` and `status/hex-conway.benchmarks-reviewed`,
  only if verification succeeds. Existing context files to inspect include
  `HexConway/Bench.lean`, `HexConway/Basic.lean`,
  `status/hex-conway.scaffolding-reviewed`, `.github/workflows/ci.yml`,
  and `lakefile.lean`.
- SPEC section: `SPEC/Libraries/hex-conway.md` defines Tier 1 / Tier 2 /
  Tier 3 and explicitly says Tier 2 and Tier 3 are out of scope for this
  Phase 4 bump.
- Q1: this is the HexConway Phase 4 completion review and bump.
- Q2: no Mathlib is needed; the executable HexConway benchmark target is
  Mathlib-free.
- Q3: this is Hex project phase bookkeeping, not an upstream Mathlib theorem.
- Q4: no prerequisite issue is known; if a missing Tier 1 deliverable is
  found, file it and do not bump the phase counter.

## Context

Read `SPEC/Libraries/hex-conway.md`, `SPEC/benchmarking.md`,
`PLAN/Phase4.md`, and `PLAN/Conventions.md`.

Relevant prior work: closed issues #2180, #2193, #2209, #2216, and the
existing `status/hex-conway.scaffolding-reviewed` token from #1078.

This issue is intentionally narrow because `HexConway.done_through: 4`
unblocks `HexGfq` Phase 4 (and downstream `HexGfqMathlib` Phase 4 once
`HexGF2Mathlib.done_through` also reaches 4).

## Verification

- `lake build HexConway`
- `lake exe hexconway_bench list`
- `lake exe hexconway_bench verify`
- Scientific run for `Hex.ConwayBench.runLuebeckConwayPolynomialLookupChecksum`
- Fixed-registration runs for the seven `Tier1Irreducibility_*` and
  `ConwayPolySupported_2_1` benchmarks
- `lake exe hexconway_conformance` (or whatever HexConway conformance
  target the workflow names; do not invent a new entry point)
- `python3 scripts/check_phase4.py HexConway`
- `python3 scripts/status.py HexConway`
- `python3 scripts/status.py`
- `python3 scripts/check_dag.py`
- `git diff --check`
- No new `axiom`, `native_decide`, `TODO`, `FIXME`, or data-level placeholder.

## Out of scope

- Adding Tier 2 (full Conway verification) or Tier 3 (on-demand search)
  benchmarks. Those are separate Phase 4-or-later features per
  `SPEC/Libraries/hex-conway.md` and not gated on this bump.
- Adding new Tier 1 benchmark registrations unless verification proves one
  is missing for already-committed Tier 1 surface area.
- Weakening the `tier1LookupComplexity` declared complexity model.
- Editing `SPEC/`, top-level `PLAN.md`, or top-level `AGENTS.md`.
- Working on `HexGfq`, `HexGfqMathlib`, or any HexBerlekampZassenhaus
  human-oversight chain in this issue.
