# Issue #8500: remove the approximation-steered LLL reducer

## Accomplished

Ripped out the approximation-steered reducer entirely. The public `lll` now
keeps exactly two paths: the certified external-candidate dispatch (provider →
`certCheck`) and the exact `lllNative`. The native fallback that used to call
`lllSteered` calls `lllNative` directly.

Code:
- Deleted `HexLLL/Steered.lean` (whole module: `SteeredState`, `steeredReduce*`,
  `lllSteered`, `steerWins`/`steerDimThreshold`, `SteeredTally`/tally IO, and all
  `*_memLattice_iff` lemmas).
- `HexLLL.lean`, `HexLLL/Dispatch.lean`: dropped `import HexLLL.Steered`;
  repointed the `lll` `none` branch and both proof-free unchecked entrypoints
  from `lllSteered` to `lllNative`; rewrote the "steered → native" docstrings.
- `HexLLLMathlib/Reducer.lean`: deleted `lllSteered_memLattice_iff` /
  `lllSteered_isLLLReduced` / `lllSteered_independent`; the `lll_*` `none`
  branches now go through `lllNative` directly (`isLLLReduced.mono_η` lifts
  `η = 1/2` to `11/20` exactly as the old fallback arm did).
- `HexBerlekampZassenhaus/Basic.lean:5110`: repointed the one cross-library
  coupling (`bhksProjectedRowsTrace_reducedMatrix_eq`) to `lllNative`.
- `bench/HexLLLBench/{Targets,Inputs}.lean`: removed `runSteeredFallbackTally`
  and its registration, and the `firstLovaszCheckForcesSwap` steering guard;
  neutralized steered doc comments.

Docs (removed the steered narrative, kept provider + checker + exact; narrowed
the `11/20`/`121/400` justification from three reducers to two, attributing the
`11/20` loosening solely to the external provider): `HexLLL/README.md`,
`HexLLL/SPEC/hex-lll.md`, `HexLLL/Provider.lean`, `HexManual/Chapters/HexLLL.lean`,
`reports/hex-lll-performance.md`.

## Verification

`lake build` green with zero warnings in touched files across HexLLL,
HexLLLMathlib, HexBerlekampZassenhaus(Mathlib), HexLLLBench, HexConformance,
hexlll_emit_fixtures, HexManual. No `sorry`/`axiom` introduced.

No pinned concrete outputs change: conformance `EmitFixtures` already computes
via `lllNative` directly (max dim 10); bench golden hashes are *computed* at
elaboration from the now-native reducer (self-consistent); the only frozen
literal hashes are on external `runFpLLL*` targets. The `runNative*` targets
shared the same computed hash as the old steered default, confirming steered and
native produced identical first-vector norms on the well-conditioned families —
so the contract is invariant and the concrete output is unchanged here too.

## Current frontier

Implementation complete and built. Next: `/second-opinion`, then PR.

## Blockers

None. The comparator SVG figures and plot script live on
`feat/hexlll-perf-restore-extend` and must drop the "Lean steered" series there;
noted in the performance report. Those figures don't exist on this branch.
