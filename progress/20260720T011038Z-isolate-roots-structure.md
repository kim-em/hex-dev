# Stage 3c: IsolatedRealRoots structure, constructors, bridge macro

## Accomplished
- Added `HexRealRootsMathlib/IsolateRoots.lean` (API only; elaborator is 3d):
  - `Hex.IsolatedRealRoots` structure with all four SPEC fields
    (`intervals`, `unique_root`, `covers`, `ordered`).
  - `aeval_toPolynomial` (coefficient-sum form, reconciled with the existing
    `aeval_eq_eval_toPolyℝ` / `eval_toPolyℝ`) and `aeval_toPolynomial_ofCoeffs`
    (sum over the raw array length, so `size` reduces to a numeral for the
    bridge tactic).
  - `IsolatedRealRoots.of` (from `RealRootIsolations`, now including `ordered`).
  - `RealRootIsolation.count_one_of_cert` and the replay constructor
    `IsolatedRealRoots.ofCert` — every field a single `decide` against a
    reified chain via `SturmChainCert` / `sturmCount_eq_of_cert` /
    `rootCount_eq_of_cert` / `orderedAdjacent` / `ordered_of_adjacent`.
  - `IsolatedRealRoots.congrRoots` (ring-heterogeneous transport) and
    `IsolatedRealRoots.constant` (n = 0 for nonzero constants).
  - `isolate_roots_bridge` tactic.
- Added `toReal_eq_cast_toRat` to `Separation.lean` (plain-import bridge for
  `Dyadic.toReal`, since it is not `@[expose]`d).
- Added `HexRealRootsMathlib/IsolateRootsTests.lean` (plain import, no
  `import all`, no sorry): bridge tactic on ℝ/ℤ/ℚ/negative-leading shapes;
  `x⁴−2` via `of` and via `ofCert`; `(x−1)²(x−3)` via `ofCert` on the reified
  core + `congrRoots`; the `congrRoots (aevalIff_squareFreeCore …)` production
  transport; a constant via `constant`.
- SPEC touch-up: recorded `SturmChainCert`'s `chain.size ≤ p.size` fuel-bound
  conjunct in the replay paragraph.
- Measured production `ofCert` kernel cost on Wilkinson-6/8/10:
  23.9k / 53.9k / 110.2k heartbeats — cheaper than the prototype's surrogate
  table (29k / 66k / 138k), so the real `SturmChainCert` validity check costs
  less than the surrogate estimate.
- Full `lake build` green (9419 jobs).

## Environment note
This worktree's Mathlib olean cache was absent and the `cache` exe could not
build (broken `ld.lld` wrapper in the elan toolchain — dangling nix store
path). Repaired the wrapper to delegate to the working system `ld.lld` (backup
at `ld.lld.broken-backup`) and unpacked the cache with the prebuilt binary.

## Current frontier
The `isolate_roots` term elaborator itself (stage 3d) is not in this PR.

## Next step
Stage 3d: the `isolate_roots` / width term elaborator emitting `ofCert`.

## Blockers
None. The squarefree-core transport in a plain-import test cannot connect a
reified core literal to `squareFreeCore q` by `decide` (squareFreeCore is
outside the exposed replay closure); the test proves that bridge by factoring
and separately exercises `congrRoots (aevalIff_squareFreeCore …)` at the type
level. The elaborator will generate the literal↔`squareFreeCore` equality at
meta level.
