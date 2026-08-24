# hex-sparse-poly: Phase 2 review fixes and Phase 3 conformance

## Accomplished

- An independent agent session performed the Phase-2 skeptical review
  (verdict pass-with-gaps); all four gaps are fixed here: `pow_zero` /
  `pow_succ` (the complete recurrence for the binary powering),
  KernelTests probes for the rest of the SPEC's `decide` closure
  (`add`, `mul`, `ofDense`), and the vacuous `foldl_max_le` hypothesis
  removed. The transported-laws CommRing placement note is recorded for
  the Phase-4 SPEC write-back. Token:
  `status/hex-sparse-poly.scaffolding-reviewed`.
- `mul`'s kernel-facing specification now routes the pairwise products
  through the term `List`s: `Array.flatMap` stalls kernel reduction and
  the SPEC requires `mul` in the `decide` closure. Value unchanged.
- `DecidableEq (ZMod64 p)` moved from `HexPolyFp/Field.lean` to
  `HexModArith/Residue.lean` where it belongs, which is what lets the
  sparse conformance suite pin only hex-mod-arith as the SPEC states.
- Phase 3: `conformance/HexSparsePoly/Conformance.lean` (the SPEC's
  invariant, round-trip-necessity, and cross-library differential cases
  plus per-operation typical/edge/adversarial coverage — all green),
  the shared `HexSparsePolyFixtures`, the emit driver + committed
  120-record JSONL snapshot, the `sparsepoly` fixture schema in
  `Hex/Conformance/Emit.lean` and `scripts/oracle/common.py`, the
  SymPy sparse-ring oracle `scripts/oracle/sparsepoly_sympy.py`
  (51/51 checks green locally under nix-shell sympy), and the ORACLES
  tuple in `scripts/ci/run_oracles.sh`.
- `done_through: 3`.

## Current frontier

Phases 1–3 complete pending CI. Eight theorem-level sorries remain
(compose agreement pack, `coeff_substScale`, two `divExactMonic?`
iffs).

## Next step

Phase 4: `bench/HexSparsePoly/Bench.lean` with the six SPEC families,
the three `mul` candidate implementations and the `@[csimp]` twin
selection, profiles, and the headline report.

## Blockers

None.
