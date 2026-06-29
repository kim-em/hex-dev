# LLL performance: checker-split experiment and improvement candidates

## Accomplished

- Read `reports/hex-lll-scaling.md`, `reports/hex-lll-performance.md`,
  `reports/hex-lll-harsh-cubic-crossover-diagnosis.md`, and the HexLLL /
  HexGramSchmidt implementation, looking for ways to improve the
  random-bounded constant and the harsh-cubic exponent.
- Built and ran a local diagnostic (`CheckerSplit.lean` at repo root,
  untracked; wiring instructions in its header) that splits the certified
  checker's cost into components on the exact bench fixtures. Headline
  numbers (local M-series Mac, native@180 = 3.97s vs carica 4.76s):
  - random-bounded n=180: `lllReducedInt B'` = 623ms, one
    `Matrix.mul` same-lattice matmul (20-bit U) = 116ms, packed
    single-point-evaluation equivalent = 45ms.
  - harsh-cubic n=55: `GramSchmidt.Int.data basis` = 223ms of the 228ms
    native total (98%); `lllReducedInt B'` = 235ms (the checker re-pays
    the full exact GSO — Gram-determinant bit sizes are lattice-invariant,
    so reducing first does not shrink them); packed eval 8.7ms vs 34ms
    matmul.
- Conclusion: one kernel — exact-integer GSO (`GramSchmidt.Int.data`) —
  dominates native harsh-cubic, the certified checker on both families,
  and (as `ofBasis` plus in-loop ν updates) most of native
  random-bounded. Candidate improvements reported to Kim in-session:
  1. Packed single-point evaluation (Kronecker-style) for
     `sameLatticeCert` (provable, ~2.5–4×on the matmul share).
  2. Fixed-precision interval/ball reducedness checker with exact
     fallback, replacing `lllReducedInt`'s exact GSO (drops the
     harsh-cubic checker exponent to ~n³ small-word ops; certified path
     then beats native everywhere on harsh-cubic).
  3. Request stronger (δ+ε, η−ε) from fplll than certified, so the ball
     checker has macroscopic margins (one-line dispatch change).
  4. Longer term: approximate-GSO-steered native loop (Schnorr–Euchner
     style) with exact integer row ops and self-certification via the
     ball checker, fallback to the proven native loop.

## Current frontier

Ideas handed to Kim for selection; no implementation started. The
experiment file `CheckerSplit.lean` (untracked) reproduces the splits;
the lakefile entry was reverted to keep the worktree clean.

## Next step

Kim to pick which candidates to pursue; likely first PR is the packed
same-lattice certificate (small, fully provable, immediate win), then
the ball/interval reducedness checker design.

## Blockers

None.
