# Phase 2/3/4/5 Checkpoint 17

This checkpoint records the merge wave on `main` after summarize issue
`#1297`. It covers the determinant proof follow-through, the concentrated
`HexHensel` Phase 5 proof stream, targeted `HexPolyFp` and `HexModArith`
proof work, the new `HexBerlekamp` benchmark harness, and the current
Phase 5 frontier through PR `#1486`.

## Newly merged on `main` since checkpoint 16

### HexHensel proof stream

- PRs `#1415`, `#1417`, `#1424`, `#1427`, `#1429`, `#1430`, `#1433`,
  `#1436`, `#1437`, `#1440`, `#1444`, `#1446`, `#1449`, `#1451`, and
  `#1467` moved the linear Hensel surface from bridge and theorem-shape
  work through the `modP` additive and multiplicative lift bridges, the
  scaled product expansion, and the public product-congruence path.
- PRs `#1419`, `#1431`, `#1432`, `#1452`, `#1457`, `#1459`, `#1461`,
  `#1463`, `#1465`, `#1466`, `#1469`, `#1471`, `#1474`, `#1475`, `#1477`,
  and `#1478` closed the quadratic Hensel Bezout, factor-congruence, and
  monicity support chain. The work added reusable dense-polynomial algebra
  helpers, modular-square divmod reconstruction and support facts, and the
  final low-remainder monicity arguments.
- PRs `#1480`, `#1482`, `#1484`, and `#1486` completed the remaining
  `HexHensel/Linear.lean` wrapper stack: step monicity and degree
  preservation, `h` degree preservation, the loop invariant, and the public
  `henselLift_spec` / `henselLift_monic` wrappers.
- Current `HexHensel` status: `HexHensel/Linear.lean` and the current
  `HexHensel/Quadratic.lean` theorem surface have no remaining placeholders.
  The remaining Phase 5 placeholder is `multifactorLift_spec` in
  `HexHensel/Multifactor.lean`, tracked by replan issue `#1487`.

### HexMatrix determinant work

- PRs `#1413` and `#1421` proved the transpose-permutation support needed for
  determinant row-operation reasoning: permutation-vector preservation and
  transpose reindexing.
- PR `#1434` proved determinant duplicate-row cancellation in
  `HexMatrix/Determinant.lean`.
- Current `HexMatrix` status: determinant duplicate-row work is complete, but
  Phase 5 still has independent placeholders in `Bareiss`, `RowEchelon`, and
  `RREF`.

### HexPolyFp and HexModArith proof work

- PR `#1414` proved the Frobenius zero-exponent simplification in
  `HexPolyFp`.
- PR `#1425` proved the modular-composition correctness theorem covered by
  issue `#1418`, leaving the square-free decomposition correctness surface as
  the active `HexPolyFp` frontier.
- PR `#1442` completed `ZMod64.neg` normalization and `toNat_neg` in
  `HexModArith/Ring.lean`. The remaining `HexModArith` Phase 5 work is the
  larger `Lean.Grind` semiring/ring/commutative-ring proof surface plus
  unrelated arithmetic proof placeholders.

### HexBerlekamp benchmark work

- PR `#1439` added the `HexBerlekamp` Phase 4 benchmark harness with
  deterministic targets for Berlekamp matrix construction, Rabin
  irreducibility testing, split-step factorization, and distinct-degree
  factorization, plus the `hexberlekamp_bench` Lake executable.
- The harness uses the existing split-step factoring surface because the full
  public `berlekampFactor` path still waits on a `Lean.Grind.Field (ZMod64 5)`
  instance from the modular-arithmetic layer.

### Cross-library helper movement

- PR `#1465` exposed `DensePoly` algebra helpers from `HexPoly/Euclid.lean`
  for downstream Hensel proofs. These helpers are part of the proof
  infrastructure now available to subsequent Phase 5 workers.
- The Hensel wave also added local coefficient-fold, modular congruence, and
  support-bound lemmas that narrow future proof obligations rather than
  changing public executable algorithms.

## Current queue frontier

- Unclaimed: `#1488`, `#1489`, and `#1490` split the remaining
  `HexPolyFp/SquareFree.lean` public correctness surface into pairwise
  coprime factors, weighted-product reconstruction, and per-factor
  square-freeness.
- Claimed: `#1455` is this checkpoint.
- Replan: `#1420` is the superseded parent for the square-free decomposition
  cluster, and `#1487` tracks the remaining `HexHensel/Multifactor.lean`
  product-congruence theorem.
- Open PR state: `coordination orient` reports no open PRs and no PRs needing
  repair.

No additional follow-up issue was created during this checkpoint: the live
queue already covers the concrete `HexPolyFp` square-free split, and the
remaining `HexHensel` multifactor proof is already represented by `#1487`.

## Ready phase frontier

`python3 scripts/status.py` currently reports these ready dispatch targets:

- Phase 5: HexArith, HexPoly, HexMatrix, HexModArith, HexGramSchmidt, HexGF2,
  HexPolyZ, HexLLL, HexPolyFp, HexGFqRing, HexGFqField, and HexHensel.
- Phase 4: HexBerlekamp and HexMatrixMathlib.
- Phase 3: HexPolyMathlib, HexModArithMathlib, HexGramSchmidtMathlib, and
  HexLLLMathlib.
- Phase 2 reviews: HexBerlekampMathlib, HexHenselMathlib, HexGF2Mathlib, and
  HexGFqMathlib.
- Phase 1 scaffolding: HexBerlekampZassenhausMathlib.

The blocked status graph is now:

- HexConway Phase 4 waits on HexBerlekamp Phase 4.
- HexGFq Phase 4 waits on HexConway Phase 4.
- HexBerlekampZassenhaus Phase 4 waits on HexBerlekamp Phase 4.
- HexPolyZMathlib Phase 3 waits on HexPolyMathlib Phase 3.

## Follow-up focus

- Finish `HexHensel` Phase 5 by proving `multifactorLift_spec`; if it closes
  the last `HexHensel` placeholder, verify the Phase 5 exit criteria before
  bumping `libraries.yml`.
- Work the three `HexPolyFp/SquareFree.lean` issues independently. The
  weighted-product theorem should provide the reconstruction spine; the
  pairwise-coprime and per-factor square-free theorems should stay focused on
  Yun-factor invariants and list reversal.
- Continue `HexMatrix` Phase 5 outside the completed determinant duplicate-row
  path, especially Bareiss correctness and the row-echelon/RREF proof surface.
- Dispatch the next `HexBerlekamp` Phase 4 review step now that the benchmark
  harness exists, while separately tracking the modular-arithmetic field
  instance needed by full kernel-based factoring benchmarks.
