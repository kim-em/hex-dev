# Phase 2/3/4/5 Checkpoint 18

This checkpoint records the merge wave on `main` after summarize issue
`#1455`. It covers the concentrated `HexPolyFp` square-free proof stream,
the `HexHensel` multifactor closure, modular-arithmetic and Montgomery
follow-through, mathlib bridge conformance and benchmark movement, and the
current Phase 5 frontier through PR `#1638`.

## Newly merged on `main` since checkpoint 17

### HexPolyFp square-free proof stream

- PRs `#1492`, `#1505`, `#1506`, `#1508`, `#1511`, `#1513`, `#1515`,
  `#1516`, `#1518`, `#1519`, `#1522`, `#1525`, `#1529`, `#1530`,
  `#1531`, `#1532`, `#1536`, and `#1539` moved the square-free
  reconstruction surface from list/product helpers through derivative-zero
  support, local exponent composition, `pthRoot` scaffolding, and public
  weighted-product wiring.
- PRs `#1540`, `#1542`, `#1546`, `#1547`, `#1552`, `#1553`, `#1559`,
  `#1566`, `#1571`, `#1572`, `#1575`, `#1577`, `#1580`, `#1581`,
  `#1582`, `#1583`, `#1586`, `#1587`, and `#1589` closed most of the
  Frobenius and derivative-zero reconstruction chain. The work established
  coefficient-fold decomposition, prime-power sum helpers, finite expansion
  boundaries, `powLinear` coefficient laws, `pthRoot` Frobenius
  reconstruction, and normalized-monic reachability.
- PRs `#1595`, `#1596`, `#1597`, `#1598`, `#1604`, `#1615`, `#1624`,
  `#1628`, and `#1629` narrowed the remaining Yun contribution work. The
  current tree has explicit Yun terminal, step, descent, and loop-state
  theorem surfaces, plus local power algebra and step-preservation lemmas.
- Current `HexPolyFp` status: `HexPolyFp/SquareFree.lean` remains the active
  Phase 5 hotspot. The live reconstruction frontier is now the replanned
  issue `#1627`: the old arbitrary-positive-multiplicity initial-state
  invariant is not the right theorem surface, and the next worker should split
  the underlying Yun gcd/division and repeated-root algebra into smaller
  lemmas before closing the reconstruction wrapper.

### HexHensel and Hensel mathlib movement

- PRs `#1494` and `#1496` repaired the multifactor theorem contract and
  proved the recursive product specification in `HexHensel/Multifactor.lean`.
  Together with the previous linear/quadratic work, this leaves no represented
  `HexHensel` issue in the live queue, though `scripts/status.py` still keeps
  `HexHensel` in Phase 5 until the library-wide placeholder count is zero.
- PR `#1599` added the quadratic Hensel mathlib-facing theorem surface. The
  proof bodies remain for later bridge work.
- `HexHenselMathlib` is now ready for Phase 3 conformance testing according
  to `scripts/status.py`.

### HexArith and HexModArith

- PR `#1498` proved the Nat-level Montgomery REDC lemmas.
- PRs `#1632`, `#1636`, and `#1638` completed the Barrett UInt64 reduction
  bridge, proved the public `BarrettCtx.mulMod` theorems, and proved the
  Montgomery REDC UInt64 bridge.
- Current `HexArith` status: the next Montgomery dependency is the inverse
  layer. Replan issue `#1639` records that the existing Nat-level
  `newton_step` statement is stale because it uses truncated Nat subtraction
  where the executable step uses wrapping `UInt64` subtraction.
- PR `#1510` gated `ZMod64` division laws on prime modulus, keeping the
  field-style laws out of composite-modulus contexts.

### Mathlib bridge conformance and benchmarks

- PRs `#1610` and `#1618` advanced `HexGF2Mathlib` through Phase 3
  conformance and added Phase 4 bridge-conversion benchmarks.
- PRs `#1613` and `#1621` advanced `HexPolyMathlib` through Phase 3
  conformance and added bridge benchmarks.
- PR `#1573` advanced `HexModArithMathlib` through Phase 3 conformance.
- PR `#1616` advanced `HexGramSchmidtMathlib` through Phase 3 conformance.
- PR `#1630` added `HexGFqMathlib` Phase 3 conformance checks, while
  PRs `#1609`, `#1602`, `#1591`, `#1558`, `#1560`, and `#1565` handled
  review and transport-surface movement for the GFq/GF2/Hensel/Berlekamp
  mathlib bridge libraries.
- PR `#1634` added `HexMatrixMathlib` bridge benchmarks.

### Gfq bridge surface

- PR `#1611` added the `HexGFqMathlib` GFq-to-`GaloisField` equivalence
  surface. This gives later proof and conformance workers a named bridge
  target, while the `HexGFqMathlib` Phase 4 status remains blocked on
  `HexGFq` and `HexGF2Mathlib` readiness.

## Current queue frontier

- Claimed: `#1535` is this checkpoint.
- Replan: `#1627` covers the remaining `HexPolyFp` Yun reconstruction
  invariant, but should be decomposed into smaller algebra lemmas before
  another worker attempts the wrapper theorem.
- Replan: `#1639` covers Montgomery inverse specs, but the helper theorem
  surface needs to be repaired to wrapping `UInt64` arithmetic before the
  public inverse specs can be proved.
- Open PR state: `coordination orient` reports no open PRs and no PRs needing
  repair.

No additional follow-up issue was created during this checkpoint. The concrete
gaps are already represented by replan issues `#1627` and `#1639`, and the
next planner should narrow those rather than duplicate them.

## Ready phase frontier

`python3 scripts/status.py` currently reports these ready dispatch targets:

- Phase 5: HexArith, HexPoly, HexMatrix, HexModArith, HexGramSchmidt, HexGF2,
  HexPolyZ, HexLLL, HexPolyFp, HexGFqRing, HexGFqField, and HexHensel.
- Phase 4: HexBerlekamp, HexPolyMathlib, HexMatrixMathlib,
  HexModArithMathlib, HexGramSchmidtMathlib, and HexGF2Mathlib.
- Phase 3: HexPolyZMathlib, HexLLLMathlib, HexBerlekampMathlib, and
  HexHenselMathlib.
- Phase 1 scaffolding: HexBerlekampZassenhausMathlib.

The blocked status graph is now:

- HexConway Phase 4 waits on HexBerlekamp Phase 4.
- HexGFq Phase 4 waits on HexConway Phase 4.
- HexBerlekampZassenhaus Phase 4 waits on HexBerlekamp Phase 4.
- HexGFqMathlib Phase 4 waits on HexGFq Phase 4 and HexGF2Mathlib Phase 4.

## Follow-up focus

- Replan `#1639` around a true wrapping-arithmetic Newton statement, then
  prove `montPosInv_spec` and `montInv_spec` without changing the executable
  Montgomery inverse definitions.
- Replan `#1627` into Yun split algebra lemmas. The next useful cuts are the
  gcd/division reconstruction facts needed by the contribution target and the
  repeated `p`-th-root descent connection used by
  `squareFreeAuxRevContribution_correct_pow_of_nonzero`.
- Continue the mathlib bridge Phase 3/4 work now exposed by
  `scripts/status.py`, especially `HexHenselMathlib` conformance and the
  Phase 4 benchmark targets for the newly advanced bridge libraries.
