# Phase 2/3/4/5 Checkpoint 19

This checkpoint records the merge wave on `main` after summarize issue
`#1535`. It covers the concentrated `HexGF2` multiplication associativity
stream, the `HexArith` Montgomery and primality proof closure, continued
`HexPolyFp` Yun decomposition work, the `HexGFqField` inverse frontier, the
new `HexGramSchmidt` decomposition surface, and the current dispatch queue
through PR `#1772`.

## Newly merged on `main` since checkpoint 18

### HexGF2 multiplication and CLMUL associativity

- PRs `#1649`, `#1650`, `#1653`, `#1654`, and `#1658` moved the packed
  multiplication proof from CLMUL word commutativity through coefficient-fold
  algebra, raw multiplication commutativity, and normalized raw-product
  transparency.
- PRs `#1662`, `#1664`, `#1665`, `#1669`, and `#1670` packaged the raw
  associativity expansion layer: word contribution expansion, triple-XOR
  reindexing, right-intermediate helpers, and source-triple expansion surfaces.
- PRs `#1693`, `#1715`, `#1716`, `#1719`, `#1721`, `#1728`, `#1729`, and
  `#1730` narrowed the CLMUL source-pair/source-triple coefficient proof.
  These PRs split the two-word associativity proof into explicit bit-fold,
  one-hot source coefficient, source-pair expansion, and coefficient-regrouping
  layers.
- PRs `#1737`, `#1738`, `#1739`, `#1740`, `#1741`, `#1742`, `#1743`,
  `#1744`, and `#1745` closed the fixed source-triple helper family: left-low,
  left-middle, left-high, right-low, right-middle, right-high, and fixed-triple
  active-slot reductions are now represented by named lemmas.
- Current `HexGF2` status: `scripts/status.py HexGF2` still reports Phase 5
  ready. The remaining `sorry` scan is concentrated in `HexGF2/Euclid.lean`,
  with separate proof placeholders in benchmark/conformance theorem surfaces.

### HexArith and HexModArith

- PR `#1671` proved the `ZMod64` inverse multiplication contract.
- PRs `#1674`, `#1676`, `#1679`, `#1680`, `#1682`, `#1684`, and `#1695`
  repaired and closed the Montgomery inverse setup path: initial Newton-step
  refinements, Nat-level Newton congruence, UInt64 inverse specs, base facts,
  `r2` context constant, and canonical residue bounds.
- PRs `#1696` and `#1698` proved the `ZMod64` semiring and Grind ring laws.
- PRs `#1700`, `#1702`, and `#1704` proved the Montgomery representation,
  multiplication, and `powMod` user-facing theorem surfaces.
- PRs `#1706`, `#1709`, `#1712`, and `#1713` completed the extended-GCD
  bridges and advanced the Nat prime frontier through local binomial expansion
  and the add-power modulo cancellation theorem.
- Current `HexArith` status: `scripts/status.py HexArith` remains Phase 5
  ready. The focused Montgomery and extended-GCD PR stream is closed; the
  visible remaining frontier is Nat prime proof work rather than the earlier
  Montgomery inverse repair surface.

### HexPolyFp Yun reconstruction

- PRs `#1686` and `#1691` packaged and refined the derivative-active Yun
  split surface.
- PR `#1751` added the Yun contribution step combiner.
- PR `#1753` partially rewired the successor theorem through the named private
  theorem `yunFactorsContribution_derivative_active_loop_invariant`.
- Current `HexPolyFp` status: issue `#1752` is unclaimed and actionable. Its
  dependency `#1747` is closed, so the next worker can focus directly on the
  derivative-active loop invariant using the step combiner, terminal case, and
  gcd/division reconstruction lemmas already in the file.

### HexGFqField inverse frontier

- PR `#1755` added the xgcd gcd helper surface for the inverse proof.
- PR `#1756` proved the xgcd gcd degree helper.
- PR `#1757` closed the normalized xgcd inverse proof.
- Current `HexGFqField` status: `scripts/status.py HexGFqField` still reports
  Phase 5 ready, but the normalized inverse proof chain represented by the
  recent issues is closed.

### HexMatrix and HexGramSchmidt

- PR `#1759` repaired the `HexMatrix` transform inverse surface.
- PRs `#1761`, `#1763`, `#1766`, `#1770`, `#1771`, and `#1772` opened the
  `HexGramSchmidt` Phase 5 proof stream: coefficient matrix shape facts,
  first-row basis facts, integer decomposition wiring, dot/subtraction helper
  lemmas, projection-preservation helpers, and a partial public decomposition
  route through the private `basisMatrix_reconstruction_invariant`.
- Current `HexGramSchmidt` status: the public rational and integer
  decomposition theorems are wired to the private reconstruction invariant,
  but that invariant requires a separate `basisRowsAux` orthogonality layer
  before the coefficient-prefix fold can be closed.

## Current queue frontier

- Claimed: `#1758` is this checkpoint.
- Unclaimed: `#1752` covers the remaining `HexPolyFp` Yun derivative-active
  loop invariant.
- Unclaimed: `#1774` covers the missing private `HexGramSchmidt`
  `basisRowsAux` orthogonality invariant.
- Blocked: `#1775` covers the `HexGramSchmidt` reconstruction fold and depends
  on `#1774`.
- Replan: `#1773` was decomposed into `#1774` and `#1775`.
- Open PR state: `coordination orient` reports no open PRs and no PRs needing
  repair.

No additional follow-up issue is needed from this checkpoint beyond the
already-created `HexGramSchmidt` split. The live gaps are represented by
`#1752`, `#1774`, and blocked successor `#1775`.

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

- Prove `#1752` to finish the named `HexPolyFp` Yun derivative-active loop
  invariant without changing executable square-free factorization behavior.
- Prove `#1774` before attempting `#1775`; the Gram-Schmidt reconstruction
  theorem depends on prefix orthogonality and the rational zero-norm projection
  case.
- Continue closing the remaining `HexGF2` Euclid proof placeholders now that
  the multiplication associativity helper stack is much more explicit.
- Continue `HexArith` Phase 5 with the Nat prime proof frontier; the recent
  Montgomery inverse, Montgomery multiplication, `powMod`, and extended-GCD
  fronts are no longer the active blockers.
