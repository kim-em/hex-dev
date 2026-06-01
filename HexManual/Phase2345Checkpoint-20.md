# Phase 2/3/4/5 Checkpoint 20

This checkpoint records the merge wave on `main` after summarize issue
`#1758`. It covers the HexHensel/HexLLL/HexBerlekampZassenhaus rollback and
Phase 1 re-scaffolding sequence, HexPolyZ rational helper closure, HexPolyFp
PrimeModulus division-law plumbing, and the current dispatch queue through PR
`#1862`.

## Newly merged on `main` since checkpoint 19

### HexPolyFp modular division and remainder laws

- PR `#1802` proved the first modular reduction laws for `HexPolyFp`.
- PR `#1820` split the canonical remainder uniqueness proof into a smaller
  core, leaving the hard uniqueness and edge-case obligations isolated.
- PR `#1849` threaded `[ZMod64.PrimeModulus p]` through the `HexPolyFp`
  `DivModLaws` instance and downstream consumers. This changed the proof
  frontier from missing algebraic assumptions to missing array-division
  invariants.
- Current `HexPolyFp` status: the live division-law chain is now represented
  by open PR `#1860` for `subtractScaledShift` leading-term cancellation,
  blocked successor `#1853` for the `divModArrayAux` remainder-degree
  invariant, and replan issue `#1819` for canonical remainder uniqueness.

### HexPolyZ rational reconstruction and square-free reassembly

- PRs `#1808`, `#1811`, `#1816`, `#1817`, `#1827`, and `#1847` built the
  rational bridge surface around `toRatPoly`, denominator clearing, primitive
  part scaling, and rational scale products.
- PR `#1824` closed the rational gcd/division reconstruction helper needed by
  primitive square-free reassembly.
- PR `#1825` then closed the top-level
  `ZPoly.primitiveSquareFreeDecomposition_reassembly_over_rat` proof.
- Issue `#1815` closed the `ratPolyPrimitivePart_rational_associate` proof
  surface after the checkpoint issue was filed, so the earlier unclaimed
  HexPolyZ helper queue is no longer live.
- Current `HexPolyZ` status: `scripts/status.py` still reports Phase 5 ready,
  but the recent rational primitive-part and square-free reassembly chain is
  closed.

### HexHensel, HexLLL, and HexBerlekampZassenhaus Phase 1 reset

- PRs `#1828`, `#1829`, `#1830`, and `#1831` updated the SPEC and dependency
  graph to require quadratic multifactor Hensel lifting, LLL-based
  recombination, and a top-level `HexLLL` entry point as Phase 1 deliverables.
- PR `#1832` rolled `HexHensel`, `HexLLL`, and `HexBerlekampZassenhaus` back
  to Phase 0 so those executable Phase 1 requirements could be represented
  honestly.
- PR `#1840` added the top-level `HexLLL` API surface and short-vector
  recovery path.
- PR `#1841` scaffolded the quadratic multifactor Hensel lift implementation,
  and PR `#1842` wired `HexBerlekampZassenhaus.henselLiftData` through that
  quadratic lifter.
- PR `#1846` added conformance coverage for the quadratic multifactor lift and
  exposed the linear multifactor Bezout-normalization bug now represented by
  issue `#1845`.
- PR `#1848` added the LLL recombination path in
  `HexBerlekampZassenhaus.recombine`, preserving the exhaustive search as a
  fallback/oracle.
- Current status: `HexHensel` and `HexLLL` are ready for Phase 1;
  `HexBerlekampZassenhaus` is blocked on both reaching Phase 1. The active
  `HexLLL` work is claimed in issue `#1859`, which replaces the remaining
  `lllAux` placeholder with the integer LLL outer loop. The active BZ
  conformance PR is `#1862`.

### HexGramSchmidt reconstruction

- Open PR `#1861` carries the `basisRowsAux` reconstruction index bridge for
  issue `#1797`.
- Current `HexGramSchmidt` status: the reconstruction bridge is no longer an
  unclaimed queue item, but it remains a high-signal risk until PR `#1861`
  lands because the public basis decomposition route still depends on that
  private bridge.

## Current queue frontier

- Claimed: `#1850` is this checkpoint.
- Claimed: `#1859` implements the `HexLLL.lllAux` integer outer loop.
- Blocked: `#1853` finishes the `HexPolyFp` remainder-degree proof after
  `#1852` lands.
- Replan: `#1819` covers the remaining `HexPolyFp` canonical remainder
  uniqueness helpers after the division-invariant chain.
- With open PRs: `#1852` is PR `#1860`, `#1839` is PR `#1862`, and `#1797`
  is PR `#1861`.
- Open PR state: `coordination orient` reports PR `#1860` as needing repair
  because CI is failing. PRs `#1861` and `#1862` are open and not currently
  repair candidates in the coordination output.

There are no unclaimed worker issues in the live queue at this checkpoint.
Planner headroom should wait for the current claimed, blocked, and open-PR
frontier to settle before adding broad new Phase 5 work.

## Ready phase frontier

`python3 scripts/status.py` currently reports these ready dispatch targets:

- Phase 5: HexArith, HexPoly, HexMatrix, HexModArith, HexGramSchmidt, HexGF2,
  HexPolyZ, HexPolyFp, HexGFqRing, and HexGFqField.
- Phase 4: HexBerlekamp, HexPolyMathlib, HexMatrixMathlib,
  HexModArithMathlib, HexGramSchmidtMathlib, and HexGF2Mathlib.
- Phase 3: HexPolyZMathlib and HexBerlekampMathlib.
- Phase 1 scaffolding: HexLLL and HexHensel.

The blocked status graph is now:

- HexConway Phase 4 waits on HexBerlekamp Phase 4.
- HexGFq Phase 4 waits on HexConway Phase 4.
- HexBerlekampZassenhaus Phase 1 waits on HexHensel Phase 1 and HexLLL
  Phase 1.
- HexLLLMathlib Phase 1 waits on HexLLL Phase 1.
- HexHenselMathlib Phase 1 waits on HexHensel Phase 1.
- HexGFqMathlib Phase 4 waits on HexGFq Phase 4 and HexGF2Mathlib Phase 4.
- HexBerlekampZassenhausMathlib Phase 1 waits on HexBerlekampZassenhaus
  Phase 1.

## Follow-up focus

- Repair or supersede PR `#1860`; the `HexPolyFp` division-law proof chain
  cannot advance to `#1853` or back to `#1819` until the leading-term
  cancellation/frame lemma surface is stable.
- Land the active `HexLLL.lllAux` implementation in `#1859`, because
  `HexBerlekampZassenhaus` Phase 1 and `HexLLLMathlib` are blocked behind
  `HexLLL.done_through >= 1`.
- Land or repair PR `#1861`; the GramSchmidt reconstruction bridge remains
  the main public decomposition risk for that library.
- Track the HexHensel Bezout-normalization bug from `#1845`; it was the
  highest-signal correctness issue found during this window, even though the
  issue now has a PR path.
- Keep BZ scale conformance (`#1839` / PR `#1862`) close to the LLL
  recombination work so executable recombination regressions are caught before
  downstream mathlib wrappers depend on it.
