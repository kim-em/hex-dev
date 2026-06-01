# Phase 1 Scaffolding Checkpoint 9

This checkpoint records the merge wave on `main` after summarize issue
`#470` and checkpoint 8. The wave starts after PR `#619` and includes the
finite-field, modular-arithmetic, Mathlib bridge, review, and repair work
merged through PR `#810`.

## Newly merged on `main` since the eighth checkpoint

### Phase 2 review tokens and readiness bumps

- PRs `#648`, `#657`, `#671`, `#675`, `#683`, `#685`, `#702`, `#705`,
  `#709`, `#714`, `#717`, `#718`, `#770`, and `#780` moved a broad set of
  libraries through review bookkeeping: `HexModArithMathlib`,
  `HexGFqRing`, `HexPoly`, `HexPolyZ`, `HexPolyZMathlib`, `HexModArith`,
  `HexGFqField`, `HexGramSchmidtMathlib`, `HexArith`, `HexPolyFp`,
  `HexMatrixMathlib`, and `HexPolyMathlib`.
- Those review completions are now reflected in `libraries.yml`: the root
  arithmetic/poly stack and several Mathlib bridge layers are at or beyond
  Phase 2, while `HexMatrix` has advanced to Phase 3 and is ready for the
  Phase 4 benchmark stream.
- `HexGFqRing`, `HexGFqField`, `HexBerlekamp`, `HexHensel`, and
  `HexConway` are no longer merely blocked future libraries. They now have
  Phase 1 surfaces in place and sit on the active Phase 2 review frontier.

### Finite-field and quotient-ring pipeline

- PRs `#664`, `#678`, `#701`, `#760`, `#764`, `#773`, `#783`, and `#785`
  expanded the finite-field stack: `HexGF2` gained field-operation wrappers,
  `HexGF2Mathlib` gained field bridges, `HexGFqField` gained quotient-backed
  ring-law transport and inverse helper surface, `HexGFqRing` gained
  reduction idempotence, and `HexConway` gained committed-entry wrappers.
- PRs `#784`, `#808`, and `#810` added proof-support pieces below the GF2
  and quotient-ring follow-up streams: normalization bounds, the generic
  dense-polynomial remainder-degree surface, and GF2 polynomial zero helpers.
- The finite-field pipeline is now much more concrete but still not fully
  certified. The current blockers are proof-level follow-ups around
  `HexGF2` Euclidean semantics, `HexGFqRing` quotient ring instances, and
  `HexGFqField` field-shell axioms.

### Factoring, Hensel, LLL, and conformance surface

- PRs `#645`, `#667`, `#704`, and `#751` advanced the Hensel path with
  linear and quadratic lift surfaces plus iterative wrapper cleanup.
- PRs `#666`, `#703`, and `#768` opened the Berlekamp and Conway side of the
  factoring pipeline with irreducibility tests, a kernel split step, and the
  initial Conway Tier 1 lookup.
- PRs `#668` and `#752` extended the LLL stack with executable
  size-reduction/swap scaffolding and the first `HexLLLMathlib` lattice bridge.
- PRs `#748`, `#757`, and `#774` added the current `HexPoly`, `HexArith`,
  and modular-arithmetic conformance slices, which is why `scripts/status.py`
  now advertises Phase 3 conformance work for `HexArith` and `HexPoly`.

### Runtime, algorithmic, and specification repairs

- PRs `#651`, `#653`, `#655`, `#684`, `#696`, `#736`, `#747`, `#749`,
  `#750`, `#753`, `#756`, `#761`, `#804`, and `#809` tightened the executable
  hot paths: Barrett and Montgomery helpers, native `UInt64` arithmetic,
  `UInt64.extGcd` routing through the `Int` runtime path, square-and-multiply
  power implementations, faster `GFqRing` exponentiation, optimized Bareiss
  pivoting, and incremental `gramDetVec` determinant extraction.
- PRs `#734`, `#737`, `#738`, `#739`, `#740`, and `#741` removed or repaired
  slow or duplicate helper code in `HexPolyZ`, `HexMatrix`, `HexPolyFp`, and
  adjacent arithmetic support.
- PRs `#713`, `#715`, `#716`, `#719`, `#735`, `#788`, `#793`, `#800`,
  `#801`, `#802`, and `#803` updated SPEC/PLAN guidance around cardinality
  ownership, Montgomery and Mignotte contracts, complexity and alias review
  questions, canonical fast defaults, planner/worker SPEC discipline, and
  the proofs-only status of `Hex.pureIntExtGcd`.

## Current frontier

- `python3 scripts/status.py` now reports a repo with several active Phase 2
  and Phase 3 frontiers rather than a simple Phase 1 scaffolding queue.
  `HexArith` and `HexPoly` are ready for Phase 3 conformance; `HexMatrix`
  is ready for Phase 4 benchmarking; `HexGramSchmidt`, `HexGF2`, `HexLLL`,
  `HexGFqRing`, `HexGFqField`, `HexBerlekamp`, `HexHensel`, and `HexConway`
  are ready for Phase 2 review.
- The Mathlib bridge side has also moved forward. `HexMatrixMathlib` is ready
  for Phase 3, while `HexLLLMathlib` is ready for Phase 2 review and still
  has a feature follow-up for the Mathlib-norm restatement of the short-vector
  guarantee.
- The finite-field quotient pipeline is the main coordination frontier.
  `HexGFq` and `HexBerlekampZassenhaus` remain Phase 1-ready-but-unstarted
  only after their executable prerequisites clear, and their Mathlib mirrors
  stay blocked behind those executable libraries.

## Ready vs blocked state

`python3 scripts/status.py` currently reports these libraries as ready:

- `HexArith -> Phase 3`
- `HexPoly -> Phase 3`
- `HexMatrix -> Phase 4`
- `HexGramSchmidt -> Phase 2`
- `HexGF2 -> Phase 2`
- `HexLLL -> Phase 2`
- `HexGFqRing -> Phase 2`
- `HexGFqField -> Phase 2`
- `HexBerlekamp -> Phase 2`
- `HexHensel -> Phase 2`
- `HexConway -> Phase 2`
- `HexGFq -> Phase 1`
- `HexBerlekampZassenhaus -> Phase 1`
- `HexMatrixMathlib -> Phase 3`
- `HexLLLMathlib -> Phase 2`
- `HexBerlekampMathlib -> Phase 1`
- `HexHenselMathlib -> Phase 1`
- `HexGF2Mathlib -> Phase 1`

The remaining libraries are blocked:

- `HexModArith -> Phase 3`, waiting on `HexArith.done_through >= 3`.
- `HexPolyZ -> Phase 3`, waiting on `HexPoly.done_through >= 3`.
- `HexPolyFp -> Phase 3`, waiting on `HexPoly.done_through >= 3` and
  `HexModArith.done_through >= 3`.
- `HexPolyMathlib -> Phase 3`, waiting on `HexPoly.done_through >= 3`.
- `HexModArithMathlib -> Phase 3`, waiting on `HexModArith.done_through >= 3`.
- `HexGramSchmidtMathlib -> Phase 3`, waiting on
  `HexGramSchmidt.done_through >= 3`.
- `HexPolyZMathlib -> Phase 3`, waiting on `HexPolyZ.done_through >= 3` and
  `HexPolyMathlib.done_through >= 3`.
- `HexGFqMathlib -> Phase 1`, waiting on `HexGFq.done_through >= 1`.
- `HexBerlekampZassenhausMathlib -> Phase 1`, waiting on
  `HexBerlekampZassenhaus.done_through >= 1`.

No library is fully done yet.

## Open work map

- Unclaimed review work is still present for `HexGF2` (`#672`) and
  `HexGFqRing` (`#673`), but both are review-certification issues whose
  bodies explicitly wait for repair streams to land.
- Unclaimed feature work is concentrated around proof and smoke-test support:
  `HexLLLMathlib` short-vector norm restatement (`#720`), the
  `HexGFqRing` representative degree wrapper (`#787`), single-word and
  packed-quotient `HexGF2` smoke coverage (`#789`, `#790`),
  quotient-constant helper lemmas for characteristic transport (`#792`), and
  finite packed-representative support for `HexGF2Mathlib` (`#797`).
- Claimed issue work is currently focused on the `HexPoly`/`HexGFqRing`
  reduction-congruence helper (`#798`), the `HexGFqField` inverse follow-up
  (`#795`), and this checkpoint issue (`#643`).
- Blocked issue work is clustered around dependent proof streams:
  `HexGF2` Euclid division and gcd/xgcd (`#806`, `#807`), the
  `HexGFqField` zero/zpow and characteristic-p follow-ups (`#794`, `#791`),
  the `HexGFqRing` ring-instance follow-up (`#776`), and the dependent
  `HexGF2` field-wrapper repair (`#772`).
- There are currently no open PRs and no PRs needing repair according to
  `coordination orient`.

## Coordination risks to watch

- The active finite-field proof streams are now the main source of critical
  path depth. In particular, `#792` blocks `#791`, `#781`/`#782` block
  `#776`, and `#806` blocks `#807`; workers should prefer the lowest
  unblocked support issue in each chain over downstream certification passes.
- Review issues `#672` and `#673` remain useful sentinels but should not be
  treated as ordinary ready review work until their prerequisite repair issues
  are actually closed on `main`.
- `HexArith` and `HexPoly` have both advanced to Phase 3, so future planning
  needs to balance proof-repair pressure with conformance-test coverage.
- No open PRs means the queue is not presently blocked on CI repair, but it
  also means claimed issues without PRs should be watched closely so useful
  partial progress does not remain invisible.
