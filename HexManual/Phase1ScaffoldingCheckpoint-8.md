# Phase 1 Scaffolding Checkpoint 8

This checkpoint records the merge wave on `main` after summarize issue
`#273` and checkpoint 7. The wave spans the benchmarking-spec reset and
bootstrap reland through PR `#619`; the live frontier below is
cross-checked against repository state after PR `#619` merged on
`2026-04-28T08:58:55Z`.

## Newly merged on `main` since the seventh checkpoint

### Bootstrap reland and execution-rule changes

- PRs `#425`, `#426`, `#427`, `#428`, `#429`, and `#430` rewrote the Phase 4
  benchmark rules around `lean-bench`, briefly landed prototype harnesses,
  reverted them, then relanded the prototype under the new rules while also
  relaxing `check_dag.py` to allow transitive imports.
- PR `#433` re-bootstrapped the repo as the current Lean monorepo baseline:
  root modules for every library, `libraries.yml`, `scripts/status.py`,
  `scripts/check_dag.py`, CI workflow stubs, and the progress/status
  machinery all now stem from that reland.
- PRs `#424`, `#531`, `#536`, `#568`, `#574`, and `#580` tightened the worker
  contract around complexity claims, extern/runtime honesty, the `HexModArith`
  design choice, `lakefile.lean`-only project wiring, `UInt64.extGcd`
  delegation, and failure-mode naming.

### Root-library Phase 1 coverage and review progression

- PRs `#444`, `#472`, `#474`, `#538`, `#545`, `#569`, `#594`, `#597`,
  `#601`, and `#617` built out `HexArith` from wide arithmetic and
  Montgomery/Barrett surfaces to the repaired native `extGcd` path and the
  real GMP-backed `mpz_gcdext` bridge.
- PRs `#445`, `#464`, `#487`, `#507`, `#522`, and `#546` established the
  `HexPoly` dense representation, arithmetic/Euclidean layers, and CRT
  theorem surface, with the later fixes removing dishonest or over-broad
  scaffold bodies.
- PRs `#446`, `#463`, `#479`, `#485`, `#486`, `#506`, `#535`, `#547`, and
  `#552` moved `HexMatrix` from the core row/shape API through RREF/span/
  nullspace, Bareiss/determinant, Gram helpers, and the initial Phase 3
  conformance executable.
- PRs `#455`, `#562`, `#573`, and `#585` opened `HexModArith` with the
  `ZMod64` core, repaired bounds/default multiplication, and added the first
  power/inverse bridges into Mathlib's `ZMod`.
- PRs `#462`, `#542`, `#565`, and `#609` gave `HexGramSchmidt` executable
  basis/coefficient data, determinant-related structure, row-update APIs, and
  the remaining basis-span theorem surface needed by downstream `HexLLL`.
- Review PRs `#509`, `#512`, `#528`, `#550`, `#555`, and `#556` moved the
  library baseline forward administratively: `HexMatrix`, `HexPoly`,
  `HexPolyZ`, and `HexArith` are no longer waiting on Phase 1 completion
  bookkeeping, and `HexMatrix` is now far enough through the DAG to expose a
  ready Phase 4 benchmark stream.

### Newly opened downstream libraries

- PRs `#500`, `#502`, `#527`, `#572`, and `#610` opened
  `HexMatrixMathlib` with rank/span/nullspace, determinant, canonical-rank
  bridge surface, and the Phase 1 completion review that has already landed.
- PR `#501` opened `HexGramSchmidtMathlib`, and PR `#518` plus `#611` opened
  `HexPolyMathlib` with both the base polynomial equivalence and the initial
  Euclidean correspondence theorems.
- PRs `#517`, `#534`, `#600`, `#607`, and `#618` moved `HexGF2` from the
  packed `GF2Poly` core through carry-less multiplication, Euclidean APIs,
  and the first single-word `GF2n` surface.
- PRs `#576`, `#523`, `#566`, and `#615` opened `HexPolyZMathlib` with the
  bridge scaffold plus the public Mahler/Mignotte theorem surface, leaving
  proof completion as a separate follow-up.
- PRs `#557` and `#524` opened the `HexLLL` side of the matrix stack with
  lattice predicates, `LLLState`, and the next Gram-Schmidt theorem frontier.
- PRs `#579`, `#582`, and `#602` opened the current `HexPolyFp` execution
  path with Frobenius APIs, modular composition, and square-free
  decomposition, turning it into the main bottleneck for several blocked
  factorization libraries.
- PR `#588` opened the `HexHensel` bridge layer, while PRs `#606` and `#619`
  opened the current `HexGFqRing` quotient-core and quotient-operations
  implementation.

### Project-wide cleanup and coordination churn

- PRs `#598`, `#599`, `#600`, and `#603` removed remaining
  "scaffold"/placeholder-flavored docstrings from the main library surfaces.
- Human-oversight issue work on the `HexArith` extern path produced useful
  fixes, but the current open PR/issue set still contains repair debris:
  PRs `#577`, `#595`, and `#596` remain open, with `#595` and `#596`
  conflicting against `main`.

## Current frontier

- The repo baseline is no longer a pre-bootstrap design shell. The bootstrap
  reland is merged, the root-library wave is live, and the active frontier is
  now a mixed DAG of Phase 1 downstream scaffolding, Phase 2 reviews for the
  newly completed roots, and the first Phase 4 benchmark slice for
  `HexMatrix`.
- `HexPolyFp` is now the main execution-path chokepoint. Once its Phase 1
  surface fully lands and reviews cleanly, it unlocks direct progress for
  `HexBerlekamp`, `HexHensel`, and `HexGF2Mathlib`.
- `HexPolyMathlib` is the main Mathlib-side chokepoint. Its remaining
  Phase 1 review work gates `HexPolyZMathlib`, `HexHenselMathlib`, and
  `HexBerlekampMathlib`.
- `HexArith` itself is past Phase 1, but the native runtime path is not fully
  settled: issue `#616` remains open because plain `lake env lean` still does
  not auto-load the `HexArith` extern plugins reliably.

## Ready vs blocked state

`python3 scripts/status.py` currently reports these libraries as ready:

- `HexArith -> Phase 2`
- `HexPoly -> Phase 2`
- `HexMatrix -> Phase 4`
- `HexModArith -> Phase 1`
- `HexGramSchmidt -> Phase 2`
- `HexGF2 -> Phase 1`
- `HexPolyZ -> Phase 2`
- `HexLLL -> Phase 1`
- `HexPolyMathlib -> Phase 1`
- `HexMatrixMathlib -> Phase 1`
- `HexGramSchmidtMathlib -> Phase 1`

The remaining libraries are blocked, with the main dependency clusters as
follows:

- Waiting on `HexModArith.done_through >= 1`: `HexPolyFp`,
  `HexModArithMathlib`.
- Waiting on `HexPolyFp.done_through >= 1`: `HexGFqRing`, `HexHensel`,
  `HexGF2Mathlib`, and part of `HexBerlekamp`.
- Waiting on the finite-field chain after `HexGFqRing`: `HexGFqField`,
  `HexConway`, `HexGFq`, and `HexGFqMathlib`.
- Waiting on `HexBerlekamp` and `HexHensel`: `HexBerlekampZassenhaus`,
  `HexBerlekampMathlib`, `HexHenselMathlib`,
  `HexBerlekampZassenhausMathlib`.
- Waiting on `HexPolyMathlib.done_through >= 1`: `HexPolyZMathlib`,
  `HexHenselMathlib`, `HexBerlekampMathlib`.
- Waiting on `HexLLL.done_through >= 1`: `HexLLLMathlib`.

No library is fully done yet.

## Open work map

- Unclaimed feature work is concentrated in downstream Phase 1 libraries:
  `HexHenselMathlib` (`#481`), `HexBerlekamp` (`#482`), `HexGFqField`
  (`#483`), `HexGF2Mathlib` (`#484`), `HexHensel` (`#489`, `#492`),
  `HexLLL` (`#524`), `HexMatrix` benchmarking (`#564`), `HexGF2`
  quotient-wrapper follow-up (`#613`), and `HexPolyZMathlib` proof
  completion (`#614`).
- The key open review item is `#516`, which determines whether
  `HexPolyMathlib` can advance and unblock the next Mathlib wave.
- Open PRs with live impact are `#602` on `HexPolyFp` and the lingering
  `HexArith` repair/doc PRs `#577`, `#595`, and `#596`.

## Coordination risks to watch

- `HexPolyFp` now carries too much downstream weight for its open PRs to
  stall; if `#602` does not land cleanly and trigger the needed review/bump
  work, the Berlekamp/Hensel/GF2 branch stays artificially blocked.
- `HexMatrix` has newly opened Phase 4 work (`#564`), but the benchmark rules
  changed mid-wave; workers need to follow the `lean-bench`/`lakefile.lean`
  rules rather than the reverted prototype wiring.
- The `HexArith` extern situation is improved but not fully closed. The real
  GMP bridge is merged, yet loader/autoload behavior still needs cleanup and
  the repo still carries conflicting PRs from earlier repair attempts.
