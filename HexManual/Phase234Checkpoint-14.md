# Phase 2/3/4 Checkpoint 14

This checkpoint records the merge wave on `main` after summarize issue
`#987`. It covers the Phase 4 completion work, downstream conformance
updates, GF2 monomial-proof decomposition, benchmark repairs, and factoring
surface expansion merged through PR `#1077`.

## Newly merged on `main` since checkpoint 13

### Phase 4 completions and benchmark repair

- PRs `#1008`, `#1010`, `#1011`, and `#1012` closed the remaining HexPoly
  Phase 4 benchmark findings for primitive part, eval, and derivative
  scaling. PR `#1017` then reran the full HexPoly Phase 4 review, verified
  all 15 registered benchmark surfaces, and advanced `HexPoly.done_through`
  to `4`, unblocking HexPolyZ Phase 4.
- PRs `#1021`, `#1033`, `#1044`, `#1059`, and `#1068` built and stabilized
  the HexModArith Phase 4 benchmark path. The final residual non-pow
  verdict repairs in `#1068` advanced `HexModArith.done_through` to `4`,
  moving HexModArith to the Phase 5 frontier and unblocking HexPolyFp Phase
  4.
- PRs `#1039`, `#1041`, and `#1076` added HexPolyZ benchmark infrastructure
  and fixed the binomial and Mignotte-bound fixture models. HexPolyZ remains
  in Phase 4 until a full review verifies every registration and applies the
  phase bump.
- PRs `#1031` and `#1042` added and tuned HexGramSchmidt update-helper
  benchmarks. HexGramSchmidt remains in Phase 4, but the update-helper
  registrations now have usable scientific schedules.

### Conformance and downstream readiness

- PR `#1009` completed the HexPolyFp square-free conformance slice, and
  PR `#1028` added HexGFqRing Phase 3 conformance. PR `#1049` then added
  HexGFqField Phase 3 core conformance, moving HexGFqField to the Phase 4
  dependency frontier behind HexGFqRing Phase 4.
- PRs `#1057` and `#1060` proved the Nat-level Barrett quotient bounds and
  reduction correctness lemmas in HexArith. HexArith was already through
  Phase 4 and remains ready for Phase 5 proof work.

### GF2 monomial proof chain

- PRs `#1020`, `#1029`, `#1048`, `#1058`, `#1064`, and `#1070` built the
  private proof surface below right multiplication by a monomial: xor-CLMUL
  coefficient helpers, zero monomial-fold helpers, active one-hot update
  helpers, fixed-row active lemmas, low-bit CLMUL facts, and fixed-row
  no-effect lemmas.
- Parent issue `#1062` was then decomposed again into `#1072`, `#1073`, and
  `#1074`: active-row raw coefficients first, outer no-effect coefficients
  second, then the public theorem `q * monomial k = q.mulXk k`. The Euclid
  bridge chain remains blocked behind that public theorem through `#1001`,
  `#977`, `#972`, `#807`, `#772`, and `#672`.

### Factoring and Hensel surface

- PR `#1056` reviewed HexBerlekamp Phase 2 and found missing downstream
  factoring surface. PRs `#1065`, `#1066`, and `#1071` filled the
  irreducibility certificate/checker, full Berlekamp factor driver, and
  distinct-degree factorization API. HexBerlekamp is now ready for a fresh
  Phase 2 review pass.
- PR `#1077` recorded the HexHensel Phase 2 review outcome. The review found
  a missing multifactor lift API and left `HexHensel.done_through` unchanged.
  Follow-up issue `#1075` now covers the ordered product helper, multifactor
  lift function, and product-preservation theorem surface needed by the
  Berlekamp-Zassenhaus pipeline.

## Current queue frontier

- Unclaimed: `#1072` for the next GF2 right-monomial active-row proof slice
  and `#1075` for the HexHensel multifactor lift API.
- Claimed: `#1067` is this checkpoint.
- Replan: `#1062` is now a decomposed right-monomial parent pointing to
  `#1072`, `#1073`, and `#1074`.
- Blocked GF2 chain: `#1073` waits on `#1072`, `#1074` waits on `#1073`,
  and the Euclid/field-wrapper review chain remains `#1001` -> `#977` ->
  `#972` -> `#807` -> `#772` -> `#672`. Issue `#1001` still needs planner
  cleanup after `#1062` was decomposed.
- Open PR state: `coordination orient` reports no open PRs and no PRs
  needing repair at this checkpoint.

## Ready phase frontier

`python3 scripts/status.py` currently reports these ready dispatch targets:

- Phase 5: HexArith, HexPoly, HexMatrix, HexModArith.
- Phase 4: HexGramSchmidt, HexPolyZ, HexPolyFp, HexMatrixMathlib.
- Phase 3: HexPolyMathlib, HexModArithMathlib, HexGramSchmidtMathlib.
- Phase 2 reviews/scaffolding: HexGF2, HexBerlekamp, HexHensel, HexConway,
  HexLLLMathlib.
- Phase 1 scaffolding: HexGFq, HexBerlekampZassenhaus,
  HexBerlekampMathlib, HexHenselMathlib, HexGF2Mathlib.

The blocked status graph is now mostly phase-promotion dependencies:
HexLLL Phase 4 waits on HexGramSchmidt Phase 4; HexGFqRing Phase 4 waits on
HexPolyFp Phase 4; HexGFqField Phase 4 waits on HexGFqRing Phase 4;
HexPolyZMathlib Phase 3 waits on HexPolyMathlib Phase 3; HexGFqMathlib
waits on HexGFq Phase 1; and HexBerlekampZassenhausMathlib waits on
HexBerlekampZassenhaus Phase 1.

## Follow-up focus

- Claim `#1072`, then continue the ordered GF2 monomial chain through
  `#1073` and `#1074` so `#1001` can unblock the Euclid reconstruction
  stream.
- Claim `#1075` to repair the HexHensel multifactor surface, then rerun the
  HexHensel Phase 2 review before any `libraries.yml` bump.
- Run the fresh HexBerlekamp Phase 2 review now that the certificate,
  factor-driver, and distinct-degree surfaces have landed.
- Continue Phase 4 review work for HexPolyZ, HexPolyFp, HexGramSchmidt, and
  HexMatrixMathlib, while Phase 5 proof work is available for HexArith,
  HexPoly, HexMatrix, and HexModArith.
