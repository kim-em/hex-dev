# Phase 2/3/4/5 Checkpoint 16

This checkpoint records the merge wave on `main` after summarize issue
`#1162`. It covers the dense-polynomial Phase 5 proof stream, benchmark
policy tightening, the `HexGFq` Phase 1 through Phase 3 transition,
`HexGFqRing` and `HexGFqField` Phase 4 benchmark work, and the current
Phase 5 proof frontier through PR `#1324`.

## Newly merged on `main` since checkpoint 15

### HexPoly and HexPolyFp proof work

- PRs `#1214`, `#1220`, `#1226`, `#1235`, `#1237`, `#1247`, `#1251`,
  `#1254`, `#1257`, `#1260`, `#1261`, `#1262`, and `#1275` reduced the
  `HexPoly` Phase 5 surface across core operation lemmas, primitive-part
  content, modular reduction, CRT congruence splitting, the narrowed
  division-law API, subtraction modulo, modulus multiples, self and zero
  remainder laws, and follow-on CRT congruence factoring.
- PRs `#1264`, `#1271`, `#1278`, `#1295`, and `#1296` advanced the dense
  multiplication proof stack with the coefficient formula, negation bridge,
  right algebra laws, generic triangular fold reindexing, and the
  associativity fold needed by later multiplication associativity proofs.
- PR `#1248` added the `HexPolyFp` Phase 4 benchmark harness, and PR `#1286`
  repaired square-free factor accumulation to avoid quadratic list appends.

### Arithmetic, GF2, and benchmark policy

- PRs `#1265`, `#1281`, and `#1291` added the `HexArith` prime-divisibility
  skeleton and `ZMod64` add/sub/pow representative laws.
- PR `#1218` repaired the packed GF2 comparison model, while PRs `#1273` and
  `#1276` reran and completed the HexGF2 Phase 4 benchmark review, moving
  HexGF2 back to the Phase 5 proof frontier.
- PRs `#1267` and `#1283` tightened benchmark policy and SPEC guidance:
  wrong-complexity implementation shapes are now explicitly forbidden in the
  affected library SPECs, verdict-fitting is named as an anti-pattern, and new
  or changed registrations need adjacent derivation comments.

### Gfq, Conway, and factoring surface

- PR `#1221` completed the `HexGFq` Phase 1 scaffold, PR `#1230` reviewed the
  Phase 2 scaffold, PR `#1242` added the GF2q-to-GFq bridge, PR `#1298` added
  the core conformance module, and PR `#1300` completed `HexGFq` Phase 3.
- PR `#1239` added Tier 1 `HexConway` conformance checks.
- PR `#1222` completed the `HexBerlekampZassenhaus` conformance core.
- PR `#1253` completed the `HexGF2Mathlib` Phase 1 scaffold audit.

### Gram-Schmidt, LLL, and Mathlib bridge work

- PRs `#1234` and `#1240` reviewed and repaired the HexGramSchmidt Phase 4
  benchmark signal floor.
- PRs `#1280`, `#1285`, and `#1292` recorded the `HexLLLMathlib` Phase 2
  blocker, repaired the short-vector statement, and reran the Phase 2 review.
- PRs `#1284` and `#1287` fixed SPEC-audited performance shapes by sharing
  the scaled-coefficients Bareiss pass and targeting HexLLL step updates.
- PRs `#1314`, `#1317`, `#1319`, and `#1320` added the HexLLL Phase 4
  benchmark smoke surface, recorded the initial inconclusive scientific run,
  tuned benchmark signal windows, and repaired the potential benchmark model,
  moving HexLLL to the Phase 5 frontier.

### GfqRing and GfqField benchmark and inverse frontier

- PRs `#1302`, `#1306`, and `#1305` added, stabilized, and reviewed the
  `HexGFqRing` Phase 4 quotient-ring benchmark surface, promoting
  `HexGFqRing` to Phase 5 readiness.
- PRs `#1308`, `#1311`, and `#1312` added the `HexGFqField` Phase 4 benchmark
  surface, recorded the first verdict pass, and resolved the inverse benchmark
  window, promoting `HexGFqField` to Phase 5 readiness.
- PR `#1324` added the scalar-scale and quotient-reduction lemmas needed by
  the `HexGFqField` inverse proof cluster, proving the scaled Bezout bridge
  and leaving the final irreducible-gcd normalization issue for replanning.

## Current queue frontier

- Unclaimed: `#1321` covers the `HexMatrix` determinant row-operation proof
  cluster.
- Claimed: `#1297` is this checkpoint.
- Replan: `#1313` is the original oversized `HexGFqField` inverse xgcd parent,
  and `#1323` needs replanning because the requested generic normalization
  theorem requires a prime-field or unit hypothesis beyond the current
  `ZMod64.Bounds p` API.
- Open PR state: `coordination orient` reports no open PRs and no PRs needing
  repair.

## Ready phase frontier

`python3 scripts/status.py` currently reports these ready dispatch targets:

- Phase 5: HexArith, HexPoly, HexMatrix, HexModArith, HexGramSchmidt, HexGF2,
  HexLLL, HexPolyFp, HexGFqRing, HexGFqField.
- Phase 4: HexPolyZ, HexBerlekamp, HexMatrixMathlib.
- Phase 3: HexPolyMathlib, HexModArithMathlib, HexGramSchmidtMathlib,
  HexLLLMathlib.
- Phase 2 reviews: HexBerlekampMathlib, HexHenselMathlib, HexGF2Mathlib.
- Phase 1 scaffolding: HexGFqMathlib, HexBerlekampZassenhausMathlib.

The blocked status graph is now:

- HexHensel Phase 4 waits on HexPolyZ Phase 4.
- HexConway Phase 4 and HexGFq Phase 4 wait on HexBerlekamp Phase 4.
- HexBerlekampZassenhaus Phase 4 waits on HexBerlekamp Phase 4 and HexHensel
  Phase 4.
- HexPolyZMathlib Phase 3 waits on HexPolyMathlib Phase 3.

## Follow-up focus

- Replan the `HexGFqField` inverse normalization theorem around the missing
  prime-field or coefficient-unit hypothesis before attempting to close
  `reduceMod_repr_mul_invPoly_eq_one`.
- Decompose or strengthen the `HexMatrix` determinant row-operation proof
  issue with reusable lemmas for `permutationVectors`, determinant products,
  and row-operation reindexing before attacking all four determinant theorems.
- Continue the `HexPoly` and `HexPolyFp` Phase 5 proof streams; the recent
  multiplication and modular-reduction lemmas have made the next Euclidean and
  CRT obligations narrower.
- Dispatch Phase 4 reviews for HexPolyZ, HexBerlekamp, and HexMatrixMathlib,
  using the current benchmark policy gates for any changed registrations.
