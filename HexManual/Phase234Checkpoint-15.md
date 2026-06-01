# Phase 2/3/4 Checkpoint 15

This checkpoint records the merge wave on `main` after summarize issue
`#1067`. It covers the GF2 monomial and inverse-proof chains, the
Berlekamp/Hensel/Berlekamp-Zassenhaus factoring surface, Mathlib bridge
scaffolding, benchmark-policy hardening, and current Phase 3/4/5 readiness
through PR `#1212`.

## Newly merged on `main` since checkpoint 14

### Benchmark policy and calibration

- PR `#1080` updated `SPEC/benchmarking.md` and the `lean-bench`
  dependency to make no-data benchmark runs mechanically fail and to forbid
  treating inconclusive verdicts as passing scientific evidence.
- PR `#1084` recorded calibration evidence for the benchmark floor used by
  current Phase 4 work.
- PR `#1206` added `scripts/check_phase4.py`, wired it into CI for changed
  `setup_benchmark` registrations, and updated `PLAN/Phase4.md` so new or
  changed parametric benchmark registrations need adjacent cost-model
  derivations and derivation-bearing commit messages.

### GF2 proof, conformance, and benchmark stream

- PRs `#1088`, `#1093`, and `#1100` completed the right-monomial
  multiplication chain from active-row coefficients through no-effect rows to
  the public `q * monomial k = q.mulXk k` bridge.
- PRs `#1111`, `#1115`, `#1116`, `#1117`, `#1121`, and `#1122` built the
  left one-hot CLMUL and left-monomial proof surface, while PRs `#1128`,
  `#1130`, `#1131`, `#1133`, `#1134`, `#1136`, `#1140`, `#1141`, `#1151`,
  `#1158`, `#1159`, and `#1160` advanced xor-linearity, quotient
  reconstruction, div/mod, xgcd Bezout, gcd divisibility, inverse-zero, and
  wrapper cancellation proofs.
- PR `#1161` finally certified HexGF2 Phase 2, and PR `#1165` added core
  conformance, moving HexGF2 through Phase 3.
- PRs `#1167`, `#1171`, and `#1173` added packed-core, field-wrapper, and
  packed-versus-generic comparison benchmarks. PRs `#1178`, `#1179`, `#1180`,
  and `#1181` added CI smoke and repaired the initial comparison verdict
  findings; PR `#1183` promoted HexGF2 through Phase 4.
- PR `#1205` then audited the GF2 comparison cost-model derivations, rolled
  `HexGF2.done_through` back from `4` to `3`, and filed `#1204` for the
  registrations whose corrected `O(n^2)` declarations still produced
  inconclusive verdicts. HexGF2 is therefore back at the Phase 4 frontier
  pending the implementation-level benchmark investigation.
- PRs `#1185` and `#1198` resumed HexGF2 Phase 5 proof work by localizing the
  inverse-congruence obligations and proving the irreducible reduced common
  divisor helper.

### Factoring, Hensel, and Zassenhaus surface

- PR `#1083` added the HexHensel multifactor lift API, and PR `#1089`
  certified HexHensel Phase 2. PR `#1103` then added HexHensel Phase 3 core
  conformance.
- PR `#1094` found a HexBerlekamp certificate blocker; PR `#1095` repaired the
  irreducibility certificate shape; PR `#1101` certified HexBerlekamp Phase 2;
  and PR `#1108` added HexBerlekamp Phase 3 conformance.
- PRs `#1092`, `#1096`, `#1145`, `#1153`, `#1154`, `#1155`, and `#1163`
  expanded the Berlekamp-Zassenhaus executable pipeline: factor entries,
  irreducibility certificates, synchronized certificate data, square-free and
  content normalization, exhaustive recombination, degree obstruction
  certificates, and normalized public-factor input handling.
- PR `#1190` reviewed HexBerlekampZassenhaus Phase 2 and found a checker gap:
  nested Rabin certificate metadata was not validated against the concrete
  modular factor. PR `#1208` fixed that by storing concrete modular
  `factorPolys`, checking monicity and degree alignment, calling the
  Berlekamp certificate checker on each modular factor, and adding malformed
  certificate conformance coverage.
- PR `#1212` reran the HexBerlekampZassenhaus Phase 2 review after the fix,
  added the scaffolding-reviewed token, and advanced
  `HexBerlekampZassenhaus.done_through` to `2`.

### Mathlib bridge and arithmetic work

- PR `#1120` isolated the arithmetic prime API from Mathlib's `Nat`
  namespace.
- PR `#1132` scaffolded the initial HexBerlekampMathlib correctness theorem
  surface. PR `#1149` recorded Phase 2 blockers for that bridge, PR `#1150`
  added the `FpPoly` transfer bridge API, and PR `#1169` exposed Rabin local
  glue.
- PR `#1146` scaffolded the HexHenselMathlib correctness theorem surface.
- PRs `#1191` and `#1199` discharged HexArith Phase 5 proof obligations in
  the Nat modular arithmetic layer and UInt64 wide-word bridge layer.

### Benchmark findings and proof cleanups beyond GF2

- PR `#1201` added derivation comments for the HexGramSchmidt adjacent-swap
  benchmark registrations and filed the scaled-coefficient finding tracked by
  `#1200`. PR `#1207` fixed the fixture and timing domain so the four affected
  adjacent scaled-coefficient registrations report consistent verdicts.
- PR `#1203` documented HexPolyZ binomial and Mignotte models plus HexPoly
  Euclidean worst-case models, and filed `#1202` for the Euclidean verdict
  uncertainty. PR `#1210` reran the affected HexPoly Euclidean registrations,
  confirmed consistent verdicts at current `HEAD`, and strengthened the local
  derivation comments.
- PR `#1209` proved the HexPoly dense constructor normalization obligations in
  `HexPoly/Dense.lean`, leaving HexPoly Phase 5 proof work focused on
  operations and Euclidean lemmas.

## Current queue frontier

- Unclaimed: none at this checkpoint.
- Claimed: `#1211` is working the HexPoly foundational operation lemmas;
  `#1204` is investigating the inconclusive HexGF2 comparison benchmark
  verdicts after the rollback; `#1162` is this checkpoint.
- Open PR state: `coordination orient` reports no open PRs and no PRs needing
  repair.
- The formerly highlighted `#1142` HexBerlekampZassenhaus normalization stream
  has landed through PR `#1163`. The `#1148` HexBerlekampMathlib Rabin local
  glue stream has landed through PR `#1169`.

## Ready phase frontier

`python3 scripts/status.py` currently reports these ready dispatch targets:

- Phase 5: HexArith, HexPoly, HexMatrix, HexModArith.
- Phase 4: HexGramSchmidt, HexGF2, HexPolyZ, HexPolyFp, HexMatrixMathlib.
- Phase 3: HexConway, HexBerlekampZassenhaus, HexPolyMathlib,
  HexModArithMathlib, HexGramSchmidtMathlib.
- Phase 2 reviews: HexLLLMathlib, HexBerlekampMathlib, HexHenselMathlib.
- Phase 1 scaffolding: HexGFq, HexGF2Mathlib,
  HexBerlekampZassenhausMathlib.

The blocked status graph is now:

- HexLLL Phase 4 waits on HexGramSchmidt Phase 4.
- HexGFqRing Phase 4 waits on HexPolyFp Phase 4.
- HexGFqField Phase 4 waits on HexGFqRing Phase 4.
- HexBerlekamp Phase 4 waits on HexPolyFp Phase 4 and HexGFqRing Phase 4.
- HexHensel Phase 4 waits on HexPolyFp Phase 4 and HexPolyZ Phase 4.
- HexPolyZMathlib Phase 3 waits on HexPolyMathlib Phase 3.
- HexGFqMathlib Phase 1 waits on HexGFq Phase 1.

## Follow-up focus

- Finish `#1204` before attempting to restore HexGF2 Phase 4 promotion; the
  rollback means downstream GF2 Phase 5 claims should account for the current
  Phase 4 benchmark finding.
- Land `#1211` or equivalent HexPoly operations proof work, then continue the
  remaining HexPoly Phase 5 clusters in `HexPoly/Euclid.lean`.
- Dispatch HexBerlekampZassenhaus Phase 3 conformance now that the Phase 2
  checker review has landed.
- Continue Phase 4 review and benchmark work for HexGramSchmidt, HexPolyZ,
  HexPolyFp, and HexMatrixMathlib, using the new derivation-comment gate for
  changed benchmark registrations.
