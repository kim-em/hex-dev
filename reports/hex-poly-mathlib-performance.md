# HexPolyMathlib Performance Report

## Bench Targets

- `HexPolyMathlib.PolyBench.runToPolynomialChecksum`: `n`
- `HexPolyMathlib.PolyBench.runOfPolynomialChecksum`: `n`
- `HexPolyMathlib.PolyBench.runRoundTripChecksum`: `n`
- `HexPolyMathlib.PolyBench.runGcdBridgeChecksum`: `n * n`
- `HexPolyMathlib.PolyBench.runXGcdBridgeChecksum`: `n * n`

## Verdicts

Scientific run at commit `0a0ff08951c259c6747c2da0790bd006aeaed920` on
`carica` (Apple M2 Ultra, macOS 14.6.1), command:

```sh
lake exe hexpolymathlib_bench run \
  HexPolyMathlib.PolyBench.runToPolynomialChecksum \
  HexPolyMathlib.PolyBench.runOfPolynomialChecksum \
  HexPolyMathlib.PolyBench.runRoundTripChecksum \
  HexPolyMathlib.PolyBench.runGcdBridgeChecksum \
  HexPolyMathlib.PolyBench.runXGcdBridgeChecksum \
  --export-file reports/bench-results/hex-poly-mathlib-0a0ff08951c2.json
```

The run used deterministic benchmark inputs from `HexPolyMathlib/Bench.lean`;
random seeds are not involved. The harness recorded `0a0ff08-dirty` because
this worktree had an unrelated pre-existing `.claude/CLAUDE.md` modification.
Export artefact: `reports/bench-results/hex-poly-mathlib-0a0ff08951c2.json`.

- `HexPolyMathlib.PolyBench.runToPolynomialChecksum`: consistent with declared
  complexity (`β=+0.011`, parameters `1024..16384`, final hash
  `0xdc12a932180e7fb9`).
- `HexPolyMathlib.PolyBench.runOfPolynomialChecksum`: consistent with declared
  complexity (`β=+0.034`, parameters `1024..16384`, final hash
  `0x1c006f1e00bb4d20`).
- `HexPolyMathlib.PolyBench.runRoundTripChecksum`: consistent with declared
  complexity (`β=+0.007`, parameters `1024..16384`, final hash
  `0xc0d028def0d7143a`).
- `HexPolyMathlib.PolyBench.runGcdBridgeChecksum`: consistent with declared
  complexity (`β=+0.053`, parameters `16..96`, final hash
  `0xb7fdc77087dff74d`).
- `HexPolyMathlib.PolyBench.runXGcdBridgeChecksum`: consistent with declared
  complexity (`β=+0.043`, parameters `16..96`, final hash
  `0xedd29fef92e48561`).

Smoke wiring was also checked with:

```sh
lake exe hexpolymathlib_bench list
lake exe hexpolymathlib_bench verify
```

`verify` passed all 5 registered benchmarks at the same commit.

## Comparator Ratios

`SPEC/Libraries/hex-poly-mathlib.md` does not name an external Phase-4
comparator for `HexPolyMathlib`, so there are no comparator ratios to
record in this snapshot.

## Profile

Profiles were captured with `samply record --save-only --unstable-presymbolicate`
through the `lean-bench profile` subcommand at the same commit on `carica`
(Apple M2 Ultra, macOS 14.6.1). Sampling rate was samply's default 1000 Hz.
Leaf and inclusive aggregations were taken from the child benchmark thread of
each capture using the `--unstable-presymbolicate` symbol sidecar. The raw
Firefox Profiler JSON artefacts and sidecars are developer-local and are not
committed.

### `dense-mathlib-conversion`

Command:

```sh
lake exe hexpolymathlib_bench profile HexPolyMathlib.PolyBench.runRoundTripChecksum --param 16384 --profiler "samply record --save-only --unstable-presymbolicate --output /tmp/hex-profiles/hex-poly-mathlib-conversion-0a0ff08951c2.json.gz" --target-inner-nanos 5000000000
```

Representative case: deterministic dense integer polynomial paired with the
matching Mathlib polynomial, parameter `16384`, no seed. The child row reported
`512` inner repeats, `3.676 s` total, `7.180 ms` per call, and result hash
`0xc0d028def0d7143a`. Leaf cost was Lean runtime/harness 66.3% (dominated by
`lean_apply_1`/`lean_apply_4` dispatch, `lean_dec_ref_cold` refcount work,
`lean_inc_heartbeat`, and Lean array/list stdlib helpers), allocation/free
19.5% (mimalloc small-bucket malloc/free and `lean_free_object`), own
HexPolyMathlib code 12.1%, and 2.2% other system. GMP did not appear in this
trace because the deterministic integer coefficients fit in fixnums for the
parameter range exercised by `runRoundTripChecksum`. Inclusive HexPolyMathlib
cost was led by `runRoundTripChecksum` (59.7%), `ofPolynomial` under
`runOfPolynomialChecksum`-shaped specialization (33.3%), the `checksumMathlib`
fold (16.9%), `denseFinsupp`/`toPolynomialBench` (6.5%), and the
`Multiset.map`/`List.mapTR_loop` chain that backs Mathlib's polynomial
construction (7.0%). The dominant work maps to the registered conversion and
round-trip targets.

### `euclidean-bridge-transport`

Command:

```sh
lake exe hexpolymathlib_bench profile HexPolyMathlib.PolyBench.runXGcdBridgeChecksum --param 96 --profiler "samply record --save-only --unstable-presymbolicate --output /tmp/hex-profiles/hex-poly-mathlib-euclidean-bridge-0a0ff08951c2.json.gz" --target-inner-nanos 5000000000
```

Representative case: polynomial Fibonacci quotient-chain over `Rat`, parameter
`96`, no seed. The child row reported `256` inner repeats, `3.358 s` total,
`13.118 ms` per call, and result hash `0xedd29fef92e48561`. Leaf cost was
allocation/free 58.6% (nanozone and `_malloc_zone_*` paths plus mimalloc
fallbacks driven by GMP integer rebuilds and `Rat` arithmetic), GMP 23.3%
(`__gmpz_add`, `__gmpz_init_set_ui`, `__gmpz_realloc`, `__gmpz_gcd`,
`__gmpz_clear`, `__gmpz_mul_2exp`, `__gmpn_gcd_1`, plus the `lean::mpz`
wrapper destructor), Lean runtime 8.0%, own HexPolyMathlib/HexPoly code 6.1%,
and 4.0% other. Inclusive HexPolyMathlib cost was led by
`runXGcdBridgeChecksum` (99.6%), `DensePoly.xgcdAux` driving the executable
extended-Euclidean loop (99.5%), the `DensePoly.mul` Fibonacci prep fold
(63.3%), `DensePoly.divMod`/`divModArray`/`divModArrayAux`/
`subtractScaledShift*` invoked from `xgcdAux` (≈17–19%), and `lean_nat_gcd`
backing `Rat` normalization on the Bezout coefficients (69.6%). The dominant
allocation, GMP, and own-code leaves are attributable to the registered
gcd-bridge and extended-gcd-bridge targets that compute `DensePoly.gcd`/
`DensePoly.xgcd` over rational coefficients and transport the result through
`toPolynomialBench`.

## Concerns

None.
