# HexBerlekamp Performance Report

## Bench Targets

- `Hex.BerlekampBench.runBerlekampMatrixChecksum`: `n * n`
- `Hex.BerlekampBench.runRabinTestChecksum`: `n * n * n`
- `Hex.BerlekampBench.runBerlekampFactorChecksum`: `n * n`
- `Hex.BerlekampBench.runDistinctDegreeChecksum`: `n * n * n`

## Verdicts

Scientific run at commit `e7bf7c23bbb5` on `carica` (Apple M2 Ultra,
macOS 14.6.1), command:

```sh
lake exe hexberlekamp_bench run \
    Hex.BerlekampBench.runBerlekampMatrixChecksum \
    Hex.BerlekampBench.runRabinTestChecksum \
    Hex.BerlekampBench.runBerlekampFactorChecksum \
    Hex.BerlekampBench.runDistinctDegreeChecksum \
    --export-file reports/bench-results/hex-berlekamp-e7bf7c2.json
```

The deterministic benchmark fixtures in `HexBerlekamp/Bench.lean` use
the fixed small prime `p = 5`; no random seeds are involved. The harness
recorded `e7bf7c2-dirty` because this worktree carried a pre-existing
local `.claude/CLAUDE.md` modification outside this evidence package.
Export artefact: `reports/bench-results/hex-berlekamp-e7bf7c2.json`,
SHA-256 `e21e8bbf5deefb5c3f44bd2b32005bee095c82487cce1aa1fa7bf3ee1bcbd30a`.

- `Hex.BerlekampBench.runBerlekampMatrixChecksum`: consistent with
  declared complexity (`cMin=1604.524, cMax=1914.459, beta=-0.058`,
  parameters `16..192`, final hash `0xa562d3f84baa18e9`).
- `Hex.BerlekampBench.runRabinTestChecksum`: consistent with declared
  complexity (`cMin=1124.630, cMax=1358.726, beta=-0.031`,
  parameters `8..64`, final hash `0xd`).
- `Hex.BerlekampBench.runBerlekampFactorChecksum`: consistent with
  declared complexity (`cMin=1927.593, cMax=2700.022, beta=-0.137`,
  parameters `16..256`, final hash `0xf7bf198d9173a6ce`).
- `Hex.BerlekampBench.runDistinctDegreeChecksum`: consistent with
  declared complexity (`cMin=1698.591, cMax=2925.243, beta=-0.316`,
  parameters `12..96`, final hash `0x967aa08b9f90679`).

Smoke wiring was checked at the same commit with:

```sh
lake exe hexberlekamp_bench list
lake exe hexberlekamp_bench verify
```

`verify` passed all four registered benchmarks.

## Comparator Ratios

`SPEC/Libraries/hex-berlekamp.md` does not name an external Phase-4
performance comparator for `HexBerlekamp`, so there are no
`phase4.comparators` ratios to record. The conformance oracle for
Berlekamp factoring remains the separate python-flint fixture driver
under `scripts/oracle/berlekamp_flint.py`; it is not a Phase-4
performance comparator named by the SPEC.

## Profile

The profiles below were recorded with `samply record --save-only
--unstable-presymbolicate` at commit `e7bf7c23bbb5` on `carica`
(Apple M2 Ultra, macOS 14.6.1) at the default 1 kHz sampling rate.
Raw Firefox Profiler JSON artefacts are developer-local under
`/tmp/hex-profiles/` and are not committed. The optimized macOS build
kept essentially all sampled child time in the generated Lean
registration closure for each target rather than unwinding through
smaller source functions; the attribution review below therefore maps
that closure back to the registered target and the source-level
algorithm path in `HexBerlekamp/Bench.lean` and `HexBerlekamp/*`.
Across the four child profiles, classified leaf samples were at least
99.5% own compiled Lean code, with Lean runtime and allocation/free
each below 0.5%; no GMP big-integer cost was observed, as expected for
fixed-word `ZMod64 5` arithmetic.

### `berlekamp-matrix`

Command:

```sh
lake exe hexberlekamp_bench profile Hex.BerlekampBench.runBerlekampMatrixChecksum \
    --param 192 --target-inner-nanos 5000000000 \
    --profiler "samply record --save-only --unstable-presymbolicate \
        -o /tmp/hex-profiles/hex-berlekamp-matrix-e7bf7c2.json --"
```

Representative case: deterministic monic `F_5` polynomial
`monicPoly 193 101`, parameter `n = 192`, no seed. Child row:
`inner_repeats=64`, `per_call_nanos=62169035.156250`,
`result_hash=0xa562d3f84baa18e9`. Total `4095` main-thread samples.
Leaf classification was own compiled Lean code 99.5%, Lean runtime
0.3%, allocation/free 0.1%, GMP 0.0%, other below 0.1%. Inclusive
cost was led by the optimized registration closure for
`runBerlekampMatrixChecksum` (99.5%). Source attribution maps this
closure to `berlekampMatrix`, whose work is the fixed-prime Frobenius
column recurrence over a degree-`n` dense polynomial. The dominant
work is exactly the registered `runBerlekampMatrixChecksum` target
and matches the declared quadratic model.

### `rabin-irreducibility`

Command:

```sh
lake exe hexberlekamp_bench profile Hex.BerlekampBench.runRabinTestChecksum \
    --param 64 --target-inner-nanos 5000000000 \
    --profiler "samply record --save-only --unstable-presymbolicate \
        -o /tmp/hex-profiles/hex-berlekamp-rabin-e7bf7c2.json --"
```

Representative case: deterministic monic `F_5` polynomial
`monicPoly 65 101`, parameter `n = 64`, no seed. Child row:
`inner_repeats=16`, `per_call_nanos=341168148.437500`,
`result_hash=0xd`. Total `5855` main-thread samples. Leaf
classification was own compiled Lean code 99.6%, Lean runtime 0.3%,
allocation/free below 0.1%, GMP 0.0%, other below 0.1%. Inclusive
cost was led by the optimized registration closure for
`runRabinTestChecksum` (99.6%). Source attribution maps this closure
to `rabinTest`, where the Frobenius remainder and bounded gcd checks
dominate the dense fixed-prime polynomial work. The profiled cost is
covered by the registered `runRabinTestChecksum` target and matches
the declared cubic model.

### `split-step-factorization`

Command:

```sh
lake exe hexberlekamp_bench profile Hex.BerlekampBench.runBerlekampFactorChecksum \
    --param 256 --target-inner-nanos 5000000000 \
    --profiler "samply record --save-only --unstable-presymbolicate \
        -o /tmp/hex-profiles/hex-berlekamp-factor-e7bf7c2.json --"
```

Representative case: Fibonacci-style polynomial pair
`fibPoly 258` and `fibPoly 257`, parameter `n = 256`, no seed.
Child row: `inner_repeats=32`, `per_call_nanos=128112763.000000`,
`result_hash=0xf7bf198d9173a6ce`. Total `4296` main-thread samples.
Leaf classification was own compiled Lean code 99.5%, Lean runtime
0.3%, allocation/free below 0.1%, GMP 0.0%, other below 0.1%.
Inclusive cost was led by the optimized registration closure for
`runBerlekampFactorChecksum` (99.5%). Source attribution maps this
closure to the constant-size sweep of `splitFactorAt` calls, each
performing a dense Euclidean gcd against the prepared witness. The
dominant work is directly measured by the registered target and
matches the declared quadratic fixed-prime model.

### `distinct-degree-factorization`

Command:

```sh
lake exe hexberlekamp_bench profile Hex.BerlekampBench.runDistinctDegreeChecksum \
    --param 96 --target-inner-nanos 5000000000 \
    --profiler "samply record --save-only --unstable-presymbolicate \
        -o /tmp/hex-profiles/hex-berlekamp-ddf-e7bf7c2.json --"
```

Representative case: deterministic monic `F_5` polynomial
`monicPoly 99 211`, parameter `n = 96`, no seed. Child row:
`inner_repeats=2`, `per_call_nanos=1523663271.000000`,
`result_hash=0x967aa08b9f90679`. Total `4642` main-thread samples.
Leaf classification was own compiled Lean code 99.5%, Lean runtime
0.3%, allocation/free below 0.1%, GMP 0.0%, other below 0.1%.
Inclusive cost was led by the optimized registration closure for
`runDistinctDegreeChecksum` (99.5%). Source attribution maps this
closure to `distinctDegreeFactor`, where repeated Frobenius updates
and gcds over the residual dominate. The work is covered by the
registered `runDistinctDegreeChecksum` target and matches the
declared cubic model.

## Concerns

