# HexPolyZ Performance Report

## Bench Targets

- `Hex.PolyZBench.runCongrPrefix`: `n`
- `Hex.PolyZBench.runCoprimeModPWitness`: `n * n`
- `Hex.PolyZBench.runContent`: `n`
- `Hex.PolyZBench.runPrimitivePartChecksum`: `n`
- `Hex.PolyZBench.runBinom`: `n * n`
- `Hex.PolyZBench.runFloorSqrtChecksum`: `n * Nat.log2 (n + 1)`
- `Hex.PolyZBench.runCeilSqrtChecksum`: `n * Nat.log2 (n + 1)`
- `Hex.PolyZBench.runCoeffNormSq`: `n`
- `Hex.PolyZBench.runCoeffL2NormBound`: `n`
- `Hex.PolyZBench.runMignotteCoeffBound`: `n`

## Verdicts

Scientific run at commit `33b7f720dcce514b455e26d27c402b415c192cd8` on
`carica` (Apple M2 Ultra, macOS 14.6.1), command:

```sh
lake exe hexpolyz_bench run Hex.PolyZBench.runCeilSqrtChecksum Hex.PolyZBench.runMignotteCoeffBound Hex.PolyZBench.runBinom Hex.PolyZBench.runCoeffNormSq Hex.PolyZBench.runContent Hex.PolyZBench.runCongrPrefix Hex.PolyZBench.runFloorSqrtChecksum Hex.PolyZBench.runPrimitivePartChecksum Hex.PolyZBench.runCoeffL2NormBound Hex.PolyZBench.runCoprimeModPWitness --export-file reports/bench-results/hex-poly-z-33b7f720dcce.json
```

The run used deterministic benchmark inputs from `HexPolyZ/Bench.lean`;
random seeds are not involved. The harness recorded `33b7f72-dirty` because
this worktree had an unrelated pre-existing `.claude/CLAUDE.md` modification.
Export artefact: `reports/bench-results/hex-poly-z-33b7f720dcce.json`.

- `Hex.PolyZBench.runCeilSqrtChecksum`: consistent with declared complexity
  (`β=-0.008`, parameters `1024..16384`, final hash
  `0x1a717901c8e1a30a`).
- `Hex.PolyZBench.runMignotteCoeffBound`: consistent with declared complexity
  (`β=+0.013`, parameters `8192..131072`, final hash `0x2617bde42`).
- `Hex.PolyZBench.runBinom`: consistent with declared complexity (`β=-0.063`,
  parameters `16384..131072`, final hash `0x19491e050eb44246`).
- `Hex.PolyZBench.runCoeffNormSq`: consistent with declared complexity
  (`β=+0.007`, parameters `8192..131072`, final hash `0x2931a5a118`).
- `Hex.PolyZBench.runContent`: consistent with declared complexity
  (`β=+0.002`, parameters `8192..131072`, final hash `0x6`).
- `Hex.PolyZBench.runCongrPrefix`: consistent with declared complexity
  (`β=-0.001`, parameters `8192..131072`, final hash `0xb`).
- `Hex.PolyZBench.runFloorSqrtChecksum`: consistent with declared complexity
  (`β=+0.002`, parameters `1024..16384`, final hash
  `0x59124940fe1749d1`).
- `Hex.PolyZBench.runPrimitivePartChecksum`: consistent with declared
  complexity (`β=+0.013`, parameters `8192..131072`, final hash
  `0x3bbdf5a725595d9`).
- `Hex.PolyZBench.runCoeffL2NormBound`: consistent with declared complexity
  (`β=-0.005`, parameters `8192..131072`, final hash `0x66b13`).
- `Hex.PolyZBench.runCoprimeModPWitness`: consistent with declared complexity
  (parameters `128..512`, final hash `0xb`).

Smoke wiring was also checked with:

```sh
lake exe hexpolyz_bench list
lake exe hexpolyz_bench verify
```

`verify` passed all 10 registered benchmarks at the same commit.

## Comparator Ratios

`SPEC/Libraries/hex-poly-z.md` does not name an external Phase-4 comparator
for `HexPolyZ`, so there are no comparator ratios to record in this snapshot.

## Profile

Profiles were captured with `samply record --save-only` through the
`lean-bench profile` subcommand at the same commit on `carica` (Apple M2 Ultra,
macOS 14.6.1). Sampling rate was samply's default 1000 Hz. The raw Firefox
Profiler JSON artefacts are developer-local and are not committed.

### `congruence-witnesses`

Command:

```sh
lake exe hexpolyz_bench profile Hex.PolyZBench.runCoprimeModPWitness --param 512 --profiler "samply record --save-only --output /tmp/hex-profiles/hex-poly-z-congruence-witnesses-33b7f720dcce.json.gz" --target-inner-nanos 5000000000
```

Representative case: deterministic dense Bezout witness check modulo `101`,
parameter `512`, no seed. The child row reported `1024` inner repeats,
`4.136 s` total, `4.039 ms` per call, and result hash `0xb`. Leaf cost was
dominated by Lean/Hex polynomial arithmetic and allocation from the dense
products in `runCoprimeModPWitness`; GMP and modular integer operations were
secondary. Inclusive cost was led by `Hex.PolyZBench.runCoprimeModPWitness`,
the dense polynomial multiplication in `DensePoly.mul`, and the final
finite-prefix congruence fold. The dominant work maps to the registered
congruence and Bezout-witness targets.

### `content-normalization`

Command:

```sh
lake exe hexpolyz_bench profile Hex.PolyZBench.runPrimitivePartChecksum --param 131072 --profiler "samply record --save-only --output /tmp/hex-profiles/hex-poly-z-content-normalization-33b7f720dcce.json.gz" --target-inner-nanos 5000000000
```

Representative case: deterministic dense integer polynomials with nontrivial
content, parameter `131072`, no seed. The child row reported `128` inner
repeats, `3.157 s` total, `24.665 ms` per call, and result hash
`0x3bbdf5a725595d9`. Leaf cost was concentrated in GMP integer gcd/division
work, allocation/free from rebuilding the primitive part, Lean runtime
overhead from array folds, and HexPolyZ/HexPoly normalization code. Inclusive
cost was led by `Hex.PolyZBench.runPrimitivePartChecksum`,
`ZPoly.primitivePart`, `ZPoly.content`, and the underlying coefficient fold.
The profile shape is attributable to the registered content and
primitive-part targets.

### `mignotte-helpers`

Command:

```sh
lake exe hexpolyz_bench profile Hex.PolyZBench.runBinom --param 131072 --profiler "samply record --save-only --output /tmp/hex-profiles/hex-poly-z-mignotte-helpers-33b7f720dcce.json.gz" --target-inner-nanos 5000000000
```

Representative case: central binomial coefficient `ZPoly.binom (2*n) n`,
parameter `131072`, no seed. The child row reported `2` inner repeats,
`3.669 s` total, `1.834 s` per call, and result hash
`0x19491e050eb44246`. Leaf cost was dominated by GMP big-integer
multiplication/division and allocation for the growing accumulator; Lean
runtime and own HexPolyZ loop overhead were smaller. Inclusive cost was led by
`Hex.PolyZBench.runBinom` and `ZPoly.binom`. This is the expected hot path for
the central-binomial stress case used to guard the Mignotte helper
implementation.

## Concerns

None.
