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

Profiles were regenerated at commit
`3bc24c50fbe57487776c433106894ee544a6d656` on `carica` (Apple M2 Ultra,
macOS 14.6.1, `arm64`) with `samply 0.13.1` at `999 Hz` through
`scripts/profile/run_profile.sh`. The binary reports `git_dirty: true` because
this worktree has an unrelated pre-existing `.claude/CLAUDE.md` modification.
The benchmark harness was `lean-bench 0.1.0` under
`leanprover/lean4:4.30.0-rc2`. The raw filtered Firefox Profiler JSON
artefacts are developer-local under `/tmp` and are not committed.

### `congruence-witnesses`

Command:

```sh
scripts/profile/run_profile.sh ./.lake/build/bin/hexpolyz_bench Hex.PolyZBench.runCoprimeModPWitness 512 5000000000
```

Representative case: deterministic dense Bezout witness check modulo `101`,
parameter `512`, no seed. The child row reported `512` inner repeats,
`2.979 s` total, `5.818 ms` per call, and result hash `0xb`. Leaf cost was
Lean own code `40.8%`, allocation/free `34.5%`, Lean runtime/refcount and
dispatch `24.7%`, and GMP `0.0%`. Inclusive cost was led by
`Hex.PolyZBench.runCoprimeModPWitness` (`100.0%`), the bench registration
wrapper (`100.0%`), dense multiplication in `DensePoly.mul` (`97.6%`), the
nested multiplication fold (`96.7%`), and the coefficient lookup used by the
finite-prefix congruence scan (`10.5%`). The dominant work is exactly the
registered Bezout-witness target: forming the dense product `s * f`, adding the
constructed witness term, and checking the finite coefficient prefix.

Diagnostics:

```json
{
  "bench_thread_name": "Thread <4410450>",
  "bench_thread_tid": "4410450",
  "regions_total": 3,
  "total_timed_ms": 2997.582124,
  "expected_samples_bench_thread": 2994.6,
  "retained_samples_bench_thread": 2917,
  "rejected_samples_bench_thread": 18,
  "off_bench_thread_samples_in_window": 0,
  "samply_interval_ms": 1.001001,
  "spawn_anchor_wall_ns": 1780141801708101000,
  "spawn_anchor_mono_ns": 329835612668000,
  "sidecar_mono_anchor_ns": 329836474315000,
  "samply_meta_start_time_ms": 1780141801733.4312
}
```

### `content-normalization`

Command:

```sh
scripts/profile/run_profile.sh ./.lake/build/bin/hexpolyz_bench Hex.PolyZBench.runPrimitivePartChecksum 131072 5000000000
```

Representative case: deterministic dense integer polynomials with nontrivial
content, parameter `131072`, no seed. The child row reported `128` inner
repeats, `3.392 s` total, `26.500 ms` per call, and result hash
`0x3bbdf5a725595d9`. Leaf cost was allocation/free `54.9%`, GMP
big-integer arithmetic `20.6%`, Lean runtime/refcount and boxing `13.0%`, and
Lean own code `11.4%`. Inclusive cost was led by the bench wrapper (`93.7%`),
`DensePoly.primitivePart` (`89.3%`), the content fold
`DensePoly.contentNat` (`70.5%`), and trailing-zero trimming while rebuilding
the primitive part (`6.6%`). The allocator share comes from constructing the
normalised polynomial, while the GMP share is the expected integer gcd/addition
work in the content computation. Both dominant paths are attributable to the
registered content and primitive-part targets.

Diagnostics:

```json
{
  "bench_thread_name": "Thread <4412372>",
  "bench_thread_tid": "4412372",
  "regions_total": 2,
  "total_timed_ms": 3417.557917,
  "expected_samples_bench_thread": 3414.1,
  "retained_samples_bench_thread": 3373,
  "rejected_samples_bench_thread": 19,
  "off_bench_thread_samples_in_window": 0,
  "samply_interval_ms": 1.001001,
  "spawn_anchor_wall_ns": 1780141815970789000,
  "spawn_anchor_mono_ns": 329849878683916,
  "sidecar_mono_anchor_ns": 329851109103666,
  "samply_meta_start_time_ms": 1780141815980.728
}
```

### `mignotte-helpers`

Command:

```sh
scripts/profile/run_profile.sh ./.lake/build/bin/hexpolyz_bench Hex.PolyZBench.runBinom 131072 5000000000
```

Representative case: central binomial coefficient `Nat.binom (2*n) n`,
parameter `131072`, no seed. The child row reported `2` inner repeats,
`3.731 s` total, `1.865 s` per call, and result hash
`0x19491e050eb44246`. Leaf cost was GMP big-integer arithmetic `96.9%`,
allocation/free `2.9%`, Lean runtime `0.2%`, and Lean own code `0.0%` at leaf
self time. Inclusive cost was led by `Nat.binom` (`100.0%`) and its fold
over multiplicative terms (`99.9%`). The dominant leaf frames were
`__gmpn_divrem_1` (`67.2%`), `__gmpn_copyi` (`20.8%`), and `__gmpn_mul_1`
(`8.5%`), which is the expected limb arithmetic for the central-binomial
Mignotte-helper stress case registered as `runBinom`.

Diagnostics:

```json
{
  "bench_thread_name": "Thread <4417677>",
  "bench_thread_tid": "4417677",
  "regions_total": 2,
  "total_timed_ms": 5718.860584,
  "expected_samples_bench_thread": 5713.1,
  "retained_samples_bench_thread": 5697,
  "rejected_samples_bench_thread": 10,
  "off_bench_thread_samples_in_window": 2,
  "samply_interval_ms": 1.001001,
  "spawn_anchor_wall_ns": 1780141880155764000,
  "spawn_anchor_mono_ns": 329914068371041,
  "sidecar_mono_anchor_ns": 329914532429916,
  "samply_meta_start_time_ms": 1780141880183.105
}
```

## Concerns

None.
