# HexConway performance and coverage

## Verified coverage

The committed scope contains **594 entries**, preserving all 38 original entries:

| Characteristic | Degrees |
|---|---|
| 2 | 1–16 |
| 3, 5, 7 | 1–8 |
| 11, 13 | 1–6 |
| Other primes below 300 | 1–4 |
| Primes between 300 and 1000 | 1–3 |

There are no holes in these ranges. They are closed under positive degree
divisors, cover all 168 prime characteristics below 1000, and include 426
entries of degree at least two. Every entry has an irreducibility proof and a
primitivity proof, including the trivial group at `(2,1)`. All **522** supported
proper-divisor pairs have compatibility proofs. Exact keys are exported as
`supportedPairs` and committed in `scripts/conway/scope.json`.

Generated `HexGFq.CommittedEntry` instances cover the same entries. The Mathlib
companion specializes generator orders for every entry and canonical embeddings
for every supported proper-divisor pair. Unselected source rows do not count
as verified coverage.

## Measurement contract

The designated machine is **chungus2**, an AMD EPYC 9455 (48 physical cores,
96 logical CPUs), Linux x86-64, with approximately 125 GiB RAM. The toolchain
is `leanprover/lean4:v4.34.0-rc2`. Controlled builds set
`LEAN_NUM_THREADS=8`, with Lake's default scheduling. The final generator
uses four serial import chains per polynomial-proof family; each compatibility
chain follows its primitivity chain. Factor-prime proofs form one serial chain.
The study launches no overlapping Lake builds or runtime benchmarks. This is
a shared machine: unrelated users can run other work. The selected scope must
pass all repeats despite that variability; new measurement records also include
the system load averages at each run's start and finish.

The acceptance ceiling is **300 seconds of wall time**, including table
compilation, generated APIs, irreducibility, primitivity, compatibility, and
all normal `lake build HexConway` outputs. Dependencies are already built.
`scripts/conway/measure.py` deletes every Conway output under `.lake/build`
(including Lean, IR, and umbrella outputs), retains dependency outputs, and
passes `--no-cache` to Lake. It rejects a measurement that rebuilt an external
dependency. Each scope has three controlled runs. A terminated run is an
unfinished rebuild and cannot establish verified coverage.

Every linked JSON contains the exact pair list, toolchain, machine, thread
settings, source and input hashes, wall time, per-module timings, output sizes
by suffix, and links to compressed verbose logs and GNU time output. Lake's
module times include elaboration, kernel checking and output generation;
they are rounded by Lake and their sum is **not** build wall time.

Memory has two distinct measures: GNU time's maximum child RSS and the maximum
sampled sum of RSS over the process tree (sample interval 0.1 seconds). The
latter captures simultaneous compiler processes but can count shared mappings
more than once. The original baseline records only maximum child RSS because
the first tree sampler did not traverse children belonging to other threads.
Artifact sizes include every retained Conway output, not just `.olean` files.
The source hashes of the accepted Conway and companion runs match the committed
library sources. The final records also hash the local dependency import closure,
including meta imports and `HexPrimality.Cert`. The source-dirty flag excludes
measurement reports, and the warm-import list is recorded before timing begins.
For capped runs these are incomplete artifacts, not the size of a full library.

The worst accepted run leaves **55.214 seconds (18.4%)** below the ceiling.
Adding entries or changing replay code requires three fresh measurements;
marginal costs do not justify extrapolating acceptance.

The [rebase source comparison](conway/rebase-equivalence.json) verifies that
all 312 Conway and local-dependency source hashes remain unchanged on the
updated main branch. Only the LeanBench package pin changes, from `b583ddd`
to `8a37daf`; the proof library does not import LeanBench. Compiled scientific
measurements use the updated framework separately below.

## Candidate measurements

| Scope / raw evidence | Entries | Wall seconds, three runs | Peak RSS GiB | Output MiB | Result |
|---|---:|---|---:|---:|---|
| [baseline](conway/baseline.json) | 38 | 118.506, 124.945, 146.494 | 5.3 (child) | 10.7 | complete |
| [optimized-38](conway/optimized-38.json) | 38 | 42.942, 35.544, 33.342 | 3.2 | 11.5 | complete |
| [candidate-90](conway/candidate-90.json) | 90 | 64.722, 64.241, 62.820 | 16.4 | 27.6 | complete |
| [wide-414](conway/wide-414.json) | 414 | 119.673, 107.784, 107.633 | 16.5 | 134.6 | complete |
| [envelope-820](conway/envelope-820.json) | 820 | 300.091, 300.091, 300.054 | 44.6 | 72.1 | capped; incomplete |
| [wide-700](conway/wide-700.json) | 700 | 300.057, 300.057, 300.041 | 10.9 | 202.9 | capped; incomplete |
| [control-38](conway/control-38.json) | 38 | 20.933, 21.940, 22.646 | 5.6 | 14.3 | complete |
| [binary32-closure](conway/binary32-closure.json) | 40 | 300.078, 300.088, 300.081 | 73.9 | 16.6 | capped; incomplete |
| [binary64-closure](conway/binary64-closure.json) | 41 | 240.816, 300.030, 300.037 | 80.0 | 11.4 | capped; incomplete |
| [shared-700](conway/shared-700.json) | 700 | 300.086, 300.071, 300.033 | 10.8 | 205.7 | capped; incomplete |
| [quartic-500](conway/quartic-500.json) | 627 | 258.782, 300.048, 264.111 | 10.6 | 190.4 | one capped; rejected |
| [quartic-300](conway/quartic-300.json) | 594 | 251.817, 252.737, 270.963 | 10.8 | 180.9 | complete |
| [direct exponents, 594](conway/final-594.json) | 594 | 224.512, 213.630, 228.874 | 10.7 | 179.7 | complete |
| [direct exponents, 627](conway/direct-627.json) | 627 | 249.186, 277.803, 300.010 | 10.4 | incomplete | one capped; rejected |
| [accepted 594](conway/accepted-594.json) | 594 | 244.786, 217.620, 211.232 | 10.8 | 179.7 | complete |

These measure several implementations, not just different row counts. The
baseline is the original 38-entry implementation at `b7f4d6200`; its Tier 1
certificate module alone takes 28–35 seconds, while primitivity takes
82–102 seconds. The earlier report's approximately 31 seconds was therefore
not a measurement of the full library. `optimized-38` measures intermediate
binary replay before full sharding. `candidate-90` matches the Lean sources
at `c38650d96`. The first wide scopes use binary replay and four proof chains;
`wide-700` matches `1a1910190`. `shared-700` additionally shares Pocklington
child proofs. Historical dirty measurements identify measured files by SHA-256;
the `commit` field alone is not a claim that all measured sources were committed
at that revision. Reproduction of an intermediate variant requires its stated
implementation as well as its pair list.

All broad reduced scopes keep degrees 1–16 at characteristic 2, 1–8 at
3, 5 and 7, and 1–6 at 11 and 13. The 90-entry scope adds degrees 1–2 at
other primes below 100. The 414-entry scope extends those primes to degree 4
and adds degrees 1–2 at every prime between 100 and 1000. The 700-entry scope
extends every prime above 13 to degree 4. The 627-entry scope retains degree 4
only below characteristic 500 and degree 3 at the remaining primes. These are divisor-closed scopes.
The 820-entry envelope is exactly the issue's proposed envelope, without holes.

The accepted 594-entry scope keeps quartic coverage below characteristic 300
and cubic coverage above that boundary. Its final controlled runs take
**244.786, 217.620, 211.232 seconds**, all below the ceiling.

The checker computes exponents directly, avoiding redundant digit-list witnesses.
An initial three-run measurement of this simplification takes 224.512, 213.630
and 228.874 seconds. That additional margin warrants remeasuring the 627-entry
scope: adding 33 quartic entries, with their 66 new compatibility obligations,
takes 249.186, 277.803 and 300.010 seconds. The third run is terminated, so this
larger scope is rejected despite its two successful runs. The accepted scope is
then restored and measured with the finalized import/provenance tooling.

These are whole-scope marginal comparisons: the degree-one and degree-two
dependencies of the additional quartic entries are already present. The
individual binary-entry comparison below also records all missing-entry and
compatibility obligations. None of these costs supports extrapolating a larger
scope without rebuilding it.

For the accepted scope, summed module times (seconds) are:

| Module or generated family | Run 1 | Run 2 | Run 3 |
|---|---:|---:|---:|
| Table data | 50.16 | 46.86 | 46.90 |
| Rabin certificates | 200.07 | 144.84 | 142.93 |
| Generated API | 70.01 | 50.10 | 49.21 |
| Factor-prime proofs | 4.94 | 5.03 | 5.03 |
| Primitivity | 325.02 | 344.44 | 323.88 |
| Compatibility | 137.81 | 137.25 | 136.16 |
| Power helpers and generation commands | 2.35 | 2.36 | 2.38 |

Every completed run produces 179.74 MiB of Conway outputs. Peak sampled
process-tree RSS is 10.85, 10.48, 10.47 GiB. The module sums exceed wall
time because the four chains run concurrently. The raw JSON retains each
individual shard's timing and artifact totals by suffix.

### Marginal accepted binary depth

A [38-entry control with shared factor-prime proofs](conway/control-38-shared.json)
takes 18.369, 18.789, 18.169 seconds. Adding only `(2,16)` gives the
[39-entry divisor-closed scope](conway/binary16-closure.json), taking
32.778, 32.496, 32.503 seconds. Its proper divisors 1, 2, 4 and 8 are already
present, so the marginal addition includes **one entry and four compatibility
proofs** (56 total), as well as its table, API, irreducibility and primitivity
outputs. The median wall-time difference is
14.134 seconds.
The 39-entry outputs occupy 14.71 MiB,
with peak process-tree RSS 8.14 GiB.
This is an entire clean-scope comparison, not timing a theorem with its
supporting outputs cached. These individual-entry probes use the preceding digit-list checker; their
source hashes identify that implementation. The accepted scope is restored
after the probes.

### Expensive and unavailable candidates

The full 820-entry envelope exceeds the ceiling: its first Rabin shards alone
take approximately 251–254 seconds. Binary degree 32 is a useful, expensive
case even outside the whole envelope. Adding `(2,16)` and `(2,32)` to the
baseline adds two entries and **nine** compatibility obligations (61 total);
all three complete-closure rebuild attempts exceed 300 seconds. Binary degree
64 adds `(2,16)`, `(2,32)` and `(2,64)` to the baseline, with **15** new
compatibility obligations (67 total). Its Rabin replay remains unfinished in
all three runs: one is stopped at the 80 GiB process-tree RSS guard after
240.816 seconds, two at the wall-time ceiling. Thus the additional degree-64
entry alone introduces six further compatibility obligations, not one proof.
The [38-entry control](conway/control-38.json) uses the same polynomial checker
and scheduling as these closure probes and takes 20.933–22.646 seconds.
These marginal experiments measure the entry, missing divisor entries and
all new obligations together; they do not subtract an isolated certificate
microbenchmark from a whole-library time.

Binary degree 128 is **unavailable** in the pinned Lübeck import. The
[characteristic-2 source page](https://www.math.rwth-aachen.de/~Frank.Luebeck/data/ConwayPol/CP2.html)
also skips it, and the optional `conway-polynomials` 0.10 package has no such
entry. Its closure would require degrees 16, 32 and 64 in addition to existing
binary degrees. No unavailable entry is synthesized or advertised.

### Verification bottlenecks and changes

Binary square-and-multiply replaces characteristic-linear power replay, and
structural Horner composition avoids kernel reduction into an opaque packed
runtime implementation. Equality proofs connect both structural checkers to
the existing soundness theorems. A compiler simplification theorem retains
packed composition for compiled clients. Generated table dispatch is nested by
characteristic and degree; large flat tuple matches exceeded elaboration limits.
Four serial proof chains bound concurrent proof heaps. Compatibility waits for
the corresponding primitivity chain so these two expensive families do not
start eight large proof heaps together.

`HexPrimality` is Mathlib-free but was not wired into Conway verification.
The new `Hex.Nat.prime_of_pocklington` bridge proves a checked parent from
separately proved child primes, using the existing Pocklington soundness proof.
The generator shares these proofs in increasing-prime order. Small primes use
bounded trial division below 100000; larger primes use checked Pocklington
arithmetic. Child certificate payloads carry subjects, and the bridge requires
actual primality proofs for every child: a `.small` payload by itself is not
claimed to pass the recursive certificate checker. In the 700-entry experiment,
sharing reduces summed factor-prime module time from 370–454 seconds to under
ten seconds. Polynomial power and compatibility replay still push the full
700-entry build above the ceiling. That experiment uses the digit-list checker; it does not establish a
mathematical limit on Conway polynomials or a timing for every later variant.
The direct-exponent checker remeasures the nearer 627-entry frontier, which
still fails one of three runs. No exhaustive search over nonrectangular
subsets is claimed.

The [all-candidate factor check](conway/all-factor-primes.json) also builds the
407 distinct multiplicative-order factor primes from all 821 available source
rows, including the 39-bit prime 502628805631. The target completes successfully
in 11.36 seconds with warmed unchanged factor shards (maximum child RSS
872592 KiB). This verifies the actual large-factor API path; it is an incremental
factor-only check, not a complete Conway rebuild or accepted coverage claim.
To reproduce it, form a scope from every `(p,n)` in `candidates.json`, regenerate
with that `--scope`, build `HexConway.PrimeFactors`, then regenerate the accepted
scope. The recorded hashes identify the generated factor modules.

## Reproducibility and source conformance

The expansion input is `scripts/conway/candidates.json`: 821 available rows
(the 820-entry envelope plus binary degree 64), with `(2,128)` explicitly
listed as unavailable. The imported source is
[Lübeck's CPimport.txt](https://www.math.rwth-aachen.de/~Frank.Luebeck/data/ConwayPol/CPimport.txt),
SHA-256 `fb8938b43c1a988c70ed1638a31bb86f571a7af363852513e839b4f172b2f108`.
Coefficients are ascending. The existing 186-row shared Lübeck cache is
unchanged, preserving its factorization-corpus consumer and benchmark inputs.

The offline generator emits coefficient tables, literals, Rabin certificates,
factorizations and prime certificates, primitivity and compatibility proofs,
supported-entry APIs, `HexGFq` instances, Mathlib order and embedding
specializations, and
a compiled all-entry replay driver. It validates the exact divisor-closed scope
and preserves baseline support. Generation also checks coefficient agreement
with the shared factorization corpus on every overlapping key. Ordinary builds do not fetch data or search for
factorizations or certificates. Irreducibility, primitivity and compatibility
do not prove lexicographic minimality; the polynomial choice is imported.

The [Python preflight](conway/preflight.json) checks all 821 source candidates,
including factorization, power conditions, norm compatibility and agreement
with the shared cache. It is preparation evidence, **not Lean certification**
of unselected entries. Source conformance requires exactly the selected scope:
missing, extra and duplicate emitted rows fail, in addition to coefficient
mismatches.

```sh
python3 -m venv .venv-conway
.venv-conway/bin/pip install -r scripts/conway/requirements.txt
.venv-conway/bin/python scripts/conway/generate.py --check
LEAN_NUM_THREADS=8 lake build HexConway
python3 scripts/conway/measure.py accepted --ceiling 300
LEAN_NUM_THREADS=8 lake build HexGFqMathlib
python3 scripts/conway/measure.py accepted-bridge --companion
```

`--scope` accepts an explicit candidate pair list for regeneration. It does not
change `scope.json`: copy the measured input there before invoking the measurement
script so the report records the actual scope. Regenerate and verify the accepted
scope again after experiments. Network refresh is a separate explicit operation,
`scripts/conway/import_source.py`.

`scripts/conway/verify_provenance.py` checks recorded source and dependency
hashes against the recorded or explicitly selected commit. It also checks a
referenced scientific artifact, and `--binary` verifies a locally rebuilt
benchmark binary. Historical reports retain their recorded source sets; the
verifier does not invent missing historical dependency evidence. The initial
`final-594` import manifest predates meta-import scanning; `accepted-594` records
the complete local import closure. The committed Python regression checks cover
meta imports, shared-cache divergence, duplicate scope keys and hash mismatches.

```sh
python3 scripts/conway/verify_provenance.py \
  reports/conway/accepted-594.json reports/conway/accepted-594-bridge.json
```

## Additional field and Mathlib build cost

The [full companion measurements](conway/accepted-594-bridge.json) remove all
`HexGFq` and `HexGFqMathlib` outputs and explicitly build both complete umbrellas,
retaining Conway and external dependencies. This includes field instances,
generic field proofs, the packed-field bridge, generator orders, subfield
soundness, and every generated embedding. No Conway proof obligation is moved
into this measurement to satisfy the Conway ceiling.

| Run | Wall seconds | Peak tree RSS GiB | Outputs MiB |
|---|---:|---:|---:|
| 1 | 20.525 | 9.88 | 31.22 |
| 2 | 21.533 | 9.88 | 31.22 |
| 3 | 21.027 | 9.87 | 31.22 |

The [preceding expanded companion measurements](conway/quartic-300-bridge.json)
take 24.830, 22.698 and 22.574 seconds with the digit-list transport.

The [original companion observations](conway/baseline-bridge.json) were
13.602, 12.298 and 12.602 seconds, but cleaned only `HexGFqMathlib` and targeted
`Primitivity` and `Subfield`. They exclude rebuilding `HexGFq` and the full
umbrella, so subtracting them from the expanded full-companion measurements
would not be a controlled estimate of marginal cost. The new measurements
report the entire additional user-facing build instead.

## Hosted CI observations

[CI run 34135441514](https://github.com/kim-em/hex-dev/actions/runs/34135441514)
passes the complete job: build, generation, compiled replay, conformance,
manual, benchmark verification and oracles. Its single Ubuntu runner is
`runnervmejwal`, an Intel Xeon Platinum 8573C with about 15.6 GiB RAM,
Lean 4.34.0-rc2 and four measurement threads.

| Target / raw evidence | Wall seconds | Peak summed RSS GiB | Outputs MiB |
|---|---:|---:|---:|
| [Conway](conway/ci/34135441514/ci-conway.json) | 392.196 | 9.90 | 177.70 |
| [Companion](conway/ci/34135441514/ci-bridge.json) | 27.161 | 6.86 | 28.94 |

Neither timed build rebuilds an external dependency. The accompanying
[compiled replay](conway/ci/34135441514/ci-runtime.jsonl) checks all 594 entries
and 522 compatibility pairs. The [run record](conway/ci/34135441514/run.json)
retains source identity and original download hashes;
[job metadata](conway/ci/34135441514/jobs.json) records the complete CI timings.

This observation uses the same direct-exponent checker and scope, before the
meta-import scanner and report-only dirty-flag corrections. The original
companion dirty flag includes the preceding Conway timing files; source hashes
match the recorded revision. The finalized CI warms all external imports,
measures each initial clean build once, and reuses its outputs for subsequent
targets. A 1800-second limit and conservative 14-GiB summed-RSS guard bound each
hosted measurement. Summed RSS can count shared mappings more than once; it is
not an exact physical-memory limit. The 300-second acceptance ceiling belongs
to the designated machine, not these hosted observations.

## Compiled runtime evidence

The advertised Phase-4 families remain `tier1-committed-table` and
`tier2-divisor-compatibility`. Runtime measurements are distinct from Lean
elaboration and kernel replay. The all-entry replay driver checks irreducibility,
primitivity, and all proper-divisor compatibilities for every supported entry,
using mutable polynomial inputs to prevent compile-time evaluation. With
`HEXCONWAY_ENFORCE_BUDGETS=1`, its operation ceilings are 2 ms for irreducibility,
5 ms for primitivity, and 5 ms for an entry's aggregate compatibility obligations.
Hosted CI checks values and records times without asserting these machine-specific
runtime ceilings.

The [five final replay passes](conway/runtime-final-594.json) use one runtime
thread and CPU 21 affinity. They cover every selected
entry and all 522 compatibility obligations, with exact emitted-key coverage
checked on every pass. Maxima over these passes are:

| Operation | Entry at maximum | Maximum | Ceiling |
|---|---|---:|---:|
| Irreducibility | `C(7,8)` | 0.293 ms | 2 ms |
| Primitivity | `C(2,16)` | 1.086 ms | 5 ms |
| Aggregate compatibility | `C(2,16)` | 2.440 ms | 5 ms |

The [preceding replay measurements](conway/runtime-594.json) retain the earlier
digit-list driver and its source/binary identities.

The development replay executable is built separately from the library target.
Splitting its generated `main` into functions of 24 entries reduces its Lean
module compilation from 151 seconds to 8.5 seconds; C compilation takes another
1.7 seconds and linking 0.571 seconds in that incremental build. This is
benchmark-driver build cost, not certificate kernel replay. The complete field
and Mathlib rebuild measurements remain separate above.

The fixture emitter writes 594 records and corresponding results. The source
oracle passes 1188 coefficient comparisons against the pinned input and
`conway-polynomials` 0.10. Lean conformance for Conway, generic fields and
primality, the Mathlib bridge build, the manual chapter, and all 14 deterministic
LeanBench verification registrations also pass.

The initial [unpinned full scientific run](bench-results/hex-conway-594-unpinned-chungus2.json)
is retained as a failed measurement: lookup is inconclusive (`cMin=59.347`,
`cMax=120.196`, `beta=+0.322`), and one fixed binary-irreducibility child reports
an error. It is not counted as passing evidence. Repeats of identical lookup
inputs vary substantially: ordinal 16 ranges from 1068 to 1817 ns across its
five trials. A [CPU-load sample](conway/runtime-cpu-selection.json) selects
idle physical core 21 (SMT sibling 69), and subsequent runtime measurements
inherit affinity to CPU 21. This pins execution but does not reserve the core
against unrelated users. The [pinned diagnostic repeats](conway/lookup-pinned-probe-594.json)
range from 1066 to 1084 ns at ordinal 16 and 308 to 313 ns at ordinal 594.
No runtime budget or lookup implementation is changed to accommodate the
initial inconclusive result. Proof rebuilds retain the eight-thread protocol
specified above; CPU affinity is a separate runtime-benchmark control.

The [pinned full run with the default runtime thread count](bench-results/hex-conway-594-pinned-chungus2.json)
passes every fixed operation ceiling, but its lookup fit remains inconclusive
(`cMin=60.635`, `cMax=108.092`, `beta=+0.201`). It too is retained without
counting the lookup as passing. Fixing `LEAN_NUM_THREADS=1` in addition to
CPU affinity gives a [passing diagnostic ladder](conway/lookup-single-thread-probe.json)
on binary degrees 1, 2, 4, 8 and 16, with five trials each (`cMin=61.669`,
`cMax=63.697`, `beta=-0.002`). The full scientific command uses these explicit
runtime controls; no system governor, other process, or global CPU setting
is changed.

### Accepted scientific run

The [final controlled scientific run](bench-results/hex-conway-594-8a37daf-chungus2.json)
uses the rebased LeanBench revision `8a37daf`, `LEAN_NUM_THREADS=1` and CPU 21
affinity on chungus2. All 594 lookup keys have five successful trials (2970
observations); the fit is consistent with `degree + 2`
(`cMin=80.872`, `cMax=112.811`, `beta=+0.058`).
Every fixed repeat succeeds, all expected hashes match, and no operation ceiling
is exceeded. [Source, dependency and binary identities](conway/scientific-final-594.json)
record the final executable and its inputs. The preceding
[passing scientific reference](bench-results/hex-conway-594-chungus2.json)
uses LeanBench `b583ddd` (`cMin=59.811`, `cMax=65.366`, `beta=-0.002`);
its [original source record](conway/scientific-594.json) remains available.
The final run is repeated after the framework update, without changing the
lookup implementation, complexity model or operation ceilings.

```sh
LEAN_NUM_THREADS=1 HEXCONWAY_ENFORCE_BUDGETS=1 taskset -c 21 \
  .lake/build/bin/hexconway_bench run --filter Hex.ConwayBench \
  --outer-trials 5 \
  --export-file reports/bench-results/hex-conway-594-8a37daf-chungus2.json
python3 scripts/conway/verify_provenance.py \
  reports/conway/scientific-final-594.json --binary .lake/build/bin/hexconway_bench
```

| Fixed target suffix | Median µs | Maximum µs |
|---|---:|---:|
| `runIrreducibility_2_16` | 215.810 | 222.142 |
| `runTier2Compat_2_3_6Checksum` | 41.211 | 41.566 |
| `runTier1Irreducibility_11_6Checksum` | 178.581 | 179.232 |
| `runTier2Compat_13_1_6Checksum` | 119.730 | 121.040 |
| `runConwayPolySupported_2_1Checksum` | 0.141 | 0.144 |
| `runTier1Irreducibility_2_6Checksum` | 29.558 | 30.330 |
| `runTier1Irreducibility_5_6Checksum` | 105.992 | 106.619 |
| `runCompat_2_1_16` | 625.633 | 650.084 |
| `runTier1Irreducibility_2_1Checksum` | 2.399 | 2.478 |
| `runTier2Compat_2_4_8Checksum` | 50.399 | 51.301 |
| `runTier1Irreducibility_7_6Checksum` | 93.907 | 97.132 |
| `runTier1Irreducibility_3_6Checksum` | 38.032 | 39.741 |
| `runTier1Irreducibility_13_6Checksum` | 128.279 | 135.678 |

The lookup registration derives its exact key schedule from `supportedPairs`.
Its mode-1 model is `degree + 2`, accounting for coefficient materialization and
checksum traversal. Retained fixed registrations check expected hashes; the
`C(13,6)` and binary degree-16 registrations additionally enforce operation
budgets. Fixed runtime budgets do not establish asymptotic scaling.

The [historical 38-entry report](hex-conway-performance-38.md) preserves the
original mode-selection experiments and profiles, including source commits and
raw artifact links. Those profiles describe the original implementation and
are not claimed as coverage or timings for the expanded table. Lübeck's table
and the optional package adapter are input sources, not performance comparators.
