# Structured nauty search

The structured engine passes the spike criteria on the fixture, campaign,
and cactus corpora. Phase B can use its node/sweep recursion. It is imported
by the library umbrella for conformance and benchmarks, while the public
answer and certificate producer continue to call the literal search.

The engine has one flat search record, reusable permutation scratch, two
fuel-recursive functions, and explicit unwind payloads. Its correspondence
table covers every line of `nauty.c:468-513` and `559-1086`. The code-1
admission condition is nauty 2.9.3's condition, without the literal port's
additional sentinel test. There are no proofs, `sorry`, `axiom`, or
`partial` declarations in the engine. Phase B must justify the first-leaf
scatter admitted when `gcaFirst >= noncheaplevel` using the cheap-automorphism
subtree theorem. The literal proof instead obtains an explicit successful
`isautom` test. Conformance does not discharge that proof obligation.

## Conformance

The twin compares labels, canonical rows, all seven statistics, accepted
automorphisms in discovery order, canonical path codes, final orbits, and
normal root termination. The existing CI job runs this full twin corpus.
Both external oracle runs use the emitters'
`--engine` mode, so their canonical labels, forms, and node counts come
from the engine independently of the literal search.

```text
twin: fixtures agree over 6028 cases
twin: autos agree over 205 cases
twin: campaign agree over 32798 cases
graphiso oracle: 6233 cases checked against nauty 2.9.3 (205 automorphism-group cases)
graphiso oracle: 32798 cases checked against nauty 2.9.3 (0 automorphism-group cases)
```

The conformance guards also exercise code-1 admission without the next
sentinel, workspace overwrite at 500 pairs, code 2 with unchanged orbits, code 2 returning through a smaller
coset representative, fuel exhaustion, and empty input.

Local builds pass for `HexGraphIso`, `HexGraphIsoMathlib`,
`HexGraphIso.TacticTests`, `HexGraphIso.Conformance`, both emitters, the
twin executable, the cactus executable, and the stage profiler.

The branch-count probe in `scripts/bench/graphiso_admissions.c` wraps the
compiled classifier without changing the search. Both instrumented emitter
streams also pass the external oracle. Its counts are:

| corpus | cases | off-path classifications | code-1 admissions | cheap short-circuit | next code not sentinel |
|---|---|---|---|---|---|
| fixtures and automorphism cases | 6,233 | 4,128 | 3,164 | 3,072 | 0 |
| campaign | 32,798 | 56,040 | 40,247 | 39,889 | 0 |

Thus the corpora exercise 42,961 admissions that skip `isautom`. They do
not exercise an admission where the next first-path code is not the
sentinel. The explicit guard checks that latter decision on a constructed
state, not on a graph traversal exhibiting a refinement-code collision.
The twin checks normal root termination over the entire corpus. The two
zero-fuel guards only check that the exhausted base cases are distinguishable.

## Timing

Measurements use `leanprover/lean4:v4.34.0-rc2` on chungus2. Each cactus
entry uses the driver's warmup and minimum-of-five timing. Three complete
98-instance comparisons run on CPU 91. The table uses the per-instance
median of each timing column across those three trials. All raw trials
are committed alongside the median and its metadata under
`reports/bench-results/hexgraphiso-engine-ddc22cf4b645-chungus2*`.

The largest family geometric mean is 0.99963, the largest individual ratio
is 1.01600, and the largest engine-minus-literal exponent is 0.00964.
The recorded median passes the default bounds without increasing the
allowed family mean. A ratio of 0.99963 is statistically indistinguishable
from 1.00 here: Paley's family mean across the raw trials ranges from
0.99906 to 1.00272. The substantive conclusion is no regression within
the noise of this run. The driver always times the literal first, which
is a possible source of order bias despite each call's warmup. Every instance has identical node counts. The anticipated
ratios below 0.9 on Kneser, Johnson, and hypercube graphs are not observed:
the gains on those families are about 1–2%. The corpus has small search
trees (one node on every random instance and at most 250 on any instance).
Both engines retain the same refinement and dense-conversion work, so
improvements to leaf admission affect only part of their total cost.

engine comparison from hexgraphiso-engine-ddc22cf4b645-chungus2.jsonl

| family | sizes | n range | eng/lit | eng/nauty | lit n^e | eng n^e | diff | worst instance |
|---|---|---|---|---|---|---|---|---|
| circulant-12 | 17 | 8–255 | 0.98 | 5.00 | 1.71 | 1.72 | 0.01 | circulant192-1-2 0.99 |
| circulant-1248 | 12 | 17–225 | 0.97 | 4.94 | 1.77 | 1.78 | 0.01 | circulant17-1-2-4-8 1.00 |
| grid | 10 | 9–225 | 1.00 | 3.22 | 1.58 | 1.58 | 0.00 | grid12x12 1.01 |
| hypercube | 5 | 8–128 | 0.99 | 7.49 | 1.36 | 1.36 | 0.01 | q4 1.01 |
| johnson | 10 | 10–231 | 0.98 | 9.60 | 1.01 | 1.01 | 0.00 | johnson22-2 0.99 |
| kneser | 10 | 10–231 | 0.99 | 10.07 | 1.37 | 1.36 | -0.01 | kneser5-2 1.02 |
| latin | 3 | 25–169 | 0.97 | 7.68 | 1.82 | 1.82 | 0.01 | latin13 0.98 |
| paley | 13 | 13–229 | 1.00 | 5.05 | 1.69 | 1.69 | 0.00 | paley41 1.00 |
| random | 18 | 10–255 | 1.00 | 3.19 | 1.87 | 1.87 | 0.00 | gnp160-seed1 1.00 |

overall (geometric mean): eng/lit 0.99, eng/nauty 5.23

The engine also passes the exponent check against nauty with margin 0.2:

timing column: eng_ns

per-node cost fit from hexgraphiso-engine-ddc22cf4b645-chungus2.jsonl

| family | sizes | n range | hex n^e | nauty n^e | diff | X (n ≤ 64) | X (n > 64) |
|---|---|---|---|---|---|---|---|
| circulant-12 | 17 | 8–255 | 1.72 | 1.83 | -0.10 | 5.24 | 4.60 |
| circulant-1248 | 12 | 17–225 | 1.78 | 1.86 | -0.08 | 5.24 | 4.65 |
| grid | 10 | 9–225 | 1.58 | 1.85 | -0.27 | 3.84 | 2.47 |
| hypercube | 5 | 8–128 | 1.36 | 1.40 | -0.04 | 7.56 | 7.21 |
| johnson | 10 | 10–231 | 1.01 | 1.04 | -0.03 | 9.94 | 9.28 |
| kneser | 10 | 10–231 | 1.36 | 1.31 | 0.05 | 9.72 | 10.44 |
| latin | 3 | 25–169 | 1.82 | 1.91 | -0.09 | 8.29 | 7.39 |
| paley | 13 | 13–229 | 1.69 | 1.82 | -0.13 | 5.36 | 4.72 |
| random | 18 | 10–255 | 1.87 | 1.89 | -0.02 | 3.23 | 3.13 |

overall X (geometric mean): n ≤ 64: 5.35, n > 64: 5.07

## Allocation profile

The profiler runs 2,000 iterations each of paley61, kneser72, and
circulant64, choosing between each graph and its rotation from the running
node-count sum. Each stage reports 14,000, 36,000, and 12,000 node visits,
respectively. DHAT 3.27.1 observes 60,809,336 allocated blocks in either
stage, or 980.796 blocks per visited node. This equal-count result is a control for the shared libc/GMP work.
The discriminating allocation measurement is the mimalloc count below.

These are whole-process counts, including the common initialization and
certificate setup. DHAT's ordinary heap mode sees libc/GMP allocations
but does not intercept this toolchain's statically linked `mi_malloc`
and `mi_malloc_small` calls. Thus this comparison does not establish a
bound on all Lean object allocations. The compressed raw DHAT profiles
and complete logs are committed alongside the timings. The [Valgrind
manual](https://valgrind.org/docs/manual/manual-core-adv.html) describes
this limitation of heap tools with custom allocators.

The supplemental wrapper in `scripts/bench/graphiso_dhat.c` counts those
mimalloc requests through DHAT ad-hoc events, including `mi_new_n` for
C++ containers. The reproducible
`scripts/bench/graphiso_alloc_calls.py` audit finds these three allocation
entry points among direct calls from outside mimalloc. Its command and
output are recorded with the wrapper. The audit does not rule out
compiler-inlined or indirect allocation paths in other toolchains. A thread-local
nesting counter prevents double counting. The wrapper's calibration
executable performs three allocations, two through nested entry points,
and DHAT records exactly three events.

| allocation requests | literal | engine | literal per node | engine per node |
|---|---|---|---|---|
| libc/GMP (ordinary DHAT) | 60,809,336 | 60,809,336 | 980.796 | 980.796 |
| mimalloc (DHAT ad-hoc events) | 68,206,460 | 67,518,459 | 1100.104 | 1089.007 |

The measured mimalloc allocation requests decrease by about 1.01%, meeting
the allocation comparison in addition to the equal libc/GMP control. Ad-hoc events count successful allocation requests, not
allocation sizes or peak live memory. Both ordinary and supplemental
profiles include the common process setup and use the same 62,000 node
visits as denominator.

## Reproduction

```sh
lake build hexgraphiso_engine_twin hexgraphiso_emit_fixtures \
  hexgraphiso_emit_campaign hexgraphiso_cactus hexgraphiso_profile \
  HexGraphIso.Conformance HexGraphIsoMathlib HexGraphIso.TacticTests
.lake/build/bin/hexgraphiso_engine_twin
.lake/build/bin/hexgraphiso_emit_fixtures --engine | python3 scripts/oracle/graphiso_nauty.py
.lake/build/bin/hexgraphiso_emit_campaign --engine | python3 scripts/oracle/graphiso_nauty.py
taskset -c 91 .lake/build/bin/hexgraphiso_cactus engine > engine.jsonl
python3 scripts/bench/graphiso_engine_compare.py engine.jsonl --check
python3 scripts/bench/graphiso_pernode_fit.py --sweep engine.jsonl --column eng_ns --check 0.2
valgrind --tool=dhat --dhat-out-file=run.json .lake/build/bin/hexgraphiso_profile run
valgrind --tool=dhat --dhat-out-file=erun.json .lake/build/bin/hexgraphiso_profile erun
cc -shared -fPIC -O2 $(pkg-config --cflags valgrind) \
  scripts/bench/graphiso_dhat.c -o /tmp/graphiso_dhat.so
LD_PRELOAD=/tmp/graphiso_dhat.so valgrind --tool=dhat --mode=ad-hoc \
  --dhat-out-file=mi-run.json .lake/build/bin/hexgraphiso_profile run
LD_PRELOAD=/tmp/graphiso_dhat.so valgrind --tool=dhat --mode=ad-hoc \
  --dhat-out-file=mi-erun.json .lake/build/bin/hexgraphiso_profile erun
python3 scripts/bench/graphiso_alloc_calls.py .lake/build/bin/hexgraphiso_profile
cc -shared -fPIC -O2 -I"$(lean --print-prefix)/include" \
  $(pkg-config --cflags valgrind) scripts/bench/graphiso_admissions.c -o /tmp/admissions.so
LD_PRELOAD=/tmp/admissions.so valgrind --tool=none \
  .lake/build/bin/hexgraphiso_emit_fixtures --engine > /dev/null
LD_PRELOAD=/tmp/admissions.so valgrind --tool=none \
  .lake/build/bin/hexgraphiso_emit_campaign --engine > /dev/null
scripts/bench/graphiso_cactus_sweep.sh issue-10041
python3 scripts/bench/check_graphiso_sweep_freshness.py
python3 scripts/bench/graphiso_pernode_fit.py --check 0.2
```

The required public-pipeline sweep, pairs, tactic timings, manifest, metadata,
and regenerated figures are committed for source fingerprint
`ddc22cf4b645`. Its freshness and per-node exponent checks pass.
