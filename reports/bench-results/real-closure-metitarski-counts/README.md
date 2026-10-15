# MetiTarski native producer counters

This is one untimed diagnostic of the complete second-stage producer for
`Yⁿ + α³ + 1`, at degrees 3, 5, 7 and 9. Here α is the selected least real
root of the original degree-15 MetiTarski polynomial. Degree three is the
paper example; the other degrees are a derived family. The ordinary and
instrumented executables reproduce all four committed functional packets
byte for byte. The retained FLINT qqbar oracle outputs independently check
the original polynomials, selected embedding, unique root and multiplicity.

The measured source is
`bff9b56cb6f222df142433a351409c0fd046c969`, published as
`measurements/10378/metitarski-counters-source-v1`. The capture uses Lean
4.35.0-rc3 and python-flint 0.9.0 / FLINT 3.6.0. Its manifest retains all
dependency pins, host activity, automatically leased CPU 46, command limits,
exit statuses and operational elapsed times. Those elapsed times are not
scientific timing samples. All 20 commands completed; no attempt was retried.

## Counter boundary and interpretation

The region begins immediately before reading the prepared runtime input and
ends after the first complete second-stage root producer returns a singleton.
It includes the producer's internal validation. Constructing/selecting the
degree-15 predecessor and building the second polynomial occur before the
region; explicit final equation/replay checks and serialization occur after
it. There is no explicit second-stage warm-up. This differs from the
historical timing runner's boundary and warm-up, so these counts cannot be
attached to its timed batches or used to explain a timing ratio numerically.

Counters select generated-C workers by their declaration names, before
specialization suffixes. Forwarders, boxed wrappers and lambda wrappers are
excluded. Loop counters sit after the tail-recursion label and include the
terminal test. They are selected worker entries/tests, rather than complete
field-operation counts. In particular, `algebraic_sign_poly` includes constant,
interval and prepared-query dispatch; each entry need not perform an expensive
sign determination. The implementation retains each of the 23 instrumented
modules and every selected function name.
Lean compiler inlining can remove a worker entry at an inlined call site;
these counts therefore need not include all source-level executions.

The native observer also wraps Lean natural gcd, GMP gcd and GMP gcdext. A
wrapped call forwards its arguments exactly once. Lean and GMP are distinct,
nested observation layers: **do not add their totals**. Polynomial entry and
loop categories also overlap. These counters do not measure integer bit
sizes, every coefficient operation, evidence bytes or all Phase 4 cost sites.

## What this resolves

The selected outer polynomial gcd entries, Euclidean loop tests, Yun loop
tests, signed-chain entries/tests and BKR entries stay constant on this ladder.
No bisection node is visited. Algebraic `signPoly` dispatch and both integer
gcd observation layers increase. This directs further investigation toward
work inside the selected coefficient field and its rational arithmetic.
The Lean and GMP gcd totals coincide at all four degrees; they are redundant
observations here, rather than independent corroboration.

An independent algebraic observation explains why a degree-linear initial
Euclidean chain is not available as a justification for this particular family.
Writing `c = α³ + 1`, the retained predecessor interval lies in `(-1,0)`, so
`0 < c < 1`. For `p = Yⁿ+c`,
`p′ = nYⁿ⁻¹` and `p - (Y/n)p′ = c`. Thus the nonzero remainder degrees are
`n, n−1, 0`, followed by zero. Its squarefree Yun step emits `p` at multiplicity
one, then terminates on the next degree-zero test. The first root bound is
2, the odd binomial has one root in `(-2,2)`, and singleton completion uses
an empty derivative-query list. This argument also independently supports the
absence of bisection; dynamically, no selected `Frontier.advance?` entry was
observed. These statements concern interpreted field
values; executing their zero/sign checks and arithmetic still has a cost.

The full producer also prepares and validates signed queries over changing
polynomials and algebraic coefficients. Neither the binomial identity nor
constant selected outer counts determine its complete field-operation or bit
complexity. This diagnostic establishes no runtime exponent or Phase 4 pass.
The previously registered `n³` model and its
[inconclusive timing capture](../real-closure-metitarski-scaling/README.md)
remain unchanged. Choosing a new model requires an independent derivation.

## Retained evidence and reproduction

`capture.tar.gz` contains every command stdout/stderr, all ordinary and
instrumented packets, oracle outputs, the original manifest, frozen driver/
observer/oracle/fixture sources, build metadata, labels and instrumented C.
`archive.json` indexes all retained members and the exact omitted snapshots.
`recipes.json` supplements this evidence with the original response file,
compiler/link traces and build configuration, collected after the capture.
At collection, every original linked object/archive and the ordinary binary
matched the identities recorded during capture. The response file also
matches its capture-time digest. Module traces had no capture-time digest;
they are supplementary matching-build evidence, not historical snapshots.
These module traces record originating compilations in sibling worktrees;
Lake's artifact cache carried them with the adopted objects. Each trace's
original source must have the same module path below `.lake/build/ir`, and
its original output must be exactly that C path plus `.o.export`. The
supplement records its collecting commit, dirty status and collection time
separately from the captured source commit.
The two executables and 24 object files are omitted; their original hashes
remain bound to the capture and build metadata. Build metadata records all
421 original object/archive link inputs and all instrumentation/compiler/link
commands. Original generated C is recovered by removing the inserted observer
declaration/calls, checked against its original hash, then instrumented again
to verify every insertion and selected function.
The verifier compares full ordered link arguments and module compiler commands
with these recipes, allowing only the recorded source/object substitutions,
observer object and four wrappers. It also checks the observer compiler command.

The 23 instrumented module recompilations use the pinned toolchain's clang.
The ordinary `Phase4` object and the final link command
use the external task-local `lean-cc` wrapper recorded in `build.json`;
that wrapper and dynamically selected system libraries were not frozen by
the capture. Their historical bytes cannot be authenticated from this archive.
The source tag, dependency pins and recorded executable/object hashes identify
the observed build; the archive does not promise bit-identical rebuilding on
another host. Full linked objects remain outside the portable archive.
The resolved `-l` library files and GMP's static/dynamic linkage are not
identified. Static linkage can expose additional internal GMP calls to the
wrapper; the GMP totals describe this executable and are not portable totals
for every GMP build. Future captures need resolved-library/link-map evidence
to distinguish those cases.

Verify the retained archive and recompute `analysis.json` and the table:

```sh
python3 scripts/bench/archive_meti_counts.py
python3 -m unittest scripts.bench.test_meti_archive
```

Verification checks archived output and provenance bindings; it does not rerun
FLINT or certify the native C instrumentation mathematically. To inspect the
members without executing the captured commands:

```sh
tar -tzf reports/bench-results/real-closure-metitarski-counts/capture.tar.gz
```

The capture runner is `scripts/bench/real_closure_meti_counts.py`. A fresh
capture requires a committed clean source tree and the pinned oracle; it is
not part of routine CI or an automatic retry of this diagnostic. Existing CI
runs the observer/selector/protocol and archive mutation checks and the
independent functional oracle in its existing single job. It exercises the
actual ordinary counts-mode degree-three packet and its two region markers.

<!-- meti-counts -->
Source: `bff9b56cb6f222df142433a351409c0fd046c969`; CPU 46; 20 commands; 23 instrumented modules; 421 original link inputs.

| degree | poly_gcd | poly_xgcd_left | gcd_loop_tests | yun_loop_tests | signed_chains | chain_loop_tests | bkr_solves | bisection_nodes | algebraic_sign_reads | algebraic_sign_poly | lean_nat_gcd | gmp_gcd |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| 3 | 19 | 17 | 65 | 2 | 69 | 969 | 1 | 0 | 100 | 935 | 448870 | 448870 |
| 5 | 19 | 17 | 65 | 2 | 69 | 969 | 1 | 0 | 104 | 1441 | 767726 | 767726 |
| 7 | 19 | 17 | 65 | 2 | 69 | 969 | 1 | 0 | 108 | 1955 | 1200769 | 1200769 |
| 9 | 19 | 17 | 65 | 2 | 69 | 969 | 1 | 0 | 112 | 2477 | 1748034 | 1748034 |

All other instrumented categories and `gmp_gcdext` are zero at every rung.
<!-- /meti-counts -->
