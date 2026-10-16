# Complete OrderedFn computational comparison

The integrated candidate completes the retained 17-family, eight-parameter,
three-trial baseline comparison: **816 arms, 136 parameter comparisons, no failed
arms and no regressions** under the unchanged independent-arm-median rule.
All result hashes agree within each parameter, including across trials. The
largest observed increase is `provider@8388608`, +3.532682%; the guard flags
only a change strictly greater than 10%. It records 67 improvements and 69
stable parameters. These are observations on the recorded shared host.

## Sources and baseline selection

| Arm | Unmodified source | Compiler | Executable SHA-256 |
| --- | --- | --- | --- |
| Historical | `ee490f54889e2db8170c8b9fc6e8568f8a978bbe` | Lean 4.34.1 | `24b1b5138cc6ef75b990ee5f7580709268fc35ad35fce2df360650eeb715be34` |
| Integrated | `b4e1e1522a81b09205ff792f8b1d0dc650a63e37` | Lean 4.35.0-rc3 | `19a7750209804b74ea3ea0d480b6aebedfe1b4bd4c6eb7d3b4dcdc90f1592c8f` |

The historical arm is a fresh build of the original committed baseline source
against exactly its sixteen pinned requirements, with isolated package and build
directories. It binds 4,794 source/configuration inputs and 87 native import files.
Its executable differs from retained `ac7a257a18ed50b1c190004223c042498c846aafef6427b57dc33d9a91ec6af7`.
The pre-timing proposal selected this complete fresh source build regardless of
byte identity, before any performance observations. This reconstructs the same
unmodified historical source; it does not recover unrecorded original build
inputs or replace the original artifact or captures. No comparison between
baseline executables was used to choose the passing result.

The integrated arm has 5,164 bound inputs, 89 native import files and sixteen
clean pinned requirements. Its separate reconstruction reproduces the measured
[combined sign/scan candidate](../ordered-fn-sign-scan/README.md) byte-for-byte.
That source includes the merged [positive quotient bounds](../ordered-fn-positive-quotient/README.md)
and the combined storage/shared-zero sign changes. Both compiler replacements
have whole-function kernel proofs. The native import paths remain Mathlib- and
Tau-Ceti-free; mathematical companions are outside these native executables.

Separately captured before/after build inventories agree. The source manifests
also bind generated C and pinned Lean/Lake executable hashes. The native
benchmark bodies, inputs and registrations differ only in six comments between
the historical and integrated sources; the retained reconciliation records the
existing lexer and both source hashes. This is a whole pinned-source/toolchain
comparison, without causal attribution solely to API edits or either optimization.

## Complete scope and method

The original committed follow-up schedule is preserved byte-for-byte:

| Families | Eight parameters | Target inner work |
| --- | --- | --- |
| scan, second, third, comparison, degree, height | 128 through 16384, doubling | 1 s |
| subtraction | 128 through 16384, doubling | 4 s |
| denominators | 16 through 2048, doubling | 1 s |
| compareHeight, realHeight, provider | 65536 through 8388608, doubling | 1 s |
| refinement, jointRefinement, approximation | 8192, 10240, 12288, 14336, 16384, 20480, 24576, 28672 | 1 s |
| horner | Same eight search parameters | 4 s |
| successiveApproximation, thirdApproximation | 4, 6, 8, 10, 12, 14, 16, 18 | 4 s |

Three trial-major adjacent source pairs use AB/BA/AB order, one automatically
leased CPU and `LEAN_NUM_THREADS=4`. The parent records successful affinity
selection and the same final affinity. Profiling and sidecar environment switches
are unset symmetrically for the ordinary timed loop. Host load and memory context
are retained without a quiet-core condition or rejected samples. Each raw filename
includes trial, family, parameter and arm. Every completed observation is retained.
Individual child failures would remain in the full schedule; interruptions would
stop and consume the attempt. The 180-second parent timeout and process-group
cleanup are operational safeguards, not scientific budgets.

The account-global attempt is keyed by the frozen historical/candidate source
pair. Changing binary bytes, output names or decision wording cannot create
another attempt for this pair. The consumed reservation is retained with the
exact decision digest and output binding. No unchanged repeat is authorized by
this comparison. The unmeasured first protocol, its review-driven corrections,
setup failures and repairs remain in the archive; they are not omitted samples.
Synthetic execution controls check the actual collector's complete 816-arm path,
failed-arm retention, lease ordering and stable reservation. Their fake rows are
not performance evidence.

The analyzer is byte-identical to the committed
[follow-up analyzer](../ordered-fn-regression-followup/analyze_guard.py), including
its `improvement_count` reporting. It uses each arm's median of three observations
and the pinned LeanBench default 10% arithmetic. Paired ratios are descriptive
only. Raw child outputs lack runner signal-floor/verdict eligibility; this check
does not reconstruct that machinery or supply a new Phase-4 scaling verdict.
Existing model derivations and owner scaling/comparator evidence remain separately
scoped. A theorem-application timing or successful smoke run is not used here.

## Relation to retained findings

All observations and verdicts in the [original capture](../ordered-fn-api-regression/README.md)
and its [single unchanged follow-up](../ordered-fn-regression-followup/README.md)
remain intact. The old findings were not reclassified as noise or discarded.
This comparison changes the implementation and uses the explicitly selected
fresh build of the historical source; it is not another unchanged repeat.
For the four follow-up findings, the new source-pair observations are:

| Workload | Parameter | Fresh historical median ns/call | Integrated median ns/call | Change |
| --- | ---: | ---: | ---: | ---: |
| height | 128 | 66.754887 | 57.492177 | −13.875703% |
| height | 2048 | 66.901749 | 57.619720 | −13.874120% |
| third | 1024 | 62,532.911743 | 1,158.027502 | −98.148131% |
| approximation | 12288 | 4,358,021,359 | 2,950,159,626 | −32.305067% |

The original capture's separate `approximation@10240` finding is included in the
same complete passing 136-parameter comparison. The third-level gain remains
specific to the shared-padding specialization described in the sign/scan report;
it does not establish generic unshared-zero fallback performance. The full
comparison also includes comparison and subtraction, alongside every other
retained family. No uniform multivariate precision/depth claim is added.

## Retained evidence and offline replay

The manifest binds 1,690 compressed and original files: all 1,632 raw streams,
all observations and host context, frozen source/SDK/generated-code inventories,
proposal/decision/schedule, consumed reservation, producer and analyzer scripts,
validation controls, preparation records and the complete native comparison.
Executable binaries are not committed. No new timings are collected by replay:

```sh
python3 reports/bench-results/ordered-fn-final-comparison/replay.py
```

Replay checks every archive binding and the complete schedule, reconstructs the
retained data in a temporary directory, applies the unchanged committed analyzer
and compares every derived field with the retained result. It also checks source,
SDK, executable, generated-code, script, pre-timing decision and reservation
bindings, recorded affinity/thread selection, commands, compiler identities and
cross-trial answer hashes. The hash-bound collector checks live source inputs on
exit; replay does not recover the measurement host's final filesystem.

To additionally compare current native input and build-configuration bytes with
the measured candidate (requiring its dependency checkouts):

```sh
python3 reports/bench-results/ordered-fn-final-comparison/replay.py --current
```

The retained corruption, missing-row, altered-verdict, affinity and reservation
controls run against temporary copies, without executing native benchmarks:

```sh
python3 reports/bench-results/ordered-fn-final-comparison/test_replay.py
```

That optional check intentionally refuses later changes to those inputs. The
complete comparison passes for its measured source. Final phase acceptance also
requires the library's proof/API, import, kernel, conformance and manual checks;
this report alone changes no library or publication counter.
