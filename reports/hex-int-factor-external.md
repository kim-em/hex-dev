# Optional external integer factorization

The frozen corpus has five complete and two partial checked results. Cases 0,
3 and 4 complete after GP discovery while the recorded native worklist allocation
of four exhausts. Cases 1 and 2 complete natively at four but exhaust at one;
these native successes are retained. Case 5 is `2^255 - 19`: discovery succeeds,
but its supported `PrimeCert` construction exhausts 128 attempts and leaves the
whole subject as a checked residual. Case 6 disables completion with zero
attempts and retains both discovered bases as unresolved hints.

## Inputs and allocations

[The committed plan](hex-int-factor-external-plan.json) fixes every subject,
seed 1729, both native worklist allocations (4 and 1), the separate 128-attempt
per-base completion budget, the optional ECM retry sharing those attempts, and
the 30-second GP allocation. It was committed before these experiments.
Stage 2 and SQUFOF are off. Native nested prime fuel is capped by the remaining
worklist allocation. GP 2.17.3 runs with one thread and a fixed 64 MB stack.
The producer admits at most 256 bits; it does not promise general 60-digit
factorization or primality-certificate completion.

[All stage observations](hex-int-factor-external.json) retain the complete
corpus, native successes/exhaustions, GP output, unresolved obligations and
source/replay outcomes. The initial measurement-support elaboration error is
retained separately in [the setup failure](hex-int-factor-external-setup-failure.json);
no subject was measured in that failed preparation. The collection command is
`python3 scripts/bench/intfactor_external.py --gp /path/to/gp`. It selects and
leases one CPU without an idle-host preflight. Host, load, CPU and plan hash
are in the record. There are no discarded completed samples or repeated trials.
This is one capability observation per fixed subject, not a statistical
comparison of implementations.

## Results and costs

| Case | Bits | Native fuel 4 | Native fuel 1 | GP ms | Completion ms | Compiled check µs | Accepted | Source bytes | Fresh replay s |
| --- | ---: | --- | --- | ---: | ---: | ---: | --- | ---: | ---: |
| 0 | 110 | exhausted | exhausted | 33.90 | 0.220 | 31.54 | complete | 790 | 1.250 |
| 1 | 111 | complete | exhausted | 34.06 | 0.340 | 34.79 | complete | 869 | 1.249 |
| 2 | 125 | complete | exhausted | 59.65 | 0.375 | 52.21 | complete | 925 | 1.251 |
| 3 | 235 | exhausted | exhausted | 936.30 | 0.691 | 55.95 | complete | 1233 | 1.255 |
| 4 | 202 | exhausted | exhausted | 335.84 | 0.463 | 43.98 | complete | 1204 | 1.248 |
| 5 | 255 | exhausted | exhausted | 33.66 | 488.554 | 12.35 | partial | 590 | 1.264 |
| 6 | 40 | complete | exhausted | 34.14 | 0.021 | 8.80 | partial | 398 | 1.267 |

The GP interval includes process startup, discovery, bounded output collection
and the producer's 25 ms polling cadence. Parsing takes approximately 0.02–0.06
ms on this corpus. Completion includes arithmetic preflight/canonicalization;
compiled acceptance is timed separately. Export validates the actual acceptance
proof and formats literal source in approximately 0.4–4.4 ms. Fresh replay is a
new module build and includes Lake startup, import loading, elaboration and
checking; it is not a measurement of checker reduction alone. Every replay
succeeds with GP unavailable.

Cases 0–4 use certifiable 50-, 61- and 64-bit bases, some with smooth predecessor
factorizations. Their helpful shape explains cheap primality completion after
discovery. Case 5 demonstrates why larger discovered probable primes need not
be certifiable within the current language/allocation. No ECPP evidence is
embedded or trusted.

## Verification and publication

`HexIntFactorTests` builds parser/import/fallback coverage, exact complete and
partial `#guard_msgs` source text, and all seven frozen modules. The existing
integer-factor oracle consumes the frozen corpus and checks primality and exact
products independently. The local [independent check](hex-int-factor-external-oracle.json)
uses python-flint 0.9.0 primality and Python exact products for all seven results. `scripts/ci/check_intfactor_pari.py --gp /path/to/gp`
checks actual small-GP production, exact suggested source, complete/partial
fresh replay, subject-substitution rejection, opaque-data rejection, exclusive
creation and editor gating. Replay proofs depend only on core `propext`; no
`native_decide`, new axiom, search proof or producer proof is involved.

[The fresh split client](hex-int-factor-external-split.json) uses publication
source/settings transforms and staged upstream prerequisites, with no Mathlib
or project build cache. HexIntFactor is not yet listed in `released.yml`, so its
skeleton and `build_modules`/`test_modules` entry are prospective; upstream
HexBasic, HexArith and HexPrimality use actual published skeletons. A release
regression checks that optional modules, tests and frozen data remain managed.
Adding a published repository is separate release work.

The new `external-production-and-import` Phase-4 family separates discovery,
parsing, completion, acceptance and replay. Pure validation bounds input/cert
traversal before arithmetic/checking; sorting costs `O(k log k)` comparisons
and certificate traversal is linear in the admitted syntax. Construction and
fallback are finite searches with separately charged attempts, not total
factorization algorithms. The source ceiling, finite allocations and retained
exhaustion outcomes define the support boundary. Phase 1/2 are owned by the
SPEC-assigned modules and existing checkers; Phase 3/7 are covered by the
conformance, oracle, manual and fresh replay checks described above.
