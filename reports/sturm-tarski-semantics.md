# Sturm–Tarski semantic replay proof costs

The semantic replay module checks rational, noncanonical-representation, and
integer/dyadic certificates against the proved shared root-sum theorem. Its
ordinary-kernel axiom guards require only `propext`, `Classical.choice`, and
`Quot.sound` for the semantic results and their query/count consequences.

## Method

[`sturm_semantics_sweep.py`](../scripts/bench/sturm_semantics_sweep.py) rebuilds
`HexSturmMathlib.Replay.Semantics` and an import-only module with the same six
imports. Dependencies are built before measurement. Each arm removes only its
own generated module artifacts and runs `lake build +<module>:olean`.
The wall times therefore include Lake startup, import loading, elaboration,
kernel checking, and axiom auditing with the foundation already compiled.

Four adjacent pairs use the fixed order AB/BA/AB/BA, where A is the import-only
reference and B is the semantic replay module. The shared-host runner pins both
arms to automatically selected CPU 2 on `chungus2` (AMD EPYC 9455), with one Lean
thread. All four pairs are retained; host activity and source hashes accompany
the raw data. The runner also writes each completed arm to an incremental
sidecar before checking the pair's diagnostics.

The measured source is `837de0f7346418d9cd3184202911250d7303af10`, using Lean
4.35.0-rc3, Mathlib `d870b9068518a0870842d15a0cd42637ec30b587`, and merged Tau Ceti
`ff72a2e86930d5268476ee33d55ab054ed1c3ea5`. Repository and dependency checkouts
were clean.

## Observations

| Pair | Order | Import-only (s) | Semantic replay (s) | Paired difference (s) |
|---|---|---:|---:|---:|
| 1 | AB | 6.937 | 7.182 | 0.245 |
| 2 | BA | 6.937 | 7.150 | 0.213 |
| 3 | AB | 6.946 | 7.184 | 0.238 |
| 4 | BA | 6.925 | 7.246 | 0.320 |

Median wall times are 6.937 s for the reference and
7.183 s for semantic replay. The median of the paired differences is
0.241 s. These are observations on this host for this fixed degree-two
probe, including its theorem applications and axiom audits.
The semantic module's `.olean` is 40,568 bytes and its
`.olean.private` is 110,224 bytes.

Every build and semantic axiom guard passed. Both build logs also replay the
imported `Accepted` module's axiom diagnostics; the harness expects those same
three ordinary axioms in both arms.

## Records

- [Complete measurement](bench-results/hex-sturm-semantics-837de0f73464-chungus2.json), including compiler output,
  dependency revisions, source hashes, memory use, and host activity.
- [Incremental arm records](bench-results/hex-sturm-semantics-837de0f73464-chungus2.json.samples.jsonl).
- [Failed harness run](bench-results/hex-sturm-semantics-6573d4872-failed.log):
  an axiom-output expectation failed after one pair; the harness had not written
  its timing data. This diagnostic record supplies no numerical observations
  for the table above.
