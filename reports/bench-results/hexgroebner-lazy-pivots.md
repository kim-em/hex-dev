# Lazy packed F₂ pivot initialization

Packed F₂ pivots initialize their private row only when dense enough to use word XOR. Sparse pivots use their existing immutable column lists. One shared native density predicate guards initialization, scans, projection and four-row tables. Tables require every byte of a dense row to initialize, including words outside its support. The accumulator initializes separately. Complete virtual scratch reservation, portable admission, exact results and all logical counters are unchanged. Allocator behaviour determines how much resident memory is saved.

The option remains disabled by default. These are ordinary F₂ polynomials, without Boolean quotient relations. Existing allocation failure and late byte-refusal costs remain; the packed-payload allowance does not bound total heap memory.

Baseline `b135e329b277`; initial lazy version `176673354ffa`; final shared-predicate version `4fb747423df0`. Each changes only the native matrix source relative to the baseline runtime manifest. Native compiler `clang version 21.1.8`, generated-C compiler `clang version 23.1.0` (SDK), compiler flags and inputs match.

## Matched observations

The initial stage retains 100 completed processes / 50 equal complete-basis pairs, and the final stage retains 104 / 52. Both have identical logical statistics. Comparisons use one leased CPU, one algorithm thread, adjacent AB then BA, degree scheduling, grevlex, batch size 1024 and complete monic reduced output. Binary pivots are enabled in both F₂ arms. Moderate cohorts use a 16 GiB packed-payload allowance; the Cyclic-9 focus uses 2⁵⁰ bytes under an 8 GiB process address-space limit. These are benchmark budgets rather than the library default of 256 MiB. All completed samples and RSS observations are retained. The final focused comparison was inconclusive, so one unchanged Cyclic-9 repeat is included; there is no further unchanged repeat.

The Cyclic-9 input also occurs in the primary fixed corpus and motivated the larger-frame work. It is an in-sample diagnostic, reported separately from the development cohorts. Process time includes initialization, parsing, candidate production, final interreduction and complete output. Certificate generation, independent native certification and kernel checking are separate.

| Stage / cohort | CPU | Process B/A | Family balanced B/A | Candidate B/A | Pair min / max | Peak RSS A / B (KiB) |
|---|---:|---:|---:|---:|---|---|
| initial / f2-true | 88 | 0.991231 | 0.991197 | 0.982001 | 0.828994 / 1.197205 | 88040 / 88020 |
| initial / prime-control | 32 | 0.996536 | 0.996536 | 0.996086 | 0.848554 / 1.227383 | 73700 / 73636 |
| initial / hard-cyclic9-f2 | 52 | 0.939719 | 0.939719 | 0.939607 | 0.891071 / 0.991023 | 913184 / 830712 |
| final / f2-true | 41 | 0.992604 | 0.994247 | 0.973956 | 0.805063 / 1.223317 | 88040 / 87332 |
| final / prime-control | 37 | 0.991450 | 0.991450 | 0.993276 | 0.846822 / 1.153700 | 73700 / 73784 |
| final / hard-cyclic9-f2 | 73 | 1.021813 | 1.021813 | 1.021902 | 0.996376 / 1.047900 | 907248 / 824640 |
| final / hard-cyclic9-f2-repeat | 84 | 0.967359 | 0.967359 | 0.967305 | 0.950564 / 0.984450 | 906616 / 822696 |

The final focused result across all four pairs has process B/A 0.994213.

These observations do not establish a broad speedup, fixed-corpus completion, held-out performance or an external-comparator milestone. Ratios from successive implementation stages are not multiplied.

## Correctness and replay

Both stages pass all twelve Clang/GCC ASan/UBSan variants and all nine project gates, including executable/theory builds, 567 SymPy and 567 Singular basis comparisons, both 1134-case driver checks, downstream kernel replay, axiom audits and project DAG/phase/release checks. Every native variant fills private row storage with 0xa5 before explicit initialization. Final tests also assert that mixed frames initialize strictly fewer packed rows than installed pivots, exercise a nonempty table-saving straddle at 2³⁴−2 / 2³⁴+1, and project dense rows at the highest full and partial word. Runtime-seeded probes avoid initialization-time evaluation; their sugar labels remain bounded even for seeds above 2⁶³.

Initial capsule `f4-lazy-pivots-176673354ffa.tar.xz`: SHA-256 `3ba260bc18e651e4a35053b5dcd42c068abd548ebe4fd075dc94e65449343a60`. Final capsule `f4-lazy-pivots-4fb747423df0.tar.xz`: SHA-256 `7715cf0eda4819edb188d33bc7592e0914084771ff9eeaf3ff6f221f7cd77b67`. They bind full source/check manifests, compiler inputs, raw samples and complete logs. Earlier failed setup/check attempts remain diagnostic records.


## Current configuration audit

Current runtime `8861aaf91c08` changes only the Lake registrations for unrelated RCF modules relative to the measured final snapshot. The only verification-manifest change is CI disk reclamation. All three freshly frozen compute/reference/bench executables have exactly the measured SHA-256 hashes; compiler controls match. All twelve native sanitizer variants and all nine project gates pass on this current snapshot.

Audit capsule `f4-lazy-config-audit-8861aaf91c08.tar.xz`: SHA-256 `b88fe9fd87361718f1c7940d531ddb10155fc3a8674a29f93637216b55add463`. No timing sample is replaced or inferred from the configuration update.

```bash
python3 scripts/bench/groebner_lazy_report.py \
  --initial reports/bench-results/raw/f4-lazy-pivots-176673354ffa.tar.xz \
  --archive reports/bench-results/raw/f4-lazy-pivots-4fb747423df0.tar.xz \
  --audit reports/bench-results/raw/f4-lazy-config-audit-8861aaf91c08.tar.xz \
  --report reports/bench-results/hexgroebner-lazy-pivots.md --check
```

Add `--current` for the measured final runtime/check snapshot. [Issue #10987](https://github.com/kim-em/hex-dev/issues/10987) remains open.
