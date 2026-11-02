# Matrix scan and candidate-output performance

The combined source preserves every complete reduced basis and resource counter
in the matched 14-input suite. It uses about 7.4% less whole-process time than
the selected dispatch source in this observation. The remaining Hex/msolve
process ratios are 1.7030 (exact mode 2) and 1.9121 (probabilistic mode 42);
the fastest-open-source milestone is not met.

Three distinct changes are combined. A bounded native scan reuses a successful
shape check of the same borrowed immutable pivot between selection, update and
completion. A resumed pending pivot is checked before use, and entry/ordering/
coefficient/error checks remain in place. No ABI, Lean definition, charged work
or output convention changes. The candidate driver writes numeric polynomial
arrays directly to an owned string, avoiding a temporary JSON tree per exponent.
Fixed punctuation and natural numbers are the only directly encoded content;
metadata and errors still use Lean's JSON encoder. The `basis` key moves from
first to last in the JSON object. Consumers compare parsed fields; byte hashes
of the old and new stdout are not interchangeable. The metadata object is
fixed and nonempty, so its compact encoding supplies the final `}` delimiter.
The third change uses an existing bounded native zero provider in the public continuation's Lean
workspace phase; its [separate report](hexgroebner-workspace-zero.md) explains
why it is an API-path improvement rather than a production F4 speedup.

Source fingerprint `fd0313c0ed28` identifies frozen snapshot
`b74589ae7668e17fcf58127aa618376f349e6018`; compute SHA-256
`2ecb3c2b8d5d44444c7d037e91d03bb1785065e8be3eb7cda42a0757992cd997` and full-initialization SHA-256
`fc28ead0155245926fc062c9f30e86a97426c653576e04298361afcb1d7d7bf1`. The reviewed source fingerprint is `8f56f7677ce6`, at code commit
`65884c900e8e59fabb8b458faa94236e5c54c866`. Fresh builds of both driver variants
have exactly the same SHA-256 values as the measured source above; a retained
runtime-identity audit connects the comment/test revision to those measurements.
The drivers are built in a fresh
detached worktree sharing only pinned dependency packages. Lean is 4.35.0-rc3,
compiler revision `470d5ce1400764999581fd26d5d72b00d990b0f4`. Compiler/link flags,
source blobs, runtime patches, build logs and initializer audit are retained.
The minimal driver links the pinned SDK's `libinitialize_minimal.a`; the
full-initialization driver is independently checked on the same complete corpus.
Candidate production remains deterministic, with explicit random state unchanged.

The [medium development corpus](hexgroebner-medium.md) has cyclic7, Katsura8,
Eco11, Noon5, Reimer6, MinRank and dense quadratic6, each over primes 32003 and
2147483647, in grevlex order. It is not a held-out or acceptance suite. The selected
baseline has fingerprint `0a7fa663e970`; the earlier pre-selection baseline
`dd2370a9e993` is measured in a different campaign and is not pooled with it.
Every before/after JSON field except candidate time agrees, including complete
basis coefficients/exponents, field/order metadata, scheduling and all counters.

Each campaign runs all adjacent AB pairs followed by all adjacent BA pairs on
the shared host chungus2. CPUs are automatically leased and all process threads
inherit one-CPU affinity. Hex's algorithm is serial, with runtime auxiliary
threads; comparators receive their one-thread option. Identical GNU-time wrappers
include launch, startup, input parse, candidate production, final interreduction
and full native-format output. Per-process limits are 60 seconds, 16 GiB address
space and 64 MiB per output file. All completed samples, failures, output, RSS,
variability and host-load context are retained. There is no host filtering or
unchanged repeat for the combined source.

Certificate generation, independent native certification and kernel checking
are excluded from candidate/process timings. Hex internal candidate time is
never compared with a comparator's process or printed internal time. The driver
serializer does not change the algorithm or its timing boundary; candidate-time
variation is recorded separately and is not attributed to faster arithmetic.

Current msolve source is clean at `3672113ee2c696a2ac9c637636e0f7214f500ba1`,
using the recorded Clang 23.1.3 `-O3 -march=native` build (znver5), GMP 6.3.0,
MPFR 4.2.2 and FLINT 3.6.0. Direct ELF and neogb library hashes/configuration
are retained. Mode 42 is probabilistic and is a separate campaign.
Official GamBa v0.3 AVX2/AVX-512 binaries and loader/library hashes are those in
[the pinned baseline report](hexgroebner-gamba-0a7fa663e970.md). These new campaigns
explicitly set seed 10987, grevlex, one thread, full reduced-basis output and
`--max-spairs 2000`. GamBa is partly closed source and ineligible for the
fastest-fully-open-source acceptance set. No probability guarantee is inferred.
Untimed priority/library audits are retained in the baseline report; historical
priority is not independently logged for each timed process.

| Combined whole-process ratio | Family-balanced mean | Median | Range | CPU | Peak RSS A/B KiB |
| --- | ---: | ---: | --- | ---: | ---: |
| New/selected baseline | 0.9263 | 0.9191 | 0.8402–1.2167 | 39 | 124812/95484 |
| New/pre-selection baseline | 0.9234 | 0.9117 | 0.8248–1.1725 | 20 | 126996/96292 |
| Hex/msolve exact 2 | 1.7030 | 1.7506 | 0.6724–2.9466 | 39 | 96292/20328 |
| Hex/msolve probabilistic 42 | 1.9121 | 1.8274 | 0.6562–4.3451 | 10 | 96292/20328 |
| Hex/GamBa AVX-512 | 3.1122 | 3.1416 | 0.9916–7.9133 | 25 | 96292/42624 |
| Hex/GamBa AVX2 | 3.2993 | 3.4387 | 0.9897–8.9847 | 89 | 96292/38552 |

Each campaign completes 56 processes and 28 complete-basis comparisons without
failures or timeouts. Before/after A is baseline and B is new; comparator A is
Hex and B is the named system. The geometric mean first combines paired ratios
within each family, then weights the seven families equally. Native output
formats differ; complete mathematical contents are compared outside timing.

| Family | New/selected | Hex/msolve 2 | Hex/msolve 42 | Hex/GamBa AVX-512 | Hex/GamBa AVX2 |
| --- | ---: | ---: | ---: | ---: | ---: |
| cyclic | 0.9225 | 2.5940 | 3.3375 | 6.1826 | 7.0119 |
| kat | 0.8752 | 1.8936 | 2.0824 | 3.0303 | 3.3315 |
| eco | 0.8960 | 1.8750 | 2.6898 | 7.2502 | 8.5671 |
| noon | 0.9437 | 1.6092 | 1.6516 | 2.0794 | 2.1320 |
| reimer | 0.9010 | 2.0919 | 2.3060 | 3.3863 | 3.6009 |
| minrank | 1.0064 | 0.9685 | 0.9542 | 1.5179 | 1.4568 |
| dense-quadratic | 0.9455 | 1.3835 | 1.3755 | 1.9479 | 1.9012 |

Small process times remain startup-sensitive. The two vendor ISA campaigns
are separate observations, not a matched ISA comparison. Summed wall time gives
a different weighting toward longer cases and is descriptive rather than a
replacement for the required balanced metric:

| Vendor ISA | Hex total ms | GamBa total ms | Ratio of totals |
| --- | ---: | ---: | ---: |
| gamba-avx512 | 5002.801 | 836.252 | 5.9824 |
| gamba-avx2 | 4868.439 | 717.818 | 6.7823 |

The combined selected-baseline internal candidate-time mean is 0.9773, with range 0.9539–1.0372. Candidate and process intervals are distinct.

Separate component sources retain their own measurements. Scan geometry reuse
`eec5501ff66f` preserves all 28 complete outputs/counters in two campaigns:
process ratios 0.9836 and 0.9832, internal candidate ratios 0.9948 and 0.9817.
The second is the one allowed unchanged repeat after an inconclusive first
campaign. Cyclic7/Eco11 candidate ratios in that repeat are roughly 0.96–0.98.
The scan-cache timing is inconclusive. A similar candidate-time shift occurs
with the driver-only source, whose change follows the timed interval; these
separate campaigns cannot isolate a matrix speedup.
Direct numeric serialization `ac18b44c91fd` has process mean 0.9191, internal
candidate mean 0.9724 and peak baseline/new RSS 124008/95444 KiB. Both 1,134-case
drivers pass. These source-specific campaigns are not pooled or added together;
the combined campaign above measures the actual composition. The serializer
observation includes that candidate-time shift: it does not establish an 8%
output-only improvement. Subtracting the observed candidate intervals from
process intervals is also not a controlled isolation of output time.

Diagnostic Eco11 user-cycle profiles of the pre-cache source `0a7fa663e970`
report no lost samples. About 39% of samples are attributed to the scan function
and 9–10% to `geometry` at both prime widths; native trie lookup is about 3%.
These are coarse symbol shares, including associated header/data loads and
memory stalls. They do not isolate shape-check arithmetic or establish a cache
speedup. The vendor binary lacks useful symbol names in its capture, so no
internal algorithm attribution is made for it. Profiles include startup/output
and provide cost attribution rather than matched timing evidence.

Combined library/theory/conformance builds, independent matrix/division/basis
oracles, both 1,134-case drivers, eight Clang/GCC sanitizer/scalar/SIMD/remainder
configurations, kernel replay/axiom guards, benchmark verification and project
DAG/phase/release/header/line checks pass. The native tests include malformed
prefixes (including resumed pending pivots), guard pages, aliases, snapshots,
late exhaustion and large widths. Workspace tests cover the one-MiB native zero
limit and scalar fallback at all three coefficient widths. An isolated harness
window requires exactly six admitted and six declined provider calls.
The full check run reuses Lake artifacts; it is not a fresh whole-graph build.
The two CLI identity builds above are fresh. The workspace-zero kernel figures
belong to the separate `a3938be198b4` source, which has the old scan code; no
identity with a final combined benchmark binary is asserted.
The serializer is checked against complete independently recomputed corpus
outputs and both driver initialization paths. No checked-result API or
certificate contract is changed.

The remaining gap is substantial, especially cyclic and Eco. These finite
observations establish neither fastest-open-source leadership nor a language
impossibility. Hard/held-out families, additional field/extension widths,
parallel sweeps, solved coverage and separate certification/native-verification/
kernel-checking costs remain required. Issue #10987 remains open.

[Raw capsule f4-scan-cache-eec5501ff66f](raw/f4-scan-cache-eec5501ff66f.tar.gz): SHA-256 `0a020f985259419132adb6cb7541d3d9186d20421fb4bf012e94903ef0533b9f`, 653 payloads, each read back and digest checked.

[Raw capsule f4-driver-output-ac18b44c91fd](raw/f4-driver-output-ac18b44c91fd.tar.gz): SHA-256 `1911c511febb46285e15f5fc080f52ae0924be6a7b93bff4459a47a692904ee5`, 405 payloads, each read back and digest checked.

[Raw capsule f4-combined-performance-fd0313c0ed28](raw/f4-combined-performance-fd0313c0ed28.tar.gz): SHA-256 `ceb95beadbc9cc4e7e7eae24345b5d05ba6c5fee819056ee8db176d90d474373`, 1558 payloads, each read back and digest checked.

[Final-source audit f4-performance-review-8f56f7677ce6](raw/f4-performance-review-8f56f7677ce6.tar.gz): SHA-256 `e2377fb7f57872ce2977d07196e28912b979603d7b60ca6fb21aeb9f897d3389`, 222 payloads, each read back and digest checked. It retains the final fresh-build identity, all nine project checks and eight sanitizer variants, their source identities, generated probes and complete logs.

[`groebner_performance_audit.py`](../../scripts/bench/groebner_performance_audit.py)
recomputes all campaign tables, component means, candidate ranges, vendor totals
and RSS from the retained sample metadata. For every before/after pair it reads
the complete stdout objects, compares every field except `candidateNanos`, and
checks counters/scheduling against metadata. The earlier analysis script is also
retained at `reproduction/analyze-equivalence-candidates.py` in each relevant raw
capsule; the new audit makes this stronger comparison directly reusable.
