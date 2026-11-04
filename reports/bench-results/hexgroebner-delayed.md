# Exact delayed prime-field elimination

The measured production snapshot is `5d76c73aac25`; the audited configuration is `dd9d311285d9` with byte-identical executables. `delayedReduction` is opt-in and defaults to false. It applies to primes `3 ≤ p < 2^16`; ordinary F₂ and wider-prime polynomial routes retain their existing arithmetic. The accumulator bound is `(p-1)+columns*(p-1)^2 < 2^50`.

All 120 final full-system processes succeeded. All 60 off/on pairs have identical complete reduced bases, metadata and logical counters. The suite contains the first primary size from each of ten fixed families over three prime fields; it does not cover the complete fixed suite or held-out acceptance. Both arms use the same frozen executable, one leased CPU, grevlex order, degree scheduling, batch size 1024, binary pivots enabled and dense pivots disabled. Adjacent arms alternate AB/BA. Every completed sample, failure and outlier is retained.

| Field | Candidate B/A geometric mean | Process B/A geometric mean | Pair candidate ratio range | Peak RSS A/B, KiB |
|---|---:|---:|---:|---:|
| 2 | 0.9983 | 1.0067 | 0.6829–1.2982 | 34832/34832 |
| 32003 | 0.9162 | 0.9419 | 0.7354–1.0151 | 605208/565308 |
| 2147483647 | 1.0060 | 0.9990 | 0.9563–1.1217 | 727104/727164 |

For the in-sample KLYZ-12 motivating case over 32003, candidate B/A is 0.7394. A separately instrumented full producer accepted all 61 matrices and discarded zero charged native work; its complete output and counters equal the production run. Its two candidate pair ratios span 0.7354–0.7434. Raw samples retain per-input variability and RSS; the field table's ratio range also includes differences between families. The parent limits are the fixed corpus protocol's explicit large allowances, with 300-second, 8-GiB address-space and 256-MiB per-file external caps. These measurements do not establish behavior under the library's default work/memory allowances.

| Kernel coefficient route | Columns | B/A geometric mean |
|---|---:|---:|
| Byte | 128 | 0.9029 |
| Byte | 256 | 0.9325 |
| Byte | 512 | 0.9461 |
| Short | 128 | 0.9151 |
| Short | 256 | 0.9573 |
| Short | 512 | 0.9687 |
| Word | 128 | 1.0078 |
| Word | 256 | 1.0084 |
| Word | 512 | 0.9967 |

Kernel inputs use distinct known heads, dense tails and eight shared targets. Preparation is outside timing; validation, elimination and complete output/counter hashing are inside. Byte uses 251, Short uses 32003 and Word is the unchanged M31 control. The final 42-process lean-bench campaign has no point below the signal floor. The recorded host is AMD EPYC 9455; the production native compiler is Clang 21.1.8, the Lean SDK compiler is Clang 23.1.0, and Lean is 4.35.0-rc3. Native dispatch uses guarded AVX2 with scalar fallback; experimental AVX-512 dispatch is disabled. Compiler hashes, flags, exact selected CPU and environment remain in the manifests. Six trial-major quadratic sweeps use three trials and three sizes. Matched observations alternate AB/BA. The earlier short-budget campaign was inconclusive because matched points fell below the signal floor; its sole unchanged repeat used a four-second batch target and twenty-second allowance. Both are retained separately from the final production campaign.

Experimental captured-matrix replay rejected a scalar UInt64 design (B/A 1.3228); the AVX2 prototype gave 0.7205. Each has four initial AB/BA observations with complete row/label/counter comparison outside the C monotonic timing interval. These experimental binaries are distinct from the production implementation. The retained input is frame 33, selected for maximum work among progressive entry-maximum dumps; the absolute maximum-work frame was not dumped.

Local verification covers twelve strict Clang/GCC ASan/UBSan variants, scalar/SIMD fallbacks, exact packet guard pages, near-UInt64-limit residues, work/byte boundary cuts, newly admitted reducer/target counts, direct scalar Lean comparisons, producer parity, independent oracles and all nine project gates. A freestanding 32-bit x86 packet compilation checks the portable intrinsic choice. Native calls remain bounded but cancellation occurs between calls; a late work or byte decline may repeat a bounded prefix.

All timing results concern unchecked candidate production or matrix elimination. Certificate generation, independent native certification, kernel checking and complete checked calls are not included. Giac process diagnostics in the archive retain installed version 2.0.0-19, explicit monic conversion and full output comparisons; CLI startup affects tiny cases, its internal time() clock is not asserted to be wall time, and no current-fastest claim follows. No CI timing is used. The fastest-open-source milestone and overall-fastest gap remain open.

Raw production evidence: `f4-delayed-p16-5d76c73aac25.tar.xz` (SHA-256 `37255588ebbde8f6d12c15725a98f1de66fed5bec97c91c8c56dc08d6a431eab`). Experimental replay: `f4-delayed-replay-11e6d0100e34.tar.xz` (SHA-256 `c8c937e1a1e3f917364f91a0b9d237c0fa77a63b716f89a2cc316151e6d3e836`). Every payload is checked against its archive SHA-256 manifest; the report also replays source blobs, complete outputs, counters and measurement coverage.
The configuration audit `f4-delayed-config-dd9d311285d9.tar.xz` (SHA-256 `e31ef44505486f64b99737b91f38a64e963c129bc99d4b570e768ccfd0da2ea7`) adds only the whole-matrix SIMD header dependency. All three fresh executable hashes and compiler/ISA controls are identical, verification sources are unchanged, and the five project linters passed again. The nine-gate results retain their measured source identity.
