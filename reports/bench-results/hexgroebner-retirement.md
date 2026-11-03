# Critical-pair retirement

A basis entry whose leading monomial is divisible by a newer leading monomial retires from future pair generation. Its polynomial remains a reducer, its stable index and derivations remain valid, and existing queued obligations remain. Installation considers the connecting pair before retirement. The selected implementation iterates an ascending active-index array, rather than scanning every old basis entry.

Pair coverage still requires a producer proof. Its dependency order includes LCM, maximum index and a final level accounting for equal-LCM groups and prior retirement-chain depth. Independent final certification continues to check every required final S-pair and both ideal containments. No correctness-completion or fastest-open-source milestone is claimed.

## Matched observations

Host `chungus2`; production native C: clang version 21.1.8; Lean-generated C: clang version 23.1.0 (https://github.com/llvm/llvm-project ea7d852a70e8bdfaf601d6626a760f9771b2c4b4); toolchain `leanprover/lean4:v4.35.0-rc3`. Both prototypes use the same compilers as their baseline, with AVX-512 disabled and one algorithm thread. The fourteen fixed grevlex inputs cover seven families at 32003 and 2147483647 with degree scheduling and complete unchecked-candidate output. Each campaign uses adjacent AB then BA on an automatically leased CPU. Candidate production excludes certification and kernel checking. Each prototype has exactly one unchanged repeat; campaigns remain separate and all completed samples are retained.

| Implementation / campaign | CPU | Process B/A | Candidate B/A | Work B/A | Considered pairs B/A | Process pair range | Peak RSS A/B (KiB) |
|---|---:|---:|---:|---:|---:|---:|---:|
| active-pairs / f4 | 37 | 0.985055 | 0.984274 | 0.990201 | 1.000000 | 0.855554–1.222622 | 92252/82096 |
| active-pairs / f4-repeat | 95 | 0.983842 | 0.981786 | 0.990201 | 1.000000 | 0.861300–1.220654 | 92252/82096 |
| active-list / f4 | 37 | 0.989454 | 0.984767 | 0.985992 | 0.761177 | 0.709128–1.589904 | 92232/79772 |
| active-list / f4-repeat | 81 | 0.975741 | 0.935443 | 0.985992 | 0.761177 | 0.833463–1.280127 | 92232/79772 |

All 224 processes (112 pairs) complete with equal canonical bases and no failures or timeouts. Statistics can change because pair generation and matrix work change. These campaigns do not establish an overall timing benefit at this resolution. The array choice rests on deterministic reductions in considered pairs and charged work, rather than a timing ranking against the tree implementation. No comparator leadership is claimed.

| Family (process B/A) | Tree first | Tree repeat | Array first | Array repeat |
|---|---:|---:|---:|---:|
| cyclic | 0.899254 | 0.896105 | 0.846126 | 0.856435 |
| kat | 1.005244 | 1.007858 | 1.137376 | 1.029331 |
| eco | 0.986982 | 0.989464 | 0.961274 | 0.982026 |
| noon | 1.020855 | 1.007866 | 0.991633 | 1.071450 |
| reimer | 0.948884 | 0.949524 | 1.007063 | 0.931251 |
| minrank | 1.022094 | 1.027195 | 0.986645 | 1.028136 |
| dense-quadratic | 1.018806 | 1.015679 | 1.018622 | 0.948157 |

The array route avoids generating retired pairs; its considered-pair count is lower rather than recording those pairs as GM rejections. Katsura regresses in both array campaigns; the first observation prompted retained ABBA cycle profiles. Those short profiles do not establish a consistent new bottleneck. Memory, inputs, complete outputs, counters and host activity remain in the raw capsules. No additional unchanged timing repeats were collected.

## Remaining comparator gap

The reviewed array executable remains 1.914153× slower than msolve in family-balanced process time on this suite. All 56 matched processes complete with 28 equal full-basis pairs; their failures, memory and raw samples are retained. msolve revision `3672113ee2c696a2ac9c637636e0f7214f500ba1` uses Clang 23.1.3, native CPU tuning, deterministic elimination (`-l 2`), full reduced output (`-g 2`) and one thread. Individual process ratios range from 0.432778 to 5.200088. Hex retains the host native compiler and runtime dispatch with AVX-512 off. This separate matched comparison is not pooled with prototype comparisons, and does not cover the full acceptance suite.

| Comparator family | Hex/msolve process |
|---|---:|
| cyclic | 2.822064 |
| kat | 3.160591 |
| eco | 1.716528 |
| noon | 2.257972 |
| reimer | 2.078976 |
| minrank | 1.286955 |
| dense-quadratic | 1.017932 |

## Verification

All twelve Clang 23.1.3/GCC 16.2.0 ASan+UBSan variants and all nine project checks pass at runtime `4976b3eed62c`, checks `8d120f12c9c1`. They include the executable/theory build, independent oracles, native/portable drivers, benchmark verification, DAG, phase, release-manifest and source checks. All 567 unique emitted bases match SymPy and Singular; 4,536 native/portable/default/serial computations match the corpus. A further fixed seed produces 128 fresh systems, with 512 native/portable and degree/sugar computations matching independently computed SymPy bases.

The reviewed runtime `b08fe700881e` changes only pair-module documentation after measurement, reproducing both measured executable hashes. Additional Lean guards check a nonzero omitted S-polynomial, connecting obligations, the required ordinary-F2 term `xz²`, and both retired and Buchberger-to-GM frontier-gap resumptions. All nine project checks also pass with the final guard sources. Their source and logs are retained separately from the earlier verification snapshot.

Rebased runtime `0ee4d62001af` incorporates the default-preserving compiler-selection setting, compiler-command provenance changes and the monomial target’s missing trie-header dependency. Only Lake/freeze metadata differs from the reviewed runtime; all three executables remain byte-identical. All nine checks pass again after rebasing. Editing and restoring the included header rebuilds the monomial object and preserves its original hash.

Final runtime `701fdd34b8f2` makes the UPDATE depth convention explicit, with active depth zero and each removed index one greater than its replacement. The runtime edit is documentation only, with all three executable hashes preserved. Final guards check the post-preprocessing depth-two chain and exact initial pair counts, compare its final basis with unpruned Buchberger, and exercise repeated installation and a GM–Buchberger–GM resumption with both removed indices and an eligibility gap. All nine checks pass again.

The reversed-divisibility mutation preserves the tested fresh bases: losing retirement can merely lose pruning. The targeted queue-obligation guard separately checks the retirement direction. A second mutation retiring unrelated entries produces a wrong basis, independently rejected by SymPy. Its minimized ordinary-F2 system `yz, xy+xz, y²` misses `xz²`; direct regressions cover both schedules. Mutation attempts and failures are retained.

`f4-active-pairs-1385ee01d770.tar.xz`: SHA-256 `34a3670c842187e046babd246a2559f476802a12acc3ca24c4df8554b6e7a9c4`.
`f4-active-list-4976b3eed62c.tar.xz`: SHA-256 `85a22519ea587b34624d92d094bbf52b9bf94866aa267baafebff297190b4695`.
`f4-active-list-checks-0a4bc08b663d.tar.xz`: SHA-256 `56c833c4258dc42d4492294117bc703ae0c93ab86d1fbaa83c5a915c140cb3b0`.
`f4-retirement-rebased-0ee4d62001af.tar.xz`: SHA-256 `59fc24aeb47db5f3c0be69a2fdd67a3239609ab32ef544192f08356d68bb23b1`.
`f4-retirement-review-c3291109e419.tar.xz`: SHA-256 `a317aee9012c5aa580be3dee1dd9d6db8198aeade6e11681ed895ffdf89840b7`.

Regenerate historical evidence with `python3 scripts/bench/groebner_retirement_report.py --tree reports/bench-results/raw/f4-active-pairs-1385ee01d770.tar.xz --array reports/bench-results/raw/f4-active-list-4976b3eed62c.tar.xz --guards reports/bench-results/raw/f4-active-list-checks-0a4bc08b663d.tar.xz --rebased reports/bench-results/raw/f4-retirement-rebased-0ee4d62001af.tar.xz --review reports/bench-results/raw/f4-retirement-review-c3291109e419.tar.xz --report reports/bench-results/hexgroebner-retirement.md --check`. Add `--current` to require the present checkout to match the final verification sources.
