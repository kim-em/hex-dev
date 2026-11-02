# Packed F4 column positions and charged translation

Symbolic candidate and certificate row construction use compact u32 positions. Dense ID prefixes use positions plus one; sparse u32 IDs use exact open-addressed key/value buckets. Hashes are filters: every successful lookup compares the complete key. Geometry alone selects the layout. A chain beyond 64 probes retains the charged attempt and builds the ordinary hash map; unsupported IDs and addressability also retain it.

Native calls translate at most 4,096 entries, reserve owned output once and commit its logical size only on success. Borrowed/output aliases, shared prefixes and marked-linear growth agree with the scalar Lean definitions. Zero initialization processes at most 4,096 bytes per call. Initialization, insertion probes and packed payload are charged before work. Rows reserve the maximum probe count per key; sorting reserves two such lookups per comparison. Cumulative bytes and conservative work bounds can exhaust earlier than the previous unit-cost hash-map route. Layout and counts can differ across 32-bit and 64-bit address widths.

The measured content fingerprint is `67e9835420ef`, captured from commit `5d0cf13ff0` plus the exact staged source snapshot in the capsule, compute SHA256 `4018867411b786bfcdafcdffd13d0412d8c36504f09e997b30400d126c391be1` and reference-driver SHA256 `09817bff776a62d96f8a2218e54a8a0a7f43e3f18afc516ce3b73b7f5d513628`. Baseline is `e878b78cf727`, compute `fb6a033166de667e753df9ba554203503bb7bb9e89ad893f351f18f064eb2a1d`. The [initial variant](hexgroebner-column-index-initial.md) has separate measurements and binaries; no observations are pooled across that source or configuration.

Both arms have fresh detached driver and benchmark builds sharing only pinned dependency packages. The archived relocatable compiler helper restores the local SDK flags and directly invokes SDK Clang/LLD 23.1.0. Native FFI uses Clang 23.1.3. Results apply to this build arrangement.

All timings are manual observations on the shared EPYC 9455 host, one requested algorithm thread and automatically leased CPUs. Each input uses adjacent AB/BA. Every completed sample, failure, outlier, host-activity observation and child RSS remains. Small, medium and fixed observations retain the first campaign and sole unchanged repeat; no further unchanged repeat is used. These are development suites, not held-out SPEC acceptance.

Recorded host activity is context for all comparisons. The initial variant's campaign-start one-minute loads were 3.2–14.3; the revised starts below were 27.5–87.1 on this 96-logical-CPU host. Load averages do not identify interference on the leased CPU. Comparisons between initial and revised campaigns are confounded by different host activity; neither the changed small-suite aggregate nor the increased msolve gap isolates a source effect. No completed observation is discarded, and no quiet-host rerun is sought.

| Revised campaign | CPU | Load start, 1/5/15 min | Load end, 1/5/15 min |
| --- | ---: | --- | --- |
| small/first | 58 | 58.97/59.48/34.91 | 57.88/59.23/35.09 |
| small/repeat | 71 | 83.13/67.34/42.53 | 79.25/67.03/42.69 |
| medium/first | 82 | 57.88/59.23/35.09 | 60.08/59.68/35.89 |
| medium/repeat | 41 | 79.25/67.03/42.69 | 78.02/67.87/43.75 |
| fixed/first | 26 | 76.37/67.37/43.46 | 79.68/68.84/44.58 |
| fixed/repeat | 67 | 61.68/65.61/44.99 | 57.97/64.60/44.99 |
| kernels/first | 69 | 87.12/66.93/41.86 | 65.64/66.60/44.85 |
| kernels/repeat | 35 | 27.49/43.75/43.82 | 48.08/44.43/43.92 |
| msolve/-l2 | 52 | 76.37/67.37/43.46 | 79.68/68.84/44.58 |
| msolve/-l42 | 66 | 79.68/68.84/44.58 | 70.46/67.53/44.79 |

Candidate time includes packing, F4 and final interreduction. Process time additionally includes initialization, parsing, complete output and identical GNU-time wrappers. Certificate generation, independent certification and kernel replay are separate and excluded. Large process/candidate discrepancies are not attributed to the representation change.

| Suite | Campaign | CPU | Candidate B/A | Process B/A |
| --- | --- | ---: | ---: | ---: |
| small | first | 58 | 1.0914 | 1.1352 |
| small | repeat | 71 | 0.9524 | 0.9387 |
| medium | first | 82 | 0.9753 | 0.8855 |
| medium | repeat | 41 | 0.8385 | 0.9322 |

| Suite | Complete pairs | Candidate B/A | Candidate median | Process B/A | Equal-family process |
| --- | ---: | ---: | ---: | ---: | ---: |
| small | 64 | 1.0195 | 0.9838 | 1.0323 | 1.0484 |
| medium | 56 | 0.9044 | 0.9571 | 0.9086 | 0.9086 |

All 240 processes succeed and all 120 complete basis pairs agree. Every non-resource algorithm counter agrees. Work and packed-allocation differences remain below. There are zero measured failures or timeouts. Small results remain mixed and medium aggregate improvements do not establish a uniform gain.

| Family | Small candidate | Small process | Medium candidate | Medium process |
| --- | ---: | ---: | ---: | ---: |
| cyclic | 0.8246 | 0.9263 | 1.0154 | 0.9886 |
| dense-quadratic | 2.4627 | 1.2890 | 1.0340 | 1.2781 |
| eco | 0.9401 | 0.9312 | 0.9402 | 0.9278 |
| kat | 1.8505 | 1.2765 | 0.9697 | 0.6959 |
| minrank | 0.3115 | 1.1292 | 0.6592 | 0.6961 |
| noon | 1.2183 | 0.7704 | 0.8331 | 0.8883 |
| reimer | 1.0561 | 1.1276 | 0.9412 | 1.0133 |

The revised small dense-quadratic candidate aggregate (2.4627) is driven by the quadratic5-M31 repeat spikes (new 28.246–86.303 ms versus baseline 4.107–4.395 ms). The revised small MinRank aggregate (0.3115) also reflects baseline spikes, including 15.834–15.995 ms in its M31 repeat. Neither is a stable family gain or regression.

Small candidate ratios span 0.0234–52.7853; process ratios span 0.2326–4.5721. Maximum child RSS is 50260/52668 KiB for baseline/new. Logical packed bytes do not bound allocator capacity or RSS.

Medium candidate ratios span 0.0848–9.5833; process ratios span 0.1748–3.8618. Maximum child RSS is 97520/94592 KiB for baseline/new. Logical packed bytes do not bound allocator capacity or RSS.

The unexplained small MinRank spikes in the initial source are explicitly outlier-driven; its family aggregate is not a stable per-family superiority or regression claim. The absolute revised small-case intervals below retain every AB/BA sample, rather than replacing a range with a pooled median. The initial MinRank CPU profile did not reproduce the anomaly and does not identify its cause.

| Small input | Campaign | Baseline candidate ms, min–max | New candidate ms, min–max |
| --- | --- | ---: | ---: |
| cyclic6-31 | first | 18.369–54.445 | 24.810–31.219 |
| cyclic6-31 | repeat | 23.345–41.722 | 15.703–30.149 |
| noon4-31 | first | 2.250–4.261 | 3.370–30.757 |
| noon4-31 | repeat | 2.559–4.013 | 2.081–4.055 |
| minrank_d_2_p_2_q_3_r_2-31 | first | 0.466–8.359 | 8.001–24.590 |
| minrank_d_2_p_2_q_3_r_2-31 | repeat | 15.834–15.995 | 0.878–28.149 |
| quadratic5-2147483647 | first | 2.912–4.861 | 2.637–3.761 |
| quadratic5-2147483647 | repeat | 4.107–4.395 | 28.246–86.303 |

| Initial-source small route profile | Direct | Indexed | Hash fallback | Maximum indexed probes |
| --- | ---: | ---: | ---: | ---: |
| cyclic6-31 | 11 | 9 | 0 | 9 |
| noon4-31 | 9 | 0 | 0 | n/a |
| minrank_d_2_p_2_q_3_r_2-31 | 4 | 0 | 0 | n/a |
| quadratic5-2147483647 | 7 | 0 | 0 | n/a |

This explanatory profile binds initial source `9449e25be93d`, CPU 86, and one instrumented plus one uninstrumented run per input. Full bases and counters agree. MinRank, Noon and dense-quadratic are direct-only, which excludes indexed probing but still exercises the new direct allocation, zero initialization and translation path. This route profile does not exclude that path as a cause of a regression. A separate eight-process adjacent AB/BA user-cycle profile compares the baseline hash route with revised direct maps on Noon4-31 and quadratic5-M31. Full bases and non-resource counters agree. Whole-process cycles are baseline 34.07/37.30 million versus direct 26.76/40.56 million for Noon, and baseline 39.71/29.00 versus direct 40.31/26.11 million for quadratic. These small whole-process profiles neither isolate map costs nor reproduce the historical wall-time spikes. All records remain; their durations replace no timing sample. The revised source changes sorting charges, not lookup geometry. No profile duration is pooled into timing estimates.

| Fixed campaign | CPU | Case | B/A geomean | Per-call median | Range |
| --- | ---: | --- | ---: | ---: | --- |
| first | 26 | cyclic4 | 0.9773 | 0.9992 | 0.6265–1.4807 |
| first | 26 | cyclic5 | 0.7472 | 0.8328 | 0.0731–4.5556 |
| first | 26 | cyclic6 | 1.3412 | 1.3561 | 0.2921–4.1758 |
| first | 26 | katsura3 | 1.1065 | 1.1915 | 0.1500–4.5956 |
| first | 26 | reimer5 | 0.8544 | 0.8882 | 0.4483–1.8710 |
| first | 26 | cyclic6Small | 0.9802 | 1.3569 | 0.2846–2.4575 |
| repeat | 67 | cyclic4 | 0.8964 | 0.9385 | 0.6449–1.0752 |
| repeat | 67 | cyclic5 | 0.9302 | 0.8582 | 0.0660–29.4634 |
| repeat | 67 | cyclic6 | 0.7699 | 0.5580 | 0.1357–7.1009 |
| repeat | 67 | katsura3 | 0.9625 | 1.0176 | 0.2179–1.8386 |
| repeat | 67 | reimer5 | 1.0672 | 1.0716 | 0.2905–4.7233 |
| repeat | 67 | cyclic6Small | 1.9708 | 2.2349 | 0.6797–4.1096 |

All 240 fixed points succeed and complete structural output hashes agree. Several campaigns disagree materially. Their per-call intervals include complete result consumption and hashing, and remain distinct from the CLI candidate interval. No uniform fixed-case improvement is inferred.

The total work increase is explicit for every input. Packed payload is charged cumulatively; it is not inferred from work-only fixture fields. Each row gives the deterministic counter from the retained processes.

| Suite/input | Baseline work | New work | Ratio | Baseline/new allocated bytes |
| --- | ---: | ---: | ---: | ---: |
| small/cyclic5-15 | 293573 | 304253 | 1.0364 | 120750/132886 |
| small/cyclic5-31 | 297587 | 308267 | 1.0359 | 131080/143216 |
| small/cyclic6-15 | 2199392 | 2300020 | 1.0458 | 688444/728332 |
| small/cyclic6-31 | 2213935 | 2314563 | 1.0455 | 755116/795004 |
| small/eco10-15 | 87701921 | 94245659 | 1.0746 | 15985568/16481544 |
| small/eco10-31 | 88678999 | 95222737 | 1.0738 | 18051592/18547568 |
| small/kat6-15 | 350554 | 353046 | 1.0071 | 158582/164666 |
| small/kat6-31 | 358192 | 360684 | 1.0070 | 177096/183180 |
| small/minrank_d_2_p_2_q_3_r_2-15 | 9057 | 9225 | 1.0185 | 9310/9654 |
| small/minrank_d_2_p_2_q_3_r_2-31 | 9448 | 9616 | 1.0178 | 10572/10916 |
| small/noon4-15 | 212429 | 215477 | 1.0143 | 102118/109586 |
| small/noon4-31 | 217588 | 220636 | 1.0140 | 113628/121096 |
| small/quadratic5-2147483647 | 324443 | 326242 | 1.0055 | 186648/190752 |
| small/quadratic5-32003 | 317014 | 318813 | 1.0057 | 165786/169890 |
| small/reimer5-15 | 2841737 | 2871978 | 1.0106 | 1262550/1319914 |
| small/reimer5-31 | 2915248 | 2945489 | 1.0104 | 1432652/1490016 |
| medium/cyclic7-15 | 126478860 | 134706691 | 1.0651 | 19338382/19649222 |
| medium/cyclic7-31 | 126833412 | 135061243 | 1.0649 | 21445260/21756100 |
| medium/eco11-15 | 565171559 | 571186118 | 1.0106 | 64071088/65680008 |
| medium/eco11-31 | 569701788 | 575716437 | 1.0106 | 72674108/74283028 |
| medium/kat8-15 | 9325622 | 9379221 | 1.0057 | 2350972/2393324 |
| medium/kat8-31 | 9444384 | 9497983 | 1.0057 | 2633184/2675536 |
| medium/minrank_d_2_p_2_q_4_r_2-15 | 100029 | 100781 | 1.0075 | 81444/83120 |
| medium/minrank_d_2_p_2_q_4_r_2-31 | 102164 | 102916 | 1.0074 | 92152/93828 |
| medium/noon5-15 | 1653344 | 1668953 | 1.0094 | 610862/650902 |
| medium/noon5-31 | 1685263 | 1700872 | 1.0093 | 683704/723744 |
| medium/quadratic6-15 | 857405 | 861676 | 1.0050 | 324622/335798 |
| medium/quadratic6-31 | 867596 | 871867 | 1.0049 | 359780/370956 |
| medium/reimer6-15 | 37045207 | 37461672 | 1.0112 | 12952222/13218270 |
| medium/reimer6-31 | 38020259 | 38436732 | 1.0110 | 14857324/15123372 |

An explanatory CPU profile directly compares initial `9449e25be93d` with this
sort-charge revision on Cyclic7-31 and Eco11-31, adjacent AB/BA, one leased CPU,
eight complete processes. Complete bases and non-resource counters agree;
zero samples are lost. Estimated user-cycle B/A ratios are 1.0427 and 0.9836.
These two inputs do not show the roughly twofold shift between the separate
msolve sweeps. The external-ratio change remains causally unattributed. Different host load is a recorded confounder, and these two user-cycle profiles do not isolate sensitivity to host activity; profile durations
are not additional timing samples and replace none of the retained observations.

Two registered lean-bench kernels cover allocation, construction, translation, independent complete-output validation and full map/support hashing. The recorded configuration requests four-second inner batches with an eight-second call cap. The runner clamps this target to about two seconds after reserving process startup; these are not four-second batches. Five trials cover nine fixed sizes, including non-powers of two and values through 65,536. Preparation is excluded. The direct and indexed kernels hash different payload lengths; their timing ratio is not an isolated map-construction comparison.

| Campaign/kernel | Complete points | Verdict | Median at 1024 | Median at 65536 | Signal-floor flags |
| --- | ---: | --- | ---: | ---: | ---: |
| first/columnDirect | 45 | consistent with declared complexity | 10.876 µs | 749.311 µs | 9 |
| first/columnIndex | 45 | consistent with declared complexity | 91.534 µs | 6368.088 µs | 38 |
| repeat/columnDirect | 45 | consistent with declared complexity | 9.672 µs | 1355.717 µs | 9 |
| repeat/columnIndex | 45 | consistent with declared complexity | 91.871 µs | 7350.946 µs | 10 |

| Campaign/kernel | Effective target seconds | Spawn floor ms | Eligible rows | Eligible parameter range |
| --- | ---: | ---: | ---: | --- |
| first/columnDirect | 2.011063 | 55.746 | 36 | 1024–65536 |
| first/columnIndex | 1.981052 | 175.792 | 7 | 1536–3072 |
| repeat/columnDirect | 2.000520 | 97.922 | 36 | 1024–65536 |
| repeat/columnIndex | 2.016418 | 34.327 | 35 | 1024–65536 |

Eligibility excludes below-floor rows before the runner groups parameters and applies its 20% leading-size warmup rule. Both direct campaigns and the indexed repeat then drop their smallest grouped parameter; the indexed first drops none. Its entire verdict therefore rests on seven rows at 1536, 2048 and 3072, a twofold size interval with no fitted slope. Each direct campaign has only one eligible row at 32768 and one at 65536. The direct 65536 medians differ materially (749 versus 1356 µs). These exported verdicts provide weak finite-range evidence, especially for the first indexed campaign.

The current registration raises the call cap to twenty seconds to accommodate the requested four-second target. It explicitly checks the selected map constructor, and zero/one verification parameters construct two sparse IDs to exercise indexing. These benchmark-only changes were locally checked; no new timing sweep is claimed for them. Runtime implementation sources remain the measured snapshot. The measurements above bind the earlier benchmark source in the capsule.

Kernel exports identify `854438f5b65051c3b27e68d49e7532ee8f39c60a-dirty`: the benchmark's environment probe observes its invoking working directory, rather than the detached build worktree. The archived build command, exact source snapshot, content fingerprint and ELF hash supply the build identity; this ambient Git identifier is not the measured implementation commit.

All 180 completed kernel rows remain. Medians above include all successful rows;
lean-bench fits separately retain their signal-floor and warmup decisions. The
single unchanged repeat follows the first sweep's many below-floor rows. These
flags limit resolution; no further unchanged repeat is used. This finite scaling
observation is neither an asymptotic proof nor an isolated map-cost comparison.
Earlier short-batch/five-size observations remain tied to their initial source
and are not pooled with this registered wider configuration.

| msolve `-l` | CPU | Hex/msolve process | Median | Range | RSS Hex/msolve KiB |
| --- | ---: | ---: | ---: | --- | ---: |
| 2 | 52 | 4.5873 | 5.0279 | 1.4854–8.5137 | 94552/20336 |
| 42 | 66 | 5.0274 | 5.6865 | 1.0784–10.4327 | 93880/20352 |

Here `-l 2` selects sparse exact elimination and `-l 42` probabilistic sparse/dense elimination in the pinned msolve version. Each mode retains its first matched 56-process sweep with 28 equal complete bases and no failures/timeouts. msolve is commit `3672113ee2c6`, effective native Clang 23.1.3/znver5, direct executable, one thread and full reduced grevlex output. Exact build/ISA identities are retained. These observations remain separate from all earlier sweeps and do not establish leadership.

Local validation covers library/theory/conformance builds, independent matrix/basis/division oracles, both CLI corpora, 34 benchmark checks and project audits. Four Clang and four GCC ASan/UBSan variants exercise the new kernels and all prior paths. Because Lean uses mimalloc, ASan does not instrument every runtime allocation, and leak detection is disabled. Ownership evidence therefore also includes explicit refcount/exclusivity checks, unchanged original bytes and distinct output storage in borrowed/output aliases, with and without an observer for ordinary shared values. Marked-linear borrowed aliases have a single output owner; tests exclude additional observing owners, which violate runtime linearity. Shared prefixes, marked-linear aliases, exclusive growth and zero-buffer reuse have direct C checks.

Exact tests cover multi-element sparse maps against an independent hash map, repeated/missing IDs, malformed slices, machine-size boundaries, exhaustion before initialization, partway through insertion and before the charged fallback. The 64-collider indexed case costs 2,272 work/1,024 bytes; 65 colliders fall back after 2,530 work/2,048 bytes. The emitted 1,134 records were compared before regeneration and differ only in charged work fields. Failed setup, lint and test-build records remain separately identified in the capsule.

Windows/macOS execution, broader fields/extensions, parallel scaling, larger native matrix coverage, probabilistic/trace features, complete theory and held-out/comparator acceptance remain required. The issue stays open. No fastest-open-source or language/runtime-impossibility claim is made.


- [column-revised-67e9835420ef.tar.gz](raw/column-revised-67e9835420ef.tar.gz): `913a8786886fc1484ab83a67ad64fec2703bb5ee10f613d683c1c22e87aae5c1`; exact revised, initial and baseline sources, validation, all timing rows and separate profiles.

- [column-followup-11012.tar.gz](raw/column-followup-11012.tar.gz): `bdc74329811f73753a3b805d5431485d1939fd87fc53eeae6a7f670d5f3a5441`; benchmark route/cap changes, strengthened ownership tests, eight sanitizer variants, smoke checks and direct-route profiles. All 56 payload digests were checked after packing.
