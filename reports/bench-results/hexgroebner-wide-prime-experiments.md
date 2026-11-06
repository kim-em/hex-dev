# Wide-prime preliminary experiments

The gather-only eight-lane implementation is retained as an unselected experiment. Reimer-8 over 𝔽₂₁₄₇₄₈₃₆₄₇ improved in both adjacent comparison orders (candidate ratios 0.7766 and 0.8868), but contiguous wide-prime kernels regressed by 8–9%. The selected implementation adds contiguous loads/stores and preserves AVX2 for short rows; its evidence is in [the wide-prime report](hexgroebner-wide-prime.md). Ratios from these stages are not multiplied.

The preliminary archive retains all 128 system processes and 64 complete-output/counter comparisons, all 24 matched kernel observations and flags, the four targeted Reimer processes, source/compiler identities, boundary-test records and the unsuccessful held-out campaign.

That held-out campaign stopped when the shared filesystem filled, before process 73 of 108. All 72 completed process logs and available full outputs, basis files and memory observations are retained. The collector had not published its in-memory exact nanosecond durations; those values are unavailable. Its printed rounded durations and a per-file digest audit remain in the archive. No complete held-out aggregate is asserted for this campaign. The selected implementation's distinct campaign uses exact per-sample journals and atomic metadata publication.

The first external boundary-test generator failed to compile because its generated C string had a newline-escaping error. The original source, failed build record and corrected Clang/GCC runs are retained. The corrected tests each exercise 108 direct protected-page cases against the actual eight-lane function.

[Archive parts index](raw/f4-wide-experiments-e252f5512360.parts.json): assembled SHA-256 `f4a12f72a606765c2361138080d4a69be8ee5018cfd134e9a965b845f378386f`, 359,441,176 bytes. Each part is at most 64 MiB; the index records every part's size and digest. The archive includes its pack script and a SHA-256 manifest for every payload.

These observations are unchecked candidate-production measurements. They do not establish certificate-generation, certification or kernel-checking performance, empirical complexity acceptance, overall fastest-open-source performance or a language/runtime limitation.
