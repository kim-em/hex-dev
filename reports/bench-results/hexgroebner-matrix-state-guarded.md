# Bounded matrix continuation: guarded five-size kernels

These measurements bind source fingerprint `85acda276a94`, snapshot `fcf4802276185cd0e619f248ee6c5353fad8b424`, and benchmark SHA256 `48c1162649314379c27f484fd91b53bfb928ee6ac6a7cc5ff32dd8503235ad64`. The base is `07c321da14f78bc7744920a4b7b23c0ca102b492`, with exact family source blobs in the capsule. Both arms use the same fresh detached ELF. A uses `Elimination.reference`; B uses the guarded twenty-object `MatrixState` continuation.

The Cauchy matrices are over prime 65537 and have full rank. The first half of their rows are reducers. Build-time checks require both success flags and complete tuple equality at sizes 16, 64, 128, 256, 512 and 1024; the rank predicate checks the actual reducer count. Outputs include decoded coefficients, target flags, multipliers, sugars and every resource counter. Preparation is excluded; validation, allocation, elimination and full result consumption are included.

Five-size sweeps extend the unresolved four-size cubic-model fits. This is the first campaign for this configuration, with adjacent AB/BA whole sweeps and one trial per sweep. All twenty completed rows, including outliers and signal-floor flags, are retained. No unchanged repeat or cross-source pooling is used. Earlier four-size measurements retain their erroneous rank flag in separate capsules.

The shared host is chungus2, an EPYC 9455 with 96 logical CPUs. One algorithm thread is requested; CPU 37 is automatically leased. Loads (1/5/15 minutes) are [11.09228515625, 16.283203125, 15.21875] → [11.8251953125, 15.6962890625, 15.0830078125]. No host-activity filtering is applied. The inner target is four seconds and the per-call cap is thirty-two seconds; actual batch durations, repeat counts, effective targets and spawn floors remain in the exports.

| Block | Columns | Reference ms/call | Continuation ms/call | B/A | Reference RSS KiB | Continuation RSS KiB |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 0 | 64 | 0.2923 | 0.2171 | 0.7428 | 61800 | 62200 |
| 0 | 128 | 1.1628 | 0.9910 | 0.8522 | 62932 | 62872 |
| 0 | 256 | 5.7636 | 5.3455 | 0.9275 | 65320 | 66872 |
| 0 | 512 | 35.4173 | 33.0645 | 0.9336 | 73816 | 76488 |
| 0 | 1024 | 253.2733 | 232.9600 | 0.9198 | 108468 | 111724 |
| 1 | 64 | 0.2939 | 0.2149 | 0.7313 | 64100 | 68292 |
| 1 | 128 | 1.1612 | 0.9805 | 0.8444 | 68284 | 65652 |
| 1 | 256 | 5.8012 | 5.2543 | 0.9057 | 68096 | 67948 |
| 1 | 512 | 34.3068 | 32.8684 | 0.9581 | 76480 | 76460 |
| 1 | 1024 | 230.6286 | 231.5594 | 1.0040 | 117444 | 110800 |

All complete result hashes agree. Two rows are flagged below the signal floor:
block 0 reference at 256 columns (128 repeats, 0.738-second batch) and block 1
continuation at 256 columns (64 repeats, 0.336-second batch). They remain in
the table and raw exports. Exported cubic-model verdicts and normalized slopes:

| Block | Arm | Verdict | Slope |
| --- | --- | --- | ---: |
| 0 | A | inconclusive | -0.555280 |
| 0 | B | inconclusive | -0.374006 |
| 1 | A | inconclusive | -0.453460 |
| 1 | B | inconclusive | -0.478612 |

These finite shared-host timings do not establish an asymptotic model or external-comparator leadership. The public F4 route remains unchanged. Frozen F4 compute/reference SHA256 values are `fb8e8c73858b122576cc3fe631a47876d10c6af06ec86b6d4ad93d980b76b617` and `7936068cb67aab7824434fe4e2bfeb5f3ecadf13427e3f63b01ccd852f338ad0`, byte-identical to the twenty-object refactoring source. Its [full-system observations](hexgroebner-matrix-state-reviewed.md) remain source-specific; they do not measure F4 using this continuation. Candidate production, certificate generation, independent verification and kernel checking are not measured by the standalone kernel timings.

The guarded implementation passes all library/theory/conformance builds, independent oracles, both 1,134-case drivers and project checks. Four Clang and four GCC sanitizer variants each report 305,466 native continuation calls and positive fast-phase counts (447,376 input, 260,343 scan, 74,067 gather). Tests compare multi-quantum paused states, saved snapshots, late exhaustion and the 65,536/65,537-column boundary. Sanitizer coverage is limited by mimalloc and leak detection is disabled; explicit ownership/snapshot checks supplement it. Benchmark-only changes additionally pass their build, full benchmark verification and phase/header/line checks.

`advance_spec` and `finish_spec` prove the Lean phase model equations. Agreement with C remains an audited native obligation. Completed execution has not yet been proved equal to `Elimination.reference`; that proof is required before selecting the continuation in F4. The kernel replay example audits to `propext` and `Quot.sound`; the [range-loop reproduction](hexgroebner-range-replay.md) records its module visibility workaround and upstream request.

[Raw capsule](raw/matrix-state-85acda276a94.tar.gz): SHA256 `ba6f00821b1ddf1b4172528f1e68ffef9f1aae01fd62b0f23d29eaeb85cb211d`; 155 Git source blobs and 256 payload digests verified after packing.
