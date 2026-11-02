# Bounded matrix continuation: source c5e1f57fbe8c

This source has a twenty-object continuation. Its content fingerprint is `c5e1f57fbe8c`, snapshot `6bea8e1df53d2a01b8304985fb8e2b36629ec268`, and monorepo base `07c321da14f78bc7744920a4b7b23c0ca102b492`. The raw capsule supplies the exact measured family overlay. The fresh standalone benchmark SHA256 is `edc7f4eeff56686cafab9ef5107f40c00a98ff0ca5631498a1645a69fe99380c`.

The four-size benchmark has an erroneous Boolean success predicate: it expects zero reducer rank although half the input rows are reducers. Both arms return `false` together with complete successful echelon rows and all counters; an error branch would return empty arrays instead. Complete output hashes agree at every size. These records retain the false flag and are historical measurements of that exact source, rather than validation of the predicate. The corrected five-size benchmark checks the actual reducer count and requires success and complete equality at every timed size. Sources are kept separate.

The shared EPYC 9455 host has 96 logical CPUs. Each arm requests one algorithm thread and leases a CPU automatically; no completed observation is filtered by host activity. Both matrix arms are in one fresh detached ELF. Preparation is excluded; validation, allocation, elimination, decoded rows, metadata and every resource counter are included. Adjacent whole sweeps alternate AB/BA, one trial per sweep. The registered inner target is four seconds, not a claim that each actual batch lasts four seconds; the call cap is thirty-two seconds. Actual repeat counts, spawn floors, effective targets and RSS are retained.

| Block | Columns | Reference ms | Continuation ms | B/A |
| --- | ---: | ---: | ---: | ---: |
| 0 | 64 | 0.2865 | 0.2068 | 0.7218 |
| 0 | 128 | 1.1322 | 0.9259 | 0.8178 |
| 0 | 256 | 5.6401 | 5.0332 | 0.8924 |
| 0 | 512 | 33.6024 | 31.4378 | 0.9356 |
| 1 | 64 | 0.2872 | 0.2060 | 0.7173 |
| 1 | 128 | 1.1291 | 0.9275 | 0.8215 |
| 1 | 256 | 5.6325 | 5.0388 | 0.8946 |
| 1 | 512 | 33.5734 | 31.3181 | 0.9328 |

All sixteen rows complete above the signal floor on CPU 26; all four cubic-model fits are inconclusive. Host loads (1/5/15 minutes) are [3.6923828125, 15.572265625, 24.111328125] at start and [3.078125, 13.57080078125, 22.9814453125] at end. No unchanged repeat is used. The finite timings do not establish an asymptotic model or a uniform speedup.

Full-system before/after sweeps compare the column-index baseline against the shared-helper extraction used by this continuation source. F4 still selects the existing matrix route, so these sweeps do not measure F4 using the new continuation. Fresh compute SHA256 values are baseline `4018867411b786bfcdafcdffd13d0412d8c36504f09e997b30400d126c391be1` and measured `fb8e8c73858b122576cc3fe631a47876d10c6af06ec86b6d4ad93d980b76b617`; measured reference-driver SHA256 is `7936068cb67aab7824434fe4e2bfeb5f3ecadf13427e3f63b01ccd852f338ad0`. All sixty pairs (120 processes) have equal complete reduced bases and every algorithm/resource counter, with no failures or timeouts. Each suite has one campaign; the analysis filename does not imply pooling across sources.

| Suite | Pairs | Candidate GM B/A | Process GM B/A | Family-balanced process B/A | Candidate ratio range | Process ratio range |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| small | 32 | 0.9349 | 0.9201 | 0.9234 | 0.0431–35.6024 | 0.1465–6.5723 |
| medium | 28 | 0.9697 | 1.0036 | 1.0036 | 0.1933–6.3565 | 0.2660–2.5233 |

| Suite/family | Candidate GM B/A | Process GM B/A |
| --- | ---: | ---: |
| small/cyclic | 0.9512 | 0.8974 |
| small/dense-quadratic | 0.3499 | 1.2386 |
| small/eco | 0.8316 | 0.8014 |
| small/kat | 2.6250 | 1.2637 |
| small/minrank | 0.3115 | 0.4123 |
| small/noon | 1.4400 | 0.9930 |
| small/reimer | 1.8833 | 1.2416 |
| medium/cyclic | 1.1516 | 1.1526 |
| medium/dense-quadratic | 1.6095 | 0.9932 |
| medium/eco | 1.0801 | 1.0428 |
| medium/kat | 0.8890 | 0.9044 |
| medium/minrank | 0.7184 | 1.0948 |
| medium/noon | 0.8032 | 0.9871 |
| medium/reimer | 0.7851 | 0.8790 |

Small-suite loads are 15.46/17.42/26.76 → 16.70/17.65/26.78 on CPU 14; medium-suite loads are 16.70/17.65/26.78 → 25.33/19.62/27.14 on CPU 21. Large individual ratios remain in the evidence. These shared-host observations do not isolate a cause for variability or establish an external performance milestone. Full raw inputs, outputs, process wall time, RSS, failures and sample metadata are retained. Certificate generation, independent certification and kernel checking are excluded from the candidate timings and are not assigned these ratios.

Library/theory builds, independent oracles, both 1,134-case drivers, all 36 benchmark checks, DAG/phase/release/header/line checks and four Clang plus four GCC ASan/UBSan variants pass for this source. ASan does not instrument every mimalloc allocation and leak detection is disabled; explicit ownership/snapshot comparisons supplement it. The native/model equations do not prove completed execution equal to the legacy reference; that proof remains required before F4 integration.

- [Raw capsule](raw/matrix-state-c5e1f57fbe8c.tar.gz): SHA256 `2b343ccd8dcdf838b82ab084b6e8831b93e2e3ac027003af638d0561a2b130fb`; 154 measured and 149 baseline Git blobs, 826 verified payload digests.
- [Nineteen-object measurements](hexgroebner-matrix-state-initial.md) use a separate source and capsule.
