# MetiTarski root-operation profiles

These profiles use the exact degree-15 MetiTarski input and its second polynomial `Y³ + α³ + 1`, where α is the least first-stage root. The independent Phase4 oracle binds the original coefficients and least-root interval. These are profiling observations on the shared host, not scientific timing distributions or complete Phase4 readiness.

The first operation includes complete root production and its root-count check. The second operation uses the actual retained native coefficient context; preparing the first root and second polynomial occurs before the timed regions. The odd-degree ladder in the benchmark extends this second input, with rung three retaining the exact paper input.

Both captures use 1000 Hz `cycles:u` sampling, monotonic timestamps and 8192-byte DWARF stacks. OS kernel time, including page faults, is excluded. Future captures request 65528-byte stacks. LeanBench emits timed regions around each benchmark operation; hashing, preparation, sidecar writes and exit are excluded by the filter. CPU leases select a permitted CPU without testing its load. Manifests retain load, affinity, tool versions, clean source commit, build-output hashes, copied executable hash and every capture/postprocessing command. Raw profiles and executable snapshots remain at their recorded local paths.

| Stage | Source commit | CPU | Retained samples | Rejected samples | Filter diagnostics |
| --- | --- | ---: | ---: | ---: | --- |
| First | `9f9e291c733a9039a9f44e88ae623dd66d6e0c4a` | 80 | 21752 | 10 | passed |
| Second | `52f769a56779ed0efe8a128683405aa29d295623` | 47 | 2524 | 4962 | passed |

The first capture attributes 94.90% of samples inclusively to root comparison/sorting, including 94.31% to descriptor comparison construction. The second attributes 81.81% inclusively to algebraic coefficient sign evaluation. Inclusive shares overlap along call stacks and must not be added. They are lower bounds: 4.74% of first-stage stacks and 12.36% of second-stage stacks omit the benchmark frame, consistent with truncated deep DWARF stacks. Symbol resolution and stack completeness are distinct diagnostics. GMP leaf shares are 50.35% and 43.42%; allocation leaf shares are 27.30% and 36.81%, respectively. The summaries retain leaf categories, unresolved shares, demangled inclusive stacks and filter calibration/sensitivity diagnostics.

The first profile source is retained by tag `issue-10378-metitarski-first-kernel-source`; the second by `issue-10378-metitarski-second-kernel-source`. The first benchmark body is unchanged between those source commits. The runner now validates the schema’s string result hash `0x1` before postprocessing. Both accepted captures returned that hash and status `ok`.

All captures are retained. `second-io-failed.manifest.json` records a rejected adaptation: the parametric macro registered an IO action as a pure result instead of executing it, producing nearly empty regions and reaching the region limit. Its functional verification did not validate execution. The pure function fixes this boundary. `second-validation-failed.manifest.json` retains the completed pure capture whose launcher rejected the string hash by comparing it to integer 1. `second-unbound-postprocess.manifest.json` retains the initial recovery whose tooling was not bound to a clean commit. The accepted `first.postprocess.manifest.json` and `second.postprocess.manifest.json` run the committed `--postprocess` mode at `26eda1c3eb`, retained by `issue-10378-metitarski-postprocess-source`. They validate each original artifact hash and clean measurement row, record the clean processor and filter revisions, and bind each resulting summary by SHA-256. The second original manifest hash is `c276c4a8929df3e3aa3e7ee4fcf54580acf0181ba12d3828911f1972a1415c58`, matching the retained validation-failure manifest. Original captured files remain unmodified. The earlier unbound recovery added derived files to the second raw directory; the committed mode writes fresh derived files into its output directory. Future captures verify the actual clean dependency checkout before building. No measurement was repeated. Counts, leaf categories, inclusive function shares and filter diagnostics reproduce the original summaries; equal-share inclusive rankings now use deterministic lexical tie ordering, and summary paths point to the new derived artifacts.

The workload archive/correction for tower8, ordinary fixed trial-major timing studies, matched clean/eager comparisons, growth/counter studies and the final Phase4 audit remain required.

The measured branch began at `b3d6da1648`, before the final rebase onto
main `3c40c9c99f`. The intervening tree adds canonical owner/cache factories,
base embedding theorems and isolation-policy APIs. The legacy root producer,
selected coefficient arithmetic and shared SignDet/Sturm/dense-polynomial
source are unchanged; the existing `Isolation.lean` delta is documentation.
These profiles describe the retained source snapshots above, rather than a
new capture of the rebased tree or a claim about all new cache/policy paths.

## Reproducibility and diagnostics

Both captures ran on chungus2, x86_64, AMD EPYC 9455 48-Core Processor,
Linux 6.12.111 / glibc 2.42. The pinned lean-bench dependency is
`8a37daf1074c3bdbd0da479b55538bad4a0022db` (version 0.1.0); the clean
filter revision is `9356baa2f5757ee40320a897bd284914d5bb9f5e`.
Samply is 0.13.1, perf 7.2.8 and Lean 4.35.0-rc3. Inputs are deterministic,
with no random seed. Full capture and postprocessing commands appear in the
manifests; raw snapshots and every command's output remain at their recorded
external paths.

| Filter output | First | Second |
| --- | ---: | ---: |
| Target window (seconds) | 15 | 3 |
| Timed regions | 3 | 17 |
| `total_timed_ms` | 21787.23241 | 2524.121549 |
| `calibration_residual_ms` | 0.9444329962 | 0.9268020019 |
| `retained_samples_bench_thread` | 21752 | 2524 |
| `sensitivity.verdict` | passed | passed |
| Benchmark frame coverage | 95.26% | 87.64% |

The first profile's dominant cost is sorting three roots, through
`Root.sortBy` / `Root.compare` and descriptor comparison/reencoding. This
is an unexpected dominant cost relative to isolation itself. The concrete
[upstream comparison concern](https://github.com/kim-em/hex-dev/issues/10377#issuecomment-5983809923)
requests investigation of checked isolation/reencoding reuse and separated
intervals from the descriptor owner. The tower does not duplicate that API.

The second profile is dominated by algebraic sign/zero checks during
`Element.ofPoly` and coefficient arithmetic. Signed-remainder construction
and dense pseudo-division perform these tests over the retained selected-root
context; multiplication accounts for 56.10% inclusively. Eager child-context
construction in `Tower.Context.adjoin` accounts for 39.26%. These observations
identify concrete costs, but do not establish the effect of a clean/eager
storage ablation.

## First: top twenty inclusive Hex functions

| Function | Inclusive sample share |
| --- | ---: |
| `Hex.RealClosure.Bench.runMetiFirst` | 95.26% |
| `Hex.RealClosure.Tower.Context.roots?` | 95.26% |
| `Hex.RealClosure.Roots.roots?` | 95.17% |
| `Hex.RealClosure.Isolation.Root.compare` | 94.90% |
| `Hex.RealClosure.Isolation.Root.insertBy` | 94.90% |
| `Hex.RealClosure.Isolation.Root.sortBy` | 94.90% |
| `Hex.SignDet.Descriptor.buildComparison` | 94.31% |
| `Hex.SignDet.Descriptor.buildReencoding` | 94.28% |
| `Hex.SignDet.buildPrepared` | 74.28% |
| `Hex.SignDet.Replay.check` | 59.61% |
| `Hex.SignDet.Node.check` | 59.55% |
| `Hex.SignedRemainderChain.check` | 56.51% |
| `Hex.SignDet.checkMoment` | 52.62% |
| `Hex.TarskiCertificate.checkCached` | 50.91% |
| `Hex.TarskiCertificate.checkQuery` | 50.23% |
| `Hex.TarskiCertificate.checkBody` | 50.04% |
| `Hex.SignedRemainderChain.checkStep` | 48.69% |
| `Hex.DensePoly.mulImpl` | 36.23% |
| `Hex.SignDet.Descriptor.build` | 35.26% |
| `Hex.SignDet.buildTreeFrom` | 34.65% |

## Second: top twenty inclusive Hex functions

| Function | Inclusive sample share |
| --- | ---: |
| `Hex.RealClosure.Tower.Context.roots?` | 87.80% |
| `Hex.RealClosure.Bench.runMetiSecond` | 87.64% |
| `_private.HexRealClosure.Bench.0_Hex.RealClosure.Bench.initFn_.lam_2.00_@.HexRealClosure.Bench.2049614086__hygCtx_.hyg.37__boxed` | 87.36% |
| `Hex.RealClosure.Algebraic.Context.signPoly` | 81.81% |
| `Hex.RealClosure.Algebraic.Element.ofPoly` | 81.74% |
| `Hex.SignedRemainderChain.build` | 71.71% |
| `Hex.DensePoly.pseudoDivMod` | 69.57% |
| `Hex.SignedRemainderChain.buildAux` | 68.34% |
| `Hex.DensePoly.positivePseudoDiv` | 63.51% |
| `Hex.DensePoly.pseudoDiv` | 59.07% |
| `Hex.RealClosure.Algebraic.Element.mul` | 56.10% |
| `Hex.Sturm.queryPrepared` | 53.84% |
| `Hex.RealClosure.Algebraic.Context.singleSign?` | 53.72% |
| `Hex.RealClosure.Roots.assemble` | 49.29% |
| `Hex.RealClosure.Roots.roots?` | 49.13% |
| `Hex.RealClosure.Isolation.complete?` | 43.74% |
| `Hex.RealClosure.Roots.factorEntries` | 43.26% |
| `Hex.RealClosure.Tower.Context.adjoin?` | 39.74% |
| `Hex.RealClosure.Tower.Context.adjoin` | 39.26% |
| `Hex.RealClosure.Tower.Root.ofSelection` | 39.18% |
