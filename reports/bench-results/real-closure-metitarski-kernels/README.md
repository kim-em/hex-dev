# MetiTarski root-operation profiles

These profiles use the exact degree-15 MetiTarski input and its second polynomial `Y³ + α³ + 1`, where α is the least first-stage root. The independent Phase4 oracle binds the original coefficients and least-root interval. These are profiling observations on the shared host, not scientific timing distributions or complete Phase4 readiness.

The first operation includes complete root production and its root-count check. The second operation uses the actual retained native coefficient context; preparing the first root and second polynomial occurs before the timed regions. The odd-degree ladder in the benchmark extends this second input, with rung three retaining the exact paper input.

Both captures use 1000 Hz `cycles:u` sampling, monotonic timestamps and DWARF stacks. LeanBench emits kernel regions around each operation; hashing, preparation, sidecar writes and exit are excluded by the filter. CPU leases select a permitted CPU without testing its load. Manifests retain load, affinity, tool versions, clean source commit, build output, copied executable hash and every capture/postprocessing command. Raw profiles and executable snapshots remain at their recorded local paths.

| Stage | Source commit | CPU | Retained samples | Rejected samples | Filter diagnostics |
| --- | --- | ---: | ---: | ---: | --- |
| First | `9f9e291c733a9039a9f44e88ae623dd66d6e0c4a` | 80 | 21752 | 10 | passed |
| Second | `52f769a56779ed0efe8a128683405aa29d295623` | 47 | 2524 | 4962 | passed |

The first capture attributes 94.90% of samples inclusively to root comparison/sorting, including 94.31% to descriptor comparison construction. The second attributes 81.81% inclusively to algebraic coefficient sign evaluation. Inclusive shares overlap along call stacks and must not be added. GMP leaf shares are 50.35% and 43.42%; allocation leaf shares are 27.30% and 36.81%, respectively. The summaries retain leaf categories, unresolved shares, demangled inclusive stacks and filter calibration/sensitivity diagnostics.

The first profile source is retained by tag `issue-10378-metitarski-first-kernel-source`; the second by `issue-10378-metitarski-second-kernel-source`. The first benchmark body is unchanged between those source commits. The runner now validates the schema’s string result hash `0x1` before postprocessing. Both accepted captures returned that hash and status `ok`.

All captures are retained. `second-io-failed.manifest.json` records a rejected adaptation: the parametric macro registered an IO action as a pure result instead of executing it, producing nearly empty regions and reaching the region limit. Its functional verification did not validate execution. The pure function fixes this boundary. `second-validation-failed.manifest.json` retains the completed pure capture whose launcher rejected the string hash by comparing it to integer 1. `second.postprocess.manifest.json` records validation and postprocessing of that same successful capture, retaining the original manifest hash and every command; no measurement was repeated to repair the parser.

The workload archive/correction for tower8, ordinary fixed trial-major timing studies, matched clean/eager comparisons, growth/counter studies and the final Phase4 audit remain required.

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
