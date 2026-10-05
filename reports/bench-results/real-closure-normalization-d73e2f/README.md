# Short product-chain normalization comparison

Both arms compute `(1 + X)^(2n)` at the same validated positive root of `2X^n − 1` in `(0,1)`, over Rat. Clean retains the integer representative; eager reduces each product modulo the monic working head `X^n − 1/2` before using the same production zero/sign packing. The original owner, descriptor, coefficient backend and prepared Sturm handle are shared. The leading coefficient 2 disables production monic reduction, so this comparison covers the non-monic regime that production leaves unreduced. Preparation is outside timing. Both arms receive one untimed warm-up call.

## Capture and analysis

Clean source `d73e2f7e1bb7f29493a22d27c941b0e2e6e543ab`, published tag `issue-10378-normalization-source-d73e2f`. The executable SHA-256 is `a3897599b1607c9fdef3830e4b77e843ec84f7a5bc83b89c25afcf188d6cb739`. The original capture and 120365952-byte snapshot remain at `/home/kim/.codex/tasks/hex-10378/normalization-capture-d73e2f`. The archive copies every command stdout/stderr, original manifest and derived analysis; `archive.json` binds their digests and identifies the retained snapshot omitted from git.

The published packaging branch is rebased onto newer main. Four imported source files gained checked-restoration constructors and associated proofs (`Algebraic`, `Descriptor`, `QueryHandle`, `Sturm.Basic`); existing measured arithmetic and query bodies are unchanged. The timings belong to the retained tagged source and executable, not a later rebuilt binary.

Six fixed trial-major blocks visit degrees 2, 4, 8, 16 in that order, with adjacent clean/eager arms and alternating AB/BA order. All 48 arms completed, with no discarded samples or rerun. Each child targets a final batch of at least 0.5 seconds; the 600-second child timeout is operational. Source/result bindings and independent exact checks pass. The preregistered analyzer uses total nanoseconds divided by inner repeats, pairs arms within each block, and defines the six-value median as the mean of the middle two sorted values. Direction is consistent only when all six paired ratios lie strictly on the same side of 1.

Host: chungus2, AMD EPYC 9455, x86_64 Linux; automatically leased CPU 48, single-CPU affinity. Initial host load was 2.334/2.662/3.649. Each arm retains its own observed load. Lean 4.35.0-rc3 and lean-bench `8a37daf` are bound in the manifest, alongside dependency pins and Python version. Host activity was recorded and no quiet-core selection or rejection threshold was used.

| n | Clean median ms | Eager median ms | Paired eager/clean median | Full paired range | Inner repeats clean/eager |
| ---: | ---: | ---: | ---: | ---: | --- |
| 2 | 0.016630 | 0.010078 | 0.606163 | 0.601539–0.614444 | [32768, 32768] / [65536, 65536] |
| 4 | 0.252485 | 0.228223 | 0.902666 | 0.891604–0.911305 | [2048, 2048] / [4096, 4096] |
| 8 | 1.876674 | 1.705376 | 0.911412 | 0.886289–0.916282 | [512, 512] / [512, 512] |
| 16 | 18.290790 | 17.091544 | 0.929202 | 0.914060–0.953264 | [32, 32] / [32, 32] |

Eager is faster in all six pairs at each degree in this observed family. The archive retains the absolute per-arm ranges; these host-specific observations carry no significance test, asymptotic fit or regression-budget verdict.

## Exact arithmetic and representation growth

Pinned python-flint 0.9.0 and Z3 4.15.4 independently check both stored results, every prefix, the literal head and monic working head, canonical fractions, selected-root equality and positive signs. Fresh snapshot emission byte-matches all four committed fixture rows, and all eight registered result hashes pass. The exact clean query is `2^max(k−n+1,0)` times the eager remainder at step k. Thus both query routes see the same polynomial up to a positive scalar.

| n | Final stored degree clean/eager | Stored numerator bits clean/eager | Query numerator bits clean/eager |
| ---: | ---: | ---: | ---: |
| 2 | 4 / 1 | 3 / 5 | 6 / 5 |
| 4 | 8 / 3 | 7 / 8 | 11 / 8 |
| 8 | 16 / 7 | 14 / 15 | 23 / 15 |
| 16 | 32 / 15 | 30 / 31 | 47 / 31 |

All 64 prefixes retain stored and actual query coefficients; the exact oracle records maximum numerator/denominator bits, total coefficient bits and serialized coefficient bytes for each arm and query. Eager stored denominators are at most 4. The oracle verifies stored numerators stay below the hash truncation bound.

## Scope and reproduction

This family has one Rat extension and only 2n linear-seed products. The selected interval has one root, so it uses the direct Sturm route and exercises no BKR matrix solve. All degrees use constant or linear fast paths for the initial prefixes. Later queries at degree 2 remain linear after reduction; later queries at degrees 4–16 use the prepared Sturm route. These degrees must not be treated as one asymptotic family. The clean stored degree reaches only 2n, and eager denominator growth is small. The study does not cover nested extensions, longer chains, tower8, MetiTarski, Rioboo/nlsat expressions, all operation counters or a production normalization policy decision.

The fixed registrations bind arithmetic result hashes for this descriptive comparison. They do not discharge Phase4 scaling, absolute time-budget or full-tower coverage requirements.

The analyzer refuses to overwrite `analysis.json`; move that derived file aside in whichever directory is being analyzed. For the full original capture, run the analyzer from the published source tag against the retained external directory. To analyze this archive, restore the omitted snapshot under its original filename after checking its SHA-256, then run `python3 scripts/bench/analyze_real_closure_normalization.py reports/bench-results/real-closure-normalization-d73e2f`. The original manifest is preserved verbatim, including original absolute command paths. Independent fixtures can be checked with the pinned oracle command and the benchmark executable can emit them with no arguments.
