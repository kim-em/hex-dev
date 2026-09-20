# Primality replay attribution

PrimeCert's fixed-window powering removes the arithmetic advantage in the
[older binary-comparator measurement](hex-primality-windowed-replay.md).
Hex's remaining replay cost includes its first-class certificate traversal,
canonical factor checks, bounded products, and table membership. The supplied
curve certificates also use different witness bases. These costs must be
separated from automatic construction and elaboration.

On the retained four-block repeat, the change reduces Curve25519 supplied-proof
replay from 5.601 to 4.532 ms and Curve448 from 10.357 to 9.240 ms.

Hex's cube-root arithmetic checkers now use the same bounded positive product
and primitive comparisons as its square-root checker. Unconditional equalities
with the original definitions preserve every accepted and rejected input;
compiler simplification retains the original native implementations. The
Boolean checker, soundness theorem, search budgets, factor subsets, and
construction suggestions remain unchanged.

## Complete kernel replay

The before/after comparison uses the same eight certificate literals and Lean
4.34.0 in both arms. Each call checks the complete expanded local proof against
its declared type with a fresh `Lean.Kernel.check`. Local opaque auxiliary
proofs are expanded, pending checks are drained, and no local proof dependency
may remain. Imported library theorems remain dependencies in both systems.
False equality, corrupted subject, and zero-witness controls must be rejected.
Imports, literal elaboration, construction, and expansion are outside this timer.

| Input | Before (ms) | After (ms) |
|---|---:|---:|
| family-31 | 0.557 | 0.591 |
| family-61 | 0.498 | 0.500 |
| family-123 | 0.866 | 0.797 |
| family-256 | 1.291 | 1.308 |
| family-511 | 2.826 | 2.689 |
| family-512 | 3.181 | 3.229 |
| Curve25519 | 5.601 | 4.532 |
| Curve448 | 10.357 | 9.240 |


The primary [paired run](bench-results/hex-primality-10292-kernel-pair.json)
is retained in full. It includes broad host timing variation and overlap with
a repository build. The [one unchanged repeat](bench-results/hex-primality-10292-kernel-repeat.json)
uses the same four-block schedule; the table reports its medians, without
pooling or removing samples from either run. Curve25519 improves in all four
repeat pairs and Curve448 in three of four. The unchanged square-root inputs
are controls, not evidence of improvements to those paths.

The [PrimeCert comparison](bench-results/hex-primality-10292-primecert.json)
uses the original Hex certificates and compact PrimeCert certificates with the
same selected factors and interval/non-square witnesses. PrimeCert uses one
common base per node; this is not yet an identical-witness comparison.

| Input | Hex after (ms) | PrimeCert (ms) |
|---|---:|---:|
| family-31 | 0.563 | 0.279 |
| family-61 | 0.503 | 0.287 |
| family-123 | 0.796 | 0.553 |
| family-256 | 1.355 | 1.027 |
| family-511 | 2.686 | 2.381 |
| family-512 | 3.418 | 2.612 |
| Curve25519 | 4.535 | 3.537 |
| Curve448 | 9.297 | 6.436 |


## Components and certificate shape

[Component probes before](bench-results/hex-primality-10292-attribution-before.json)
and [after](bench-results/hex-primality-10292-attribution-after.json) check
individual groups of obligations with fresh kernel checkers. They are
attribution probes, not additive samples of a complete proof: arithmetic
contains witnesses, and changing expression shape can change kernel sharing.
In particular, isolated literal power equalities do not preserve all sharing
of related exponents in a full witness check. Their times must not be summed
or subtracted to derive a percentage profile.

| Component | Curve25519 before / after (ms) | Curve448 before / after (ms) |
|---|---:|---:|
| Complete Boolean check | 4.960 / 4.136 | 9.911 / 8.701 |
| All node arithmetic, including witnesses | 4.693 / 3.815 | 9.464 / 8.255 |
| Witness conditions alone | 3.152 / 3.143 | 7.267 / 7.853 |
| Table leaves before | 0.162 | 0.199 |
| Canonical subjects before | 0.304 | 0.405 |
| Positive-product worker in isolation | 0.374 | 0.528 |

The product row probes `pockProduct`, already used by the square-root arm;
the old cube-root arms instead used the nested `Option`-returning `certProduct`.
The arithmetic-minus-witness contrast motivated optimizing cube-root
products and comparisons. The same-certificate paired experiment above
checks the resulting complete-proof improvement. The component probes were
separate runs, so their before/after columns alone are not a paired estimate.

| Input | Non-leaf nodes | Leaf occurrences | Factor entries | Hex powers | Common-base powers |
|---|---:|---:|---:|---:|---:|
| family-31 | 1 | 2 | 2 | 3 | 3 |
| family-61/123/256/511 | 1 | 1 | 1 | 2 | 2 |
| family-512 | 2 | 2 | 3 | 5 | 5 |
| Curve25519 | 3 | 6 | 8 | 12 | 11 |
| Curve448 | 4 | 9 | 12 | 20 | 16 |

The counts are generated from the retained literals, including off-by-one
stored exponents. Curve25519 repeats one leaf subject and Curve448 repeats
three; neither has a repeated non-leaf subtree. Hex traverses child certificates
and factor lists, with separate ordering, product, and witness folds. PrimeCert
looks up factors in its elaboration-time dictionary and emits a proof composed
from `PocklingtonPred` constructors. This moves dictionary lookup and proof
assembly into elaboration, but each arithmetic premise is still checked by the
kernel. Imported small-prime proofs are available directly to PrimeCert through
997; Hex reduces its verified bit lookup. Neither replay timer reruns the
proof of the imported sieve/table.

Hex shares the Fermat leg only for adjacent equal bases. The corpus has four
such reuses on each curve before matching; common bases raise these to five
and eight. [Matched sources](bench-results/hex-primality-10292-matched-sources.json)
select the same first valid common base from the translator's finite candidate
list, preserving every factor, exponent, child, and interval witness.
Their generation is untrusted; the kernel benchmark validates every proof.

The [adjacent original/common-base experiment](bench-results/hex-primality-10292-base-pair.json)
checks both Boolean proofs in the same process and reverses their order in odd
blocks. Curve25519 takes 4.480 / 4.393 ms and Curve448 10.355 / 7.661 ms
(original / common-base medians). Changing to a larger common base can offset
the saved power; a power-count reduction is not itself a speedup estimate.
These supplied-certificate changes are not applied to automatic construction.

The separate [matched package run](bench-results/hex-primality-10292-matched-kernel.json)
retains all 64 checks and negative controls. It is noisy, including a reversal
on the unchanged family-511 control; its timings are not pooled with the
original-base package run or used to estimate the benefit of changing bases.

| Matched input | Hex after (ms) | PrimeCert (ms) |
|---|---:|---:|
| family-31 | 0.849 | 0.346 |
| family-61 | 0.874 | 0.320 |
| family-123 | 1.176 | 0.593 |
| family-256 | 1.537 | 1.120 |
| family-511 | 3.505 | 3.752 |
| family-512 | 4.725 | 3.089 |
| Curve25519 | 12.518 | 6.719 |
| Curve448 | 23.730 | 11.143 |


The eight shared certificates have no `pock3Sieve` nodes and therefore no
nontrivial divisor-exclusion loops. This is a coverage limitation, not an
attribution of zero sieve cost to general certificates. The kernel conformance
probe separately accepts the pure-power certificate with `m = 4`, and rejects
zero bases, invalid intervals, oversized products, and a sieve bound above 64.
Repeated prime powers remain one factor entry with a bounded exponent, not
repeated primality proofs.

The remaining gap has two concrete sources. The Boolean interface checks
canonical ordering, bounds attacker-supplied products, and recursively checks
the data it receives. A specialized proof has no corresponding first-class
certificate preflight or traversal, though its premises still need checking.
Removing those Hex checks would change its malformed-input contract. Replacing
the public proof path with specialized proof assembly would be a different
interface and would need separate elaboration and maintenance evidence.
The default producer also chooses witnesses independently, returning the first
successful base for each factor. Demanding a common base would add search and
could exhaust where independent witnesses succeed; the supplied-base experiment
does not justify changing that bounded construction policy. It measures the
replay benefit available to a caller supplying a different valid certificate.

## Construction and elaboration

The [fresh-module phase record](bench-results/hex-primality-10292-phases.json)
uses the same Curve25519 `Nat.Prime` goal for complete tactics. It includes
imports-only and input-only controls, literal preparation, Hex syntax rendering,
search, supplied-proof elaboration, and complete `primality?`/`prime_cert?`.
Each timed build deletes its module's olean. Dependencies are prepared first;
wall time includes Lake startup, imports, parsing, macro expansion, elaboration,
proof construction, kernel checking, and artifact writing where applicable.
The direct kernel experiment isolates checking; subtracting these noisy wall
measurements is not a precise parser-only or elaborator-only clock.

| Fresh-module phase | Hex before (s) | Hex after (s) | PrimeCert (s) |
|---|---:|---:|---:|
| imports | 1.533 | 1.529 | 1.639 |
| input | 1.453 | 2.012 | 1.746 |
| literal | 1.608 | 1.751 | — |
| render | 1.583 | 1.680 | 3.501 |
| search | 2.477 | 2.537 | 3.411 |
| replay | 2.133 | 1.540 | 1.575 |
| complete | 2.431 | 2.388 | 3.547 |

The table reports the [one unchanged phase repeat](bench-results/hex-primality-10292-phases-repeat.json).
All 80 completed builds in each corrected run remain evidence. The initial run
has complete-tactic medians 3.171 / 3.469 / 4.252 s (Hex before / after /
PrimeCert); the repeat has 2.431 / 2.388 / 3.547 s. The repeat's median of
within-block complete-minus-import differences is 0.898 / 0.581 / 1.908 s.
Individual phase differences can be negative when host timing changes between
builds. The adjacent complete-tactic after/before ratios in the repeat are
1.004, 1.219, 0.963, and 0.795: this is not evidence of a precise tactic speedup
or a consistent material regression. The separate native check and preserved
compiled definitions provide the construction regression evidence.


Hex's render probe builds syntax from a supplied literal. PrimeCert's render
probe includes search, rendering, and printing its suggestion; its search probe
includes sieve enumeration and prints the attempt count. Consequently these
render rows are explicitly different scopes. Supplied-proof replay excludes
search in both systems. PrimeCert's complete tactic reparses its generated
source, elaborates it, and explicitly kernel-checks the proof before presenting
the suggestion; Hex reifies the certificate directly and builds its suggestion
separately. Neither the complete-tactic difference nor the kernel difference
alone is a measure of certificate-search speed.

An initial phase-run setup error resolved `Nat.Prime` relative to a `Hex`
namespace. Its [partial record and error](bench-results/hex-primality-10292-phases-setup-failure.json)
are retained; no failed declaration is performance evidence, and its completed
samples are not pooled with the corrected run.

The [native regression record](bench-results/hex-primality-10292-native.json)
uses lean-bench's existing fixed `runConstruction` and `runCurveChecker`
registrations, including their autotuning, five repeats per invocation, and
expected hashes. Four adjacent alternating old/new invocations retain all
20 measured samples per arm. Construction medians are **812.405 ms before and
766.422 ms after**; compiled checking is **1.075 ms before and 1.014 ms after**.
These observations show no construction regression; they are not claims of a
native algorithm improvement. Every construction returns the same 29-attempt
certificate. The compiled algorithms are retained by proved `@[csimp]` equalities.

## Versions and reproduction

The records identify the host `chungus2`, automatically selected logical CPUs,
load observations, toolchains, source text and hashes/diffs, and exact commits.
Hex's baseline is `cc2baf89ea86df39c9ca1aa909a34728ac5ad3d2`.
PrimeCert is the clean local merge `9527ee7bbb1dd6e84bcb65efc7daccced4cdd751`
of PR #171 at `69db9aa4631795683eda56468139f77fd513094d` and PR #172 at
`560c7931b2e96d4316dcc90b6e296165d2c358d3`. Its pinned Mathlib/toolchain is
Lean 4.33.0; Hex uses 4.34.0. The before/after Hex experiment isolates the
implementation change on one toolchain. The package comparison retains
PrimeCert's supported dependency graph instead of also changing its Mathlib.

The [identical-code calibration](bench-results/hex-primality-10292-calibration.json)
checks the same local fixed-window definition and Curve25519 power on both
kernels: medians are 0.660 ms on Hex's kernel and 0.829 ms on PrimeCert's.
The identical binary-accumulator control is 3.394 / 3.249 ms. These noisy,
workload-specific observations do not support a universal kernel-version
correction or explain the certificate gap by version alone. The two libraries'
positive-modulus window loops and dispatch cutoffs agree over this corpus;
Hex additionally guards modulus zero, preserving its own API contract.

Create an isolated Hex baseline checkout and build `HexPrimalityMathlib` and
`hexprimality_bench` in both checkouts. Build the PrimeCert checkout before
measuring. All runners refuse existing output paths and retain completed
samples, including errors, without load-based selection. Use a fresh output
path for each command; the one permitted unchanged repeat also gets a new path.

```sh
record=reports/bench-results/hex-primality-small-replay/hex-primitive-all-certificate-kernel.json
python3 scripts/bench/primality_replay_attribution.py "$record" --output /tmp/components.json
python3 scripts/bench/primality_replay_attribution.py "$record" \
  --compare-bases --output /tmp/base-pair.json
python3 scripts/bench/primality_replay_attribution.py "$record" \
  --prepare-matched --output /tmp/matched-sources.json
python3 scripts/bench/primality_primecert_sources.py "$record" /tmp/primecert-sources --interval
python3 scripts/bench/primality_replay_pair.py --baseline /path/to/baseline \
  --record "$record" --kind kernel --output /tmp/kernel-pair.json
python3 scripts/bench/primality_replay_pair.py --baseline /path/to/baseline \
  --record "$record" --kind native --output /tmp/native-pair.json
python3 scripts/bench/primality_replay_pair.py --baseline /path/to/baseline \
  --record "$record" --kind phases --primecert /path/to/PrimeCert \
  --primecert-source /tmp/primecert-sources/Curve25519.lean --output /tmp/phases.json
```

For the package replay comparison, pass each generated comparator source as
`--primecert-supplied CASE=PATH` to `primality_kernel_direct.py`, using the
construction corpus record and the supplied Hex Curve448 fixture, as in the
[complete reproduction recipe](hex-primality-windowed-replay.md#reproduction).
For the matched-base experiment, write each `rows[].source` from the matched
record to a file and pass those files as `--hex-supplied CASE=PATH` too.
`--powers` adds an identical fixed-window calibration on both pinned kernels.
The component script's embedded Lean source and complete stdout make its
individual checks reproducible without reconstructing the generator.

Validation covers the checker and Mathlib bridge, kernel probes, construction
conformance with exact suggestions, malformed certificates, native benchmark
hashes, and freshly emitted oracle fixtures. The checker and native benchmark
remain Mathlib-free; Mathlib appears only in the separate complete-tactic proof
experiment.
