# Certified factor-isolation reuse

The candidate root-isolation arrays are tied to the existing deterministic run
by ordinary-kernel equality proofs. Reusing them in the canonical constructor
removes one candidate re-isolation from `AlgebraicRoot.exactFactor?`; complete
`Option AlgebraicNumber` equality preserves stored representatives and every
checked failure. The lazy eliminant isolation, fixed-presentation conversion
and per-root exactification remain separate costs. The forward local normal
form and comparison-strategy algorithms are outside this change.

Each family uses four fixed trial-major blocks with adjacent Before/After arms
in alternating AB/BA order, a leased CPU and retained host context. Every
completed arm, including failures, is retained. Inputs, expected hashes,
ordinary warmup and operational caps are unchanged. The measurements compare
frozen executables from `121fc1e027` (metadata-only differences from computational
base `864afe0e83`) and `7ceaf9d47d`. Metadata records exact binary hashes,
source snapshots, commands and all raw outputs; binaries remain under the
persistent paths in each metadata file. Observations are host-specific, with
no fitted complexity model, portable budget or all-library CI inference.

| Case | Before median ms | After median ms | Median adjacent Before/After ratio |
| --- | ---: | ---: | ---: |
| Hard real addition | 6626.008 | 4437.722 | 1.498 |
| Hard real subtraction | 6681.559 | 4446.329 | 1.496 |
| Candidate exactification | 92.658 | 46.723 | 1.984 |
| Enclosing-root exactification | 93.028 | 47.182 | 1.977 |
| End-to-end six-factor exactification | 1.536 | 1.012 | 1.517 |

The arithmetic capture retains 16 successful arms and the root-degree capture
48 successful arms with complete sorted polynomial/sign/multiplicity hashes.
The initial NumberField capture retains all 24 arms: 20 succeed and four old
`runExactLadder` children hit the unchanged 0.2-second whole-child cap during
amplification with the collector's 0.05-second floor. That is not a measured
single-operation timeout or a hash mismatch. The corrected ExactLadder-only
capture restores the registration's 0.001-second floor and retains eight
successful arms. No other inputs or caps change, no completed sample is
discarded and no unchanged rerun is performed. Candidate/selection comparisons
use the successful original arms; end-to-end ratios use only the corrected
paired capture. `analyze.py` reports every failed arm explicitly.

The root plot compares the actual real polynomial-root API at rational degrees
2/4/8 and quadratic-coefficient degrees 1/2/4. External FLINT and Z3 RCF lines
reuse the separately retained observations on `edb3ef9566` as historical
reference curves: they are not paired with these new native samples. Their
backend implementations and fixture problems are unchanged. The native API
produces canonical minimal polynomials; external fingerprints use fixture
Eisenstein proofs and retain exact annihilation/transport/cleanup costs.

Local verification on `7ceaf9d47d` passes the full Lake build (15818 targets),
NumberField companion and real-algebraic theorem/axiom guards, conformance
build and all 102 real-algebraic and 92 NumberField compiled result checks.
The initial operational verifications without installed oracle dependencies
are retained separately; `verify-with-oracles.json` records the corrected
environment and successful checks. This is not required CI or Phase-4
attestation for a later source.

The representative hard-add profile on documented source `08c8a9f13e`
retains 4344 kernel samples; calibration, expected counts and ±5 ms boundary
sensitivity pass. Isolation remains 90.56% inclusive. The old third isolation
pass is removed; two remain. Raw perf/samply/sidecar data and the exact
source/binary hashes persist at the manifest paths. This supplies required
attribution rather than a per-change profiling policy.
