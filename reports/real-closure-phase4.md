# Real-closure Phase 4 evidence

## Compiled MetiTarski functional validation

The input is the degree-15 polynomial from section 4 of
[de Moura and Passmore, CADE 2013](https://www.cl.cam.ac.uk/~gp351/infinitesimals.pdf),
followed by `Y³ + x³ + 1` over its least real root `x`.
`bench/HexRealClosure/Phase4.lean` runs the actual native complete-root API
and the canonical real-algebraic backend on these same inputs.
It flushes every completed stage, checks root equations and multiplicities
after isolation, and reports construction of `x³ + 1` as a separate stage.
The independently verified interval `(-1875/2048, -1875/4096)` selects the
least root. The historical runs below precede these explicit stage and
selection checks.

[Retained outputs and metadata](bench-results/real-closure-phase4-functional/)
identify the exact source, executable hash, automatically leased CPU, host,
start and end times and operational timeout. Every completed or interrupted
arm is retained. These runs validate the workload; they are not a fixed
trial-major scientific comparison.

The native arm completed in 5.52 seconds on the shared host. Its first
isolation returned three roots and took 4.98 seconds; the second returned
one root and took 0.150 seconds. Both equation and multiplicity checks passed.
The canonical backend arm reached the 1800-second operational cap. Its stdout
was buffered and empty when the process was terminated, so the last completed
stage cannot be established from that output.
This timeout is a censored observation, not a completed timing sample or a
quantified speedup. No unchanged rerun of that arm has been collected.

## Preliminary native profile

[Retained profile metadata and reports](bench-results/real-closure-phase4-native-profile/)
cover one compiled native MetiTarski run, at 99 Hz `cycles:u` with
8192-byte DWARF call stacks. The exact compiled source is
`b2cea573a742a279dc07e8626f64b570c19d0c2e`; the binary SHA-256 is
`3edbc3503a26592c2dc36410d5a30e81d571306aa4a835d997c90154578a62af`.
The source is preserved by the upstream tag
`issue-10378-phase4-profile-source`. The measured repository's subsequent
changes contain only evidence files;
its driver and Lake configuration match the compiled source. Both stages
and the equation/multiplicity checks completed.

The profile retained 539 samples and reported zero lost samples. The largest
exclusive symbols were GMP half-gcd (`__gmpn_hgcd2`, 14.68%), `div2`
(9.90%), `malloc` (8.82%), and GMP gcd (`__gmpn_gcd_11_x86_64`, 5.81%).
The retained leaf categorization assigns 53.72% to GMP arithmetic (including
`div2`) and 30.50% to allocation; 8.63% lies below the report's displayed
threshold. These exclusive samples show substantial exact rational arithmetic and
allocation cost. Stack unwinding did not recover reliable inclusive Hex
callers. This whole-process profile includes untimed checks and uses 99 Hz;
it does not satisfy the filtered 1 kHz LeanBench/Samply profile contract in
`SPEC/profiling.md`. They do not separate the two isolation stages or supply exact
operation counts. Sampling percentages describe this one shared-host run.

The 4,833,596-byte raw profile is retained at the local path and SHA-256
recorded in metadata (`2ecc4899ef1b3b7c7f2d0cf98c23a19d739a3be2d673d64d4aa9e1ff751da14d`).
The historical gather profile with missing exact source provenance is not
used for this attribution.

## Exact workload provenance

The retained independent checks use python-flint 0.9.0 to establish that
the MetiTarski degree-15 polynomial is irreducible and squarefree. An exact
rational Sturm sequence finds three real roots and verifies the least-root
interval, with no root below it. Reproduce these checks with
`python3 scripts/oracle/real_closure_phase4_inputs.py` in an environment with
the pinned versions. Retain a new compiled functional run with
`python3 scripts/bench/real_closure_phase4.py native NEW_OUTPUT_DIRECTORY`
(or `canonical`); the runner refuses to overwrite evidence and records
CPU model, OS, kernel, source snapshot, binary hash and termination signal.
Z3 4.15.4 checks the printed first `tower8` polynomial under `0 < ε < 1`.
The paper prints a constant term `4 − 2ε² + 4`, giving

`P(x) = (x² − εx − 2)² + 4 − 2ε²`.

It has no real root for `0 < ε < 1`; the exact Z3 check is unsatisfiable.
The paper PDF SHA-256 and formula are in the retained checks. The original
CADE 2013 scripts have not been recovered from the pinned Z3 source trees.
No corrected polynomial or replacement workload is assumed here.

## Remaining measurements

The functional runs do not establish Phase 4 readiness. Required remaining
evidence includes the fixed trial-major schedule, clean versus eager
reduction, exact archived workloads, coefficient and evidence growth,
operation and query counters, DAG sharing, serialization and kernel replay,
and the required filtered inclusive Hex attribution. Neither this preliminary
profile nor historical gather profiles with missing source provenance satisfy
that requirement.
