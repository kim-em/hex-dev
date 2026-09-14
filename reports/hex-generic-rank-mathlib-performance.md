# HexGenericRankMathlib performance

## Preregistered proof measurements

`scripts/bench/generic_rank_sweep.py` specifies fourteen fresh-module probes,
with six adjacent baseline/candidate pairs each, alternating AB/BA order.
Every probe has a 30 second full-proof-build ceiling and a 120 second cleanup
timeout. The import baseline matches each candidate's imports. All completed
samples are retained on the shared host; CPU placement is selected automatically.

The full/low 2×2 workloads at one variable, degree one and factor support one,
and the `[x]` and quadratic examples each have generic, hypothesis-discharge,
and visible-side-goal probes. The finite-field example has hypothesis and
side-goal probes; its positive-characteristic polynomial-ring output-1 probe
is a documented non-test until the shared Nat residue encoding (#10257) lands.
The field fallback checks balanced integer representatives modulo p with the
existing polynomial-list arithmetic, without reducing through ZMod64.

Lean's cumulative profiler records batch reification/conversion, compiled
certificate production, and synchronous declaration checks separately for the
header, pivot-block identity and all-column identity. Nested profiler categories
are disabled inside those three checks so their named categories include the
kernel's work. Boolean proof-term construction is outside those categories;
the external full-build time includes it and all other elaboration. No library
or probe reads an in-process clock. A trace records distinct expression nodes
across the provider's shared output proofs; the reflection batch additionally
charges its own reconstruction.

Comparator: **no-comparable-surface-in-named-comparator**. Mathlib's numeric
`eval_rank` does not provide these symbolic or conditional outputs.

The [diagnostic clock-instrumented sweep](data/hex-generic-rank-diagnostic-clock-probes.json.gz)
retains all 84 pairs collected before replacing direct clock reads with Lean's
profiler. Its build and axiom checks passed, but that instrumentation violated
the build-only probe policy. It is diagnostic evidence only; the accepted
measurements below use the profiler-based implementation.
