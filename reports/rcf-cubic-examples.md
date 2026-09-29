# Cubic coefficients, simultaneous signs and repeated roots

The checked examples in `conformance/HexRCF/RealCoefficientTactic.lean` and
`HexManual/Chapters/HexRCF.lean` use the existing `rcf` command. Write
`c = (2 : ℝ) ^ (1 / 3 : ℝ)`, Mathlib's nonnegative real cube root, and
`b = (c² + 1) / 2`, computed with the actual `QAdjoin` field operations.
The additional goals ask for:

- a root of `x² − c` with `1 < x < c`;
- a common root of `(x − c)²` and `x³ − 2`, with `1 < x < 3/2`;
- `1 < x < 3/2` at every root of `(x − b)²`;
- existence of that repeated root. A false universal bound is also required to produce the guarded false-verdict diagnostic.

The defining field has degree three. The repeated factors are in the user's
polynomials; the internal sign-query root domain remains squarefree. The
examples supply no witness and use no manual rewriting before `rcf`.

## Proof validation

The tactic checks the original goal type and transitive axiom dependencies,
shares repeated expression nodes, and closes the entire candidate over its
local variables as a fresh auxiliary theorem. Lean's ordinary kernel checks
this theorem synchronously, using its configured heartbeat and recursion
limits and cancellation token. The final proof uses the checked theorem
instead of checking the large candidate again. The auxiliary theorem cache
is disabled so another proof of the same type cannot substitute for checking
this candidate. Let-bound locals are substituted while closing the proof,
without evaluating certificate checks in the elaborator. Elaboration keeps
its own heartbeat budget; the auxiliary theorem has a separate bounded
kernel budget. Unsafe declarations are rejected. The synchronous check can wait for earlier background
declaration checks.

Handler regressions cover malformed terms, unresolved proofs, wrong goals,
target-metavariable assignments, exceptions, local aliases and forbidden
admitted dependencies, kernel depth exhaustion, attempts to bypass kernel
checking or defer it asynchronously, escaped locals and assigned
metavariables in hypothesis types. Each new theorem has a guarded axiom inventory
containing only `propext`, `Classical.choice` and `Quot.sound`.

The algebraic-coefficient proofs consume the proved fixed-field replay and
`HexRealRootsMathlib.Tarski.check_rootSum` bridge. They require no new
admission and do not assert the missing general Tau Ceti Thom order theorem.
The retained [diagnostics](data/rcf-cubic-examples/a99cd60c6/20260929T113911Z/diagnostics/) include the initial failed
one-million- and five-million-heartbeat builds and the focused proof-checking
investigation. They are operational diagnostics, not a controlled timing
comparison. The temporary instrumented tactic and adapter sources were not
retained, so the profiles cannot be reproduced from the archived snapshots.

The archived source `a99cd60c6` used a direct `Kernel.check` pre-check outside
heartbeat accounting and without a cancellation token. Its successful build
therefore does not show that every step respected the module's one-million
heartbeat limit. The delivered implementation uses bounded synchronous
auxiliary-theorem checking instead.

## Representative module observation

The retained observation describes the earlier direct-check implementation,
not the subsequent bounded auxiliary-theorem implementation or the additional
repeated-root existence/false-verdict tests. One automatically pinned fresh-module build at source `a99cd60c681e8fdefa043995179c6438df0fd388`
on `chungus2`, CPU 29, took **254.749 seconds** wall time,
249.316 seconds user CPU and 4.384 seconds system CPU.
The largest child-process peak RSS was 5.282 GiB. This measures the complete
module, including its existing examples and axiom guards, imports,
elaboration, certificate search, kernel checking and artifact writing, after
dependencies were built. It does not give an individual example's time or
simultaneous process-tree memory. Allocated bytes are unavailable.

The [sample](data/rcf-cubic-examples/a99cd60c6/20260929T113911Z/sample.json), [complete build log](data/rcf-cubic-examples/a99cd60c6/20260929T113911Z/build.log.gz),
source snapshots, dependency manifest, source patch and commit object are
retained. Host load before and after the run is recorded in the sample.
A manual build ran concurrently on the shared host. This single observation
is not a scaling result, a before/after comparison or a Phase-4 pass.

To reproduce, preserve the [collector](data/rcf-cubic-examples/a99cd60c6/20260929T113911Z/collect.py) outside an isolated
checkout, restore the recorded source commit (or decompress and apply `source.patch.gz` to the
recorded parent), and build `HexRCF.RealCoefficientTactic` once to validate
and warm its dependencies. Run the collector from that clean checkout. It
leases a CPU, removes only this module's `.olean`, runs `lake build`, and
retains the complete output and metadata for the resulting observation.

An independent exact-rational check brackets `c` between `5/4` and `13/10`,
since their cubes bracket two. Its positive square root lies between `11/10`
and `23/20`, and `b` lies between `41/32` and `269/200`. These bounds check
the examples' mathematical plausibility; their proofs are the checked Lean
terms, not numerical approximations.
