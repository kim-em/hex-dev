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

With the debug kernel bypass disabled while invoking handlers, the tactic
shares repeated expression nodes, checks the original goal type and
transitive axiom dependencies, and closes the entire candidate over its
local variables as a fresh auxiliary theorem. Lean's ordinary kernel checks
this theorem synchronously, using its configured heartbeat and recursion
limits and cancellation token. The final proof uses the checked theorem
instead of checking the large candidate again. The auxiliary theorem cache
is disabled so another proof of the same type cannot substitute for checking
this candidate. Let-bound locals are substituted while closing the proof,
without evaluating certificate checks in the elaborator. Elaboration keeps
its own heartbeat budget; the auxiliary theorem has a separate bounded
kernel counter and configured limit; synchronous checks accumulate kernel
work within the elaboration task. The counter is not reset for each auxiliary
theorem. Unsafe declarations are rejected, including those exposed by closing
over a local let value. The handler itself also runs with the debug kernel
bypass disabled. These guarantees assume an ordinarily checked environment
and normal declaration APIs. The synchronous check can wait for earlier
background declaration checks.

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

## Bounded implementation observation

The revised implementation at source `b46026b4caec0f26cba2c2a4ee18712816cef2fa` passed
all four new theorem axiom guards and the exact repeated-root false-verdict
guard. Its automatically pinned fresh complete-module build on `chungus2`,
CPU 26, took **288.998 seconds** wall time,
284.210 seconds user CPU and 3.682 seconds
system CPU. The largest child-process peak RSS was 5.276 GiB.
The four new theorems use `maxHeartbeats 1000000`. Elaboration and kernel
checking use separate counters; synchronous kernel checks accumulate within
the elaboration task rather than receiving a fresh counter for every theorem.

The [sample](data/rcf-cubic-examples/b46026b4c/20260929T122349Z/sample.json),
[complete build log](data/rcf-cubic-examples/b46026b4c/20260929T122349Z/build.log.gz),
source snapshots, dependency manifest, source patch, commit object and
[collector](data/rcf-cubic-examples/b46026b4c/20260929T122349Z/collect.py) are retained.
The scope includes the whole conformance module, its existing examples and
all guards, imports, elaboration, search, ordinary kernel checks and artifact
writing after dependencies were built. This observation predates the subsequent ambient-handler bypass and
closed-theorem guards; their additional checks are not timed here. It is
one observation, not an
individual theorem timing, simultaneous process-tree memory, a controlled
before/after comparison, a scaling result or a Phase-4 pass. Allocated bytes
are unavailable. The sample records host load before and after the run.

The resource description follows the pinned Lean sources:
[`lean_add_decl`](https://github.com/leanprover/lean4/blob/v4.35.0-rc3/src/kernel/environment.cpp),
[heartbeat counters](https://github.com/leanprover/lean4/blob/v4.35.0-rc3/src/runtime/interrupt.cpp) and
[task resets](https://github.com/leanprover/lean4/blob/v4.35.0-rc3/src/runtime/object.cpp).
[Profiler categories](https://github.com/leanprover/lean4/blob/v4.35.0-rc3/src/library/time_task.cpp)
subtract nested work when reporting their exclusive times.

The [validation and focused diagnostics](data/rcf-cubic-examples/b46026b4c/20260929T122349Z/diagnostics/)
retain the failed default-closure build, interrupted related manual build,
passing final builds and successful focused common-root probe. The probe's
complete temporary source and hash inventory are retained; the failed
intermediate tactic source was not retained. Profiling observations are
unpinned and their categories are exclusive: nested kernel checking appears
in the cumulative `type checking` category. The 44.5 ms `candidate check`
category measures closure/bookkeeping and excludes that nested kernel time. They are not a controlled performance
comparison. The full repository build also passed on the revised source.

Complete-tree [reconstruction patches](data/rcf-cubic-examples/b46026b4c/20260929T122349Z/source-archive.json)
for the measured source and its parent are bound to reachable main commit
`72db07c8cb3ce6a0c21cbc41a72e989a28cc70de`. Applying each patch to a temporary
index reproduces its recorded tree hash exactly; the raw source and parent
commit objects are retained as well. This preserves reconstruction after
branch removal.

To reproduce this observation, preserve its collector outside an isolated
checkout, restore the recorded source commit (or reconstruct it from those
patches and commit objects), validate and warm
`HexRCF.RealCoefficientTactic`, then run the collector from that clean
checkout. As for the earlier observation below, it removes only the selected
module's `.olean` and retains the complete result without filtering samples.

## Earlier direct-check observation

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
