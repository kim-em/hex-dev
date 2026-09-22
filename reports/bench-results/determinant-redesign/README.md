# Determinant redesign experiment archive

- `arithmetic`: initial implicit-exponent generator; one completed replay
  sample followed by a 60-second timeout.
- `arithmetic-direct`: explicit conjunction traversal; same statement
  inference problem and timeout. The completed replay sample is retained.
- `arithmetic-threshold`: bounded heartbeat diagnostic identifies pending
  metavariable/typeclass synthesis as the failure before tactic execution.
- `arithmetic-typed`: explicit `Nat` exponent types; all eight arithmetic
  samples complete. The support source here is integer-specific.
- `full`: all eight complete-proof samples, including every candidate lemma.
  Its support is generalized to arbitrary commutative rings.
- `setup`: development failures, smaller diagnostics and successful axiom /
  proof-node audit. These logs are not performance samples.
- `arithmetic-sealed`: negative result for separately checked opaque arithmetic
  reuse; includes all auxiliary checks.
- `full-transport`: failed first transport proof, retaining its completed control.
- `full-synchronous`: original versus constructor transport, using complete
  synchronous declaration clocks without the profiler.
- `transport-controls`: explicit Mathlib and production Hex versus constructor
  transport, using the same synchronous clock.
- `value-int16`, `value-poly4`: compiled schedules with shared coefficient
  representations and independent exact validation.
- `value-rat8`, `value-dyadic8`, `value-dyadic8-wide`: direct arithmetic versus
  exact integer scaling, including scaling in the clock.
- `value-modular32`, `value-modular128`: existing CRT/divisor/Bareiss comparison
  and ordinary CRT stage attribution.
- `value-flat128`: recursive versus flat modular elimination; also FLINT
  modular elimination on the same matrix and recorded moduli.
- `value-verification`: 36 boundary/singular/pivot differential checks and the
  computational import closure. Validation, not performance evidence.
- `setup-followup`: compressed build logs and generated-C timing barrier
  inspection. These are not performance samples.
- `proof-deferred`: same Bird expression, independent versus shared final
  normalization, with an explicit Mathlib control.
- `proof-shared-controls`, `proof-shared-independent4`, `proof-shared-linear6`,
  `proof-shared-factored4`: direct paired complete-proof comparisons, including
  the common-factor median loss. All final target proofs are checked.
- `value-owned32`, `value-owned128`, `value-word128`: owned Lean buffers and
  raw-word scalar arithmetic; neither closes the modular gap.
- `value-c128`: C diagnostic versus FLINT on the same 41 modular images.
- `value-univariate4`: sparse/dense arithmetic and cold interpolation, with
  identical normalized coefficient output.
- `value-verification-extended`: 46 exact checks including the new Lean loops.
- `c-verification`: failed sanitizer-runtime loading, before numerical checks.
- `c-verification-runtime`: corrected runtime loading and 21 successful C
  differential checks with UBSan.

Each batch retains source snapshots, fixture, raw observations, result data,
host context and a terminal status with elapsed time. Failed attempts are not
discarded or counted as successes. No larger comparable input followed a timeout.

Proof-work clocks and external build clocks are separate. A final kernel
check below the 1 ms profiler threshold contributes an interval `[0,1)`;
it is not declared free. Full-proof samples sum all four candidate lemmas'
tactic and kernel costs, including the first check of each.

The synchronous batches instead clock complete theorem commands with async
elaboration and profiling disabled. Their totals include statement elaboration;
they cannot be compared numerically with the older proof-work clocks. Native
value clocks and external FLINT clocks have their own boundaries, described in
the report. No value result is claimed as a checked-proof speedup.

The report is [here](../../determinant-redesign-results.md); reproducible
working generators are under `experiments/Determinant/`. Exact measured
generator/support versions remain in these directories as `*.txt` snapshots.
