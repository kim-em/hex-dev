# Benchmarking

This document specifies the performance-measurement contract for the
project. It complements [testing.md](testing.md): testing asks
whether the implementation is correct against an oracle, benchmarking
asks whether the implementation matches its declared algorithmic
complexity. Both are bug-finding tools and route to the same response
when they fire.

## Why benchmark

Benchmarking serves three purposes, in priority order:

1. **Detect wrong implementations** by checking declared algorithmic
   complexity against observed scaling. A Phase-1 commit ships a
   `def` with the *real* algorithm at the *intended* complexity (per
   [design-principles.md §7](design-principles.md)). A Phase-4
   benchmark whose verdict disagrees with the declared model means
   that promise was broken, and the `def` needs to be fixed.
2. **Measure how Lean compares to external systems** on hard
   problems. "Factoring `x^128 + 1` over `F_2` takes ~2 s in Lean
   versus ~0.8 s in FLINT" is a useful sentence even when both
   systems agree on the answer; benchmarking is how that sentence
   gets recorded.
3. **Make design tradeoffs evidence-based.** "Barrett or Montgomery?"
   "Linear or quadratic Hensel lifting?" are answered by running
   both and looking at the numbers, not by argument from textbook.

Detecting time-series regressions is a side effect of (1) and (2),
not the primary goal. A correctly-declared and correctly-implemented
operation should be regression-stable; if it isn't, the test is the
benchmark itself.

## The verdict-as-bug-trigger model

Every parametric benchmark has a complexity claim declared *at the
registration site* in the per-library `Bench.lean`. The benchmark harness
([§Harness](#harness-lean-bench)) fits the observed scaling against that model.
Its current two-sided mode emits one of two verdicts:

- **consistent with declared complexity** — observed scaling matches
  the model within tolerance.
- **inconclusive** — observed scaling does not match. The
  implementation is either wrong, or the model was misdeclared.

The latter case is the **valuable** outcome of a two-sided benchmark run.
"Everything looks consistent and within a small constant factor of
the external comparator" is acceptable but unexciting; "the verdict
came back inconclusive and the slope is `+0.4` over `n`" is the run
that earned its keep.

### Choosing the complexity claim

Choose the first mode in this ordered list that the operation admits. This is
not a menu. A report created or reconciled under this rule names the selected
mode for every performance-evidence registration and explains why each
stronger preceding mode does not apply. Existing passing two-sided
registrations are mode 1 by default and need not be relabelled until their
report is next revised.

This ordering applies to registrations used as Phase-4 performance evidence
for an operation. A fixed registration used only as an expected-hash anchor,
an external-comparator endpoint, or protocol-overhead control makes no
complexity claim and has no mode. The report labels that limited purpose
explicitly, and such an anchor cannot discharge performance coverage for an
advertised operation.

1. **Two-sided parametric — the default.** Use this whenever the intended
   algorithm's expected scaling on the registered input family can be derived
   before measurement. Both directions gate: slower than declared means the
   implementation is wrong, while faster than declared means the model or the
   family is wrong.
2. **One-sided upper-bound parametric.** Use this only when all three
   conditions hold:
   - no tight family-specific model can be derived, and the headline report
     says why;
   - the declared bound is published and cited, and the cited result covers
     the phase that the profile shows dominating — a citation for work absent
     from the profile is not evidence for the registration;
   - the input family exercises that phase, as required by
     [§The Attribution rule](#the-attribution-rule).

   Slower than the bound fails. Faster than the bound passes and is reported
   as **within declared upper bound (observed faster)**. This is visibly weaker
   than a two-sided pass and is never rendered as *consistent with declared
   complexity*. A matching observation is **within declared upper bound
   (observed matching)**, not a two-sided consistency claim. lean-bench does
   not yet have this registration mode; until
   [lean-bench #70](https://github.com/kim-em/lean-bench/issues/70) lands, the
   headline report records the harness verdict, the observed direction, and
   the reason it is a passing upper-bound result.
3. **Fixed registration with an absolute budget.** Use this only when no
   stable one-parameter wall-time model is reachable and a canonical hard
   input with a meaningful ceiling exists. The headline report states plainly
   that asymptotic regression detection has been given up for this operation.
   It also records the attempted parameterisations and schedules and explains
   why each failed to yield a stable independently derived model. When a
   comparator or external requirement supplies a meaningful ceiling, use it;
   a measured baseline plus stated margin is the fallback only when neither is
   available.
   The budget is an operation-specific regression ceiling justified from a
   comparator, a reference requirement, or a measured baseline plus stated
   margin. A generic harness timeout or inherited `maxSecondsPerCall` default
   is a safety cap, not an absolute budget. The scientific evidence recorded
   in the report must show the canonical input completing within the budget;
   the budget remains a Phase-4 gate even when the current harness only emits
   the measurement rather than a distinct fixed-budget verdict.
4. **Blocked.** If none of the preceding modes honestly applies, Phase 4 is
   not done. Failure to characterise an operation's cost is a reason to stay
   at the current phase, not a route to a fixed registration.

Two guards make the ordering binding:

- The operation's worst-case bound remains in its per-library SPEC regardless
  of the benchmark mode. Mode 2 or 3 changes the test, never the documented
  contract.
- Mode 1 is not licence to fit observed timings. Its declaration is the
  intended algorithm's independently derived expected scaling on the
  registered family, derived before measurement and never read off observed
  timings. The adjacent derivation explains how that family relates to the
  per-library SPEC's worst-case bound.

When a declared mode fails, or when a passing verdict has a constant wildly
off an external reference — orders of magnitude, not a small constant factor
— the response is mandatory and uniform. In particular, a faster-than-declared
two-sided result fails, while that same direction passes only for a registration
that independently qualified for mode 2 before measurement:

1. **File a GitHub issue.** Use the bench-found-bug template in
   [PLAN/Conventions.md](../PLAN/Conventions.md#bench-found-and-conformance-found-issues).
2. **Roll the library's `done_through` back** to the phase
   predating the broken `def`, per
   [PLAN/Conventions.md §Rollback is a normal action](../PLAN/Conventions.md#rollback-is-a-normal-action).
3. **Re-enter the rolled-back phase** to fix the implementation;
   the benchmark stays as written.

Worked examples (the bugs are real; the verdicts are predicted, not
observed — the prototype that found these bugs ran a hand-rolled
harness, not lean-bench):

- HexArith Montgomery: `MontCtx.mk` declared as `O(log p)` per call
  but effectively `O(p)` because `montgomeryRadixInvNat` did
  `(List.range p.toNat).find?` instead of using the existing
  Bezout-based `extGcd`. The broken cost lives in `mk`, not in
  `mulMont` itself; what the bench reports depends on whether `mk`
  is hoisted via `with prep := MontCtx.mk p` (bug surfaces as bench
  startup hitting the wallclock cap at large `p`) or stays inside
  the timed body (bug surfaces as an `inconclusive` verdict with
  residual log-log slope around `+1.0`). Either signature triggers
  the same response: file issue, roll HexArith back, replace the
  brute-force inverse with `extGcd`.
- HexLLL `swapStep` declared as `O(n²)` (incremental Gram–Schmidt
  update) but effectively `O(n³)` because the implementation
  rebuilt Gram–Schmidt from scratch on every swap. You don't bench
  `swapStep` directly — you bench `lll`, which performs `O(n)`
  swaps per call, so the broken `swapStep` shows up at the `lll`
  level as a residual slope around `+1.0` against whatever
  complexity the SPEC declares for full reduction. Response: file
  issue, roll HexLLL back, implement the incremental update.

These are not retrospectives; they are the canonical shape of a
benchmark finding.

## Scaffolding cross-link

[Design principles §7](design-principles.md) already forbids
data-level scaffolding: every committed `def` ships with the
intended-final implementation, not a wrong-but-plausible stand-in.
Benchmarking is the third enforcement point for that rule, after
Phase 1 (the author's own discipline) and Phase 2 (skeptical
review). A benchmark verdict revealing a scaffolding `def` triggers
the rollback above; the doctrine is symmetric with conformance
failures (see [testing.md](testing.md)).

## Harness: lean-bench

The benchmark harness is [`kim-em/lean-bench`](https://github.com/kim-em/lean-bench).
It is the only harness; do not roll a per-library replacement.

A library's Phase-4 deliverable is a `HexFoo.Bench` exe rooted at
`HexFoo/Bench.lean`. Supporting modules may live under
`HexFoo/Bench/`. The Lake target is named `hexfoo_bench`:

```lean
-- lakefile.lean
require «lean-bench» from git
  "https://github.com/kim-em/lean-bench.git" @ "main"

lean_exe hexfoo_bench where
  root := `HexFoo.Bench
```

Reproducibility comes from committing `lake-manifest.json` alongside
the lakefile, not from the `rev` field; `lake update` resolves
`rev = "main"` to a specific commit and records that commit in the
manifest. Pin to a tag instead once lean-bench publishes them.

```lean
-- HexFoo/Bench.lean
import LeanBench
import HexFoo

setup_benchmark Hex.Foo.op n => n * Nat.log2 (n + 1)
setup_fixed_benchmark Hex.Foo.canonicalHardProblem
  where { repeats := 10 }

def main (args : List String) : IO UInt32 :=
  LeanBench.Cli.dispatch args
```

Two registration forms:

- **`setup_benchmark <fn> <param> => <complexity>`** for parametric
  sweeps. `<fn> : Nat → α`. `<complexity> : Nat → Nat` is the
  declared model for the selected parametric mode (e.g. `n`, `n * n`,
  `n * Nat.log2 (n + 1)`, `2 ^ n`). Optional `with prep := <prepFn>`
  hoists per-param setup out of the timing loop, useful when the hot path takes
  `σ → α` and `σ` is expensive to construct (random matrices,
  pre-canonicalised polynomials).
- **`setup_fixed_benchmark <name>`** for absolute-time measurements
  on a single canonical input. `<name> : α` (pure) or `<name> : IO α`
  (effectful — required when the input must be read from disk or
  the call shells out to an external tool). No parameter, no
  complexity model; runs `--repeats N` measured calls (default 5)
  and reports median / min / max.

Both forms accept a `where { … }` clause to override fields of the
per-benchmark config (`maxSecondsPerCall`, `repeats`, `paramCeiling`,
slope tolerance, etc.); CLI flags layer on top.

The parametric runner hashes every result before stopping its inner-loop timer.
That hash is the conformance signal used by `compare`, not optional harness
overhead. A target returning a growing structure must therefore include the
structural hash walk in its adjacent cost derivation and ensure the walk has no
higher asymptotic order than the operation being measured. Do not replace a
structural result hash with a parameter-only digest merely to hide its cost;
that would discard the conformance signal.

Each benchmark therefore has two settings layers:

- **scientific settings** — the canonical parameter domain or fixed
  input used for Phase 4 and scheduled timing runs;
- **smoke settings** — the reduced `verify`-only budget used to
  prove the registration works.

Smoke settings may lower tuning budget and repeat count. They may
not redefine the benchmark family, replace a canonical fixed input
with an easier one, or shrink the scientific comparison domain.

The CLI surface is `lake exe hexfoo_bench <subcommand>`:

- `list` — print every registered benchmark, annotating fixed ones.
- `run NAME` — run a single benchmark, print the result table and
  verdict.
- `compare A B [C…]` — run multiple benchmarks (all parametric or
  all fixed), report `allAgreed` / `divergedAt` based on result
  hashes at common parameters, plus a relative-timing summary.
- `verify [NAMES…]` — smoke-test registration wiring: spawn each
  benchmark with a tight inner-tuning budget, check the child exits
  cleanly and emits a hash where one is expected. Used as a CI
  gate; see [§CI integration](#ci-integration).

Per-library SPECs declare the worst-case complexity contract for each
operation in their API surface. A benchmark registration makes the strongest
claim allowed by [§Choosing the complexity claim](#choosing-the-complexity-claim).
**Do not declare a complexity model that matches the buggy current code.** If
the intended algorithm has expected family scaling `O(n²)` but the current
implementation is `O(n³)`, declare `O(n²)`, let the verdict fail, file the
issue, and roll back.

### Adaptive ladder

The harness picks the parameter ladder (doubling vs. linear) at
runtime by probing the declared complexity at small parameters.
Polynomial complexity gets a doubling ladder (`2, 4, 8, …`)
extending to the configured `paramCeiling`; exponential complexity
gets a narrow linear ladder bracketing the productive band before
the wallclock cap kicks in. The user just declares the model
correctly; the harness handles ladder shape.

### Spawn-floor filter

Parametric reports record the harness's per-spawn floor and, by
default, exclude rows whose child-side timed batch is shorter than
`10 × spawn_floor`. This protects ordinary microbenchmarks from
mistaking process-startup noise for algorithmic signal.

Scientific registrations may set `signalFloorMultiplier := 1.0`
when all of the following hold:

- The benchmark target uses warm child-side inner repeats, so
  `total_nanos` measures work inside the child rather than parent-side
  spawn wall time.
- The registered rungs are fixed by the library SPEC or headline
  report and already clear the algorithmic signal needed for the
  declared complexity or comparator-ratio question.
- The scheduled host has a high executable startup floor that would
  otherwise make the fixed ladder unusable without changing the
  measured algorithm.

This setting disables only the spawn-floor filter. It does not raise
wallclock caps, weaken the declared complexity model, shrink the
scientific ladder, or hide the host condition: JSON exports still
record `spawn_floor_nanos` and `signal_floor_multiplier`.

### What we don't measure

`lean-bench` measures compiled-code execution. The following are
**out of scope** for LeanBench's compiled timing contract:

- elaboration-time `decide` and `decide +kernel`,
- `#eval` and `#eval!`,
- kernel reduction (proof terms, `decide` after elaboration),
- proof-search tactics inside `Bench.lean`.

These are out of scope for **LeanBench**. When a library advertises a tactic or
proof-producing API, Phase 4 covers that surface through the build-only
fresh-module evidence below; it must not disguise elaboration or kernel time as
compiled benchmark time.

CPU profiling of compiled benchmark binaries is **in scope** and is
a Phase-4 deliverable; see [profiling.md](profiling.md). A passing parametric
verdict only checks the selected asymptotic claim; profiling attributes the
constant factor and catches dominant costs that the registered targets do not
measure.

## Fresh-module proof evidence

Elaboration, tactic execution, emitted proof terms, and ordinary kernel
checking are measured only by an external runner building fresh Lean modules.
The module sources live recursively below a directory listed in the owning
`mathlib: true` library's `libraries.yml: proof_probes`. A path may reserve a
not-yet-created directory for a stacked change, but when present it must be a
directory below `bench/<Owner>/`, must resolve physically inside `bench/`, and
must contain no symlinks. Reservations are staging-only: before a library may
claim `done_through: 4`, each declared root must exist and contain at least one
Lean source.
Names such as `HexFooMathlib` and a library's `mathlib: true` flag grant no
implicit directory-wide exception.

For a mixed library, a proof-probe subtree may coexist with an ordinary
Mathlib-free `bench/<Owner>/Bench.lean` executable. The exception is exact and
component-aware: a declaration of `bench/HexFoo/ProofProbe` admits neither
`bench/HexFoo/Bench.lean` nor `bench/HexFoo/ProofProbeExtra`. Every undeclared
bench source whose transitive import closure reaches Mathlib is rejected.

Neither a proof probe nor any repository-local source in its transitive import
closure may import `LeanBench`, register a benchmark, define `main`, read an
in-process clock, or contain a timing loop. A probe also cannot root any
`lean_exe`. Their external runner must:

- before each sample, remove only the measured module's generated artefacts
  and run `lake build +<module>:olean`, keeping imported dependency artefacts
  warm; build each matched reference/candidate pair adjacently, rotate pair
  order, and alternate pair orientation over an even preregistered number of
  rounds;
- retain every raw wall-time sample and paired delta, and identify the exact
  source hashes, repository commit, dirty-state decision, toolchain, command,
  host/CPU/OS, load state, and timeout/cleanup policy;
- record emitted artefact sizes and the axiom set of the accepted theorem;
- refuse a release-quality verdict on a dirty tree, an uncontrolled or
  saturated host, a timed-out build, or a provenance mismatch.

The default release protocol uses a quiescent host and rejects concurrent
Lake/Lean processes. A named shared machine is also admissible through the
explicit designated-shared-host protocol: the command preregisters the expected
hostname and logical CPU, pins itself before warmup, and verifies its own
affinity after every arm; every timed descendant inherits that affinity, and
the timed Lean processes use one worker thread. The
manifest's `config.order` begins with at least two same-module null controls at
distinct cheap and expensive build magnitudes, followed by substantive pairs.
The preregistered sample count is even and at least six. Physical-core and SMT
topology are recorded once; host load, CPU-pressure state, affinity, and
concurrent Lake/Lean counts are retained around every measured arm. Cumulative
CPU-frequency residency is differenced across the arm to retain its
time-weighted mean frequency; idle snapshots before and after the build are
context only.
Scheduler counters on the pinned CPU and every SMT sibling are differenced
across each arm and combined with child user/system time and the harness's own
CPU time inside that counter window. The pinned CPU's separately reported
IRQ/softirq ticks are retained but excluded from the residual attributed to a
foreign process; otherwise ordinary interrupt handling is systematically
misclassified as another workload. The raw residual, interrupt time, and
signed non-interrupt residual are all retained; child CPU time materially above
the pinned CPU's non-interrupt busy time is an affinity/accounting failure.
The positive foreign residual on the pinned CPU plus busy time on every SMT
sibling forms one aggregate interference quantity. Exceeding the
preregistered ratio or three scheduler ticks rejects the complete pair
attempt.

A rejected pair attempt is retained with both arms, their fixed orientation,
and all counters. The runner then rebuilds both arms in the same order; it
never retry-warms one arm in isolation. The default is eight retries, while a
suite with preregistered long arms may explicitly request at most 32. The
requested value counts retries after the initial attempt. The chosen finite
bound is recorded and changes only how many clean-pair opportunities are
attempted, never the admission threshold. Before each
attempt, the runner waits up to five minutes for a two-second physical-core
observation with at most two non-interrupt busy ticks on the pinned CPU and two
busy ticks on each sibling. This preflight avoids spending the finite
build-retry budget inside a sustained burst; every rejected preflight window
and its counters are retained, and the unchanged per-arm admission gate
remains authoritative.
Only a wholly clean, adjacent pair attempt enters the timing sample. Exhausting
the build-retry bound or the preflight wait emits an explicit partial artifact,
records every rejected attempt or window, and never places a contaminated arm
in results, medians, or budget conclusions. The effective quantized ceiling,
retry count, and preflight wait are recorded rather than represented as the
nominal ratio. Missing frequency residency or a spread of admitted arm means
above the preregistered band also invalidates release quality. Global load and
unrelated Lake/Lean presence are context rather than automatic failures in this
mode.

A proof-track sweep may precede its substantive pairs with one or more marked
same-module null controls at representative build magnitudes. Each control uses
the exact same module and axiom policy in both roles, independently rebuilds it
under the ordinary alternating orientation, and requires an even preregistered
sample count so each role is built first equally often. Its raw signed deltas
describe fresh-build noise under that run's host conditions. The control
records its median, MAD, IQR, Tukey fences, range, maximum absolute signed
delta, and outlier count. Its conservative zero-centred envelope is the larger
of the Tukey-fence magnitude and the largest observed absolute signed delta,
so an isolated outlier can widen but never shrink the admission envelope.
A control whose IQR exceeds 10% of its build magnitude invalidates release
quality.

A suite may instead preregister `absolute_only` when every substantive pair
declares an absolute fresh-module wall-clock budget and no pair declares a
reference-subtracted tactic budget. In that mode the raw candidate maximum,
not a paired delta, is the release contract. Null controls remain in the
artifact to describe and classify paired noise, but their IQR and relative
build-magnitude coverage do not gate release quality because neither quantity
can change the absolute conclusion. Dirty-state, provenance, timeout,
frequency, per-arm CPU/SMT interference, and absolute-budget failures retain
their ordinary fail-closed behavior. The harness rejects `absolute_only`
manifests that omit an absolute budget from any substantive pair or add a
relative tactic budget.

The artifact interpolates control IQRs and conservative envelopes between
representative build magnitudes. Outside the measured range it may scale a
cheaper control upward by the build-time magnitude ratio, but never scales an
envelope down. A control farther away than the preregistered magnitude factor
is not comparable. Every substantive pair records `resolved`, `unresolved`, or
`no-comparable-control` from the resulting envelope. A cheap control does not
resolve noise for a much more expensive build.

When a suite names an import-only baseline, its same-round wall time is
subtracted from both arms before a workload ratio is formed. When the two arms
also construct materially different inputs, a matched construction-only pair
is subtracted round by round as well. If the attributed reference and
candidate workloads are `r` and `c` and the comparable envelope is `e`, a
threshold interval is `(r - e) / (c + e)` through
`(r + e) / (c - e)`. A threshold passes only when the arm delta is resolved
and the conservative lower bound exceeds the preregistered threshold.
Baseline-limited or noise-limited point estimates do not pass.

A fixed tactic budget is release-quality only when its median passes and
remains below the budget after the comparable null envelope is applied as a
conservative resolution check. The accepted worst-case core-interference
allowance across both arms must also be smaller than the budget. The reported
raw timing itself is never corrected. Artifact `release_quality` is derived
from pristine provenance, complete scheduler accounting, magnitude-comparable
controls, the scoped interference ceiling, and every required budget
conclusion. A diagnostic `--allow-busy` run remains non-release evidence and
is not this protocol.

Phase attribution uses matched module variants, not clocks embedded in the
probe. A tactic library may use a baseline; a reify-only module; an input module
containing the reflected sentence literal; a search module that runs compiled
certificate construction from that input through a meta checksum but emits no
proof; a literal module adding the pre-generated certificate; a replay module
adding the kernel-checked theorem; and a full tactic module. The matched
differences attribute reification, compiled search within the build, emitted
literal elaboration, kernel replay, and whole-tactic cost.

The search variant is phase-attribution evidence only: it gets no asymptotic
verdict. The same Mathlib-free operation is also timed by LeanBench on a
controlled ladder for its scientific complexity claim. The report links the
two by input and source hash and never substitutes the fresh-build delta for
the LeanBench verdict or adds both times together. Fixed tactic budgets apply
to the predeclared paired fresh-build cases and are not asymptotic evidence.

## Within-Lean comparisons

Where a SPEC names alternative algorithms or representations,
register them all and `compare` them in the same exe:

- `Hex.GF2.GF2Poly.mul` vs `Hex.PolyFp.mul` at `p = 2`
- `Hex.ModArith.mulModBarrett` vs `Hex.ModArith.mulModMontgomery`
  on overlapping modulus regimes
- `Hex.Hensel.linearLift` vs `Hex.Hensel.quadraticLift` on the same
  named inputs
- exponential-recombination versus LLL-assisted recombination
  inside Berlekamp–Zassenhaus

`compare` joins on result hashes (`Hashable α` registers the hash
in the JSONL output), so divergence shows up as a hash mismatch at
a common parameter. This makes a `compare` invocation
double-purpose: a timing report and a cross-implementation
conformance check, in one go. A divergence triggers the same
response as any other conformance failure: file an issue, roll back.

A `compare` group is valid only when the registrations cover the
same semantic task on an intentional common domain. If that common
domain is not obvious from the benchmark names, state it in the
bench module docstring. A trivial accidental overlap does not count.
If no meaningful common domain exists, leave that comparison
requirement open and file a narrow issue rather than faking one.

## External comparators

Where a SPEC marks an operation as architecturally important against
an external reference, register the comparator alongside the Lean
implementation in the same `Bench.lean` and let `compare` join them.
Two integration patterns:

- **FFI shim, preferred for hot-path comparisons.** The external
  tool is C/C++ with a stable ABI (FLINT, fpLLL, GMP, NTL). Wrap
  the relevant function with `@[extern]` returning a pure `α`,
  register it as a `setup_benchmark` target, and let the
  inner-repeat loop amortise the call cost. Per-call overhead is
  one C call. Add the shim sources under
  `HexFoo/ffi/<comparator>.c`; wire them into `lakefile.lean` via
  an `extern_lib hexfooffi (pkg)` block that builds the `.c`
  sources to `.o` (via `compileO`) and links them into a static
  library that the corresponding `lean_lib HexFoo` depends on.
  See `lakefile.lean`'s `extern_lib hexgf2ffi` for the canonical
  shape. Record any system link arguments (e.g. `-lgmp`) on the
  `lean_lib` block via `moreLinkArgs := #[…]`. **Do not put `.c`
  paths in `moreLinkArgs`** — that field is for link-time flags,
  not source compilation, and putting `.c` paths there silently
  produces no extern resolution. The same `@[extern]` boundary
  rules from [Conventions.md](../PLAN/Conventions.md) apply.
- **Process call, acceptable when FFI isn't viable.** The external
  tool is scripted (Sage, python-flint, GAP, PARI) or has a foreign
  runtime that doesn't interop cleanly with Lean's RTS. Use
  `setup_fixed_benchmark` with an `IO α` body that drives the
  comparator. This covers both single canonical-input comparisons
  *and* "swept" process-call comparisons, by registering one
  `setup_fixed_benchmark` per parameter value (e.g.
  `Hex.LLL.fpLLL.dim10`, `Hex.LLL.fpLLL.dim20`,
  `Hex.LLL.fpLLL.dim30`) — the parametric `setup_benchmark` form
  itself takes `Nat → α`, not `Nat → IO α`, so the per-rung-fixed
  pattern is the canonical workaround. If a true `Nat → IO α`
  parametric form matters more than the per-rung-fixed encoding,
  file an issue against lean-bench rather than rolling a hex-local
  harness.

  Process-call comparator wiring carries three contract clauses:

  - **Measure overhead.** Every process-call comparator records a
    per-call overhead measurement in
    `reports/<lib>-performance.md §"Comparator ratios"`. Methodology:
    time the comparator binary on a trivial input whose algorithmic
    work is sub-millisecond; report the median across enough runs to
    be stable. This figure is subtracted from per-call wall times
    before reporting ratios per
    [§Headline reports — Comparator ratios](#headline-reports).
  - **Persistent-subprocess is the preferred shape when overhead is
    non-negligible.** Wrap the comparator in a driver that loops on
    stdin (one problem per request, length- or delimiter-framed)
    and emits answers on stdout. For a fixed benchmark, the harness
    spawns one Lean child per outer warmup or repeat. Configure
    `warmupFirstIter` so that each child starts its driver before the
    timed region, then reuses the file descriptors across the
    auto-tuned inner-repeat batch. This amortises one driver startup
    across the measured calls in that child; driver state is not
    shared across outer repeats. Fixed registrations using the shared
    `Hex.BenchOracle.Flint` driver are checked by
    `scripts/ci/check_persistent_flint_warmup.py`. Document the protocol
    and lifetime in the bench module docstring.
  - **Per-call process spawn is acceptable only as a last resort.**
    FFI is preferred when feasible; persistent-subprocess is the
    fallback when FFI isn't viable. Per-call process spawn (the
    pattern where each `setup_fixed_benchmark` body shells out
    afresh) is acceptable only when both above are infeasible *and*
    the per-call algorithmic work is large enough that the measured
    per-call overhead falls below the adjustment threshold defined
    in [§Headline reports — Comparator ratios](#headline-reports).

Where a SPEC asks for a comparison lean-bench cannot directly model,
file the gap as a feature request against lean-bench. Do not invent
a parallel hex-local benchmark harness; one harness is the rule.

### Cross-system comparator sweeps

The one-harness rule governs **hex-internal** performance claims: any
number that gates a phase, or that appears in a headline report as a
statement about hex's own scaling, comes from lean-bench. It does *not*
forbid a re-runnable multi-system *comparator sweep* whose purpose is a
publication-quality cross-implementation picture, because such a sweep
makes no hex-internal claim — it measures several independent factorizers
under one protocol and plots them side by side.

A comparator sweep (the Berlekamp–Zassenhaus factorization comparison is
the motivating case) MUST obey:

- **Not CI.** No workflow under `.github/workflows/` runs it; the
  single-job rule is untouched. Sweeps run manually on dedicated hardware,
  and their durable records are committed under `reports/bench-results/`,
  named by git commit and host.
- **Uniform warm-process protocol.** Every measured system — hex (running
  as a warm process, one entry point per curve) and each external
  comparator (e.g. FLINT, NTL, PARI/GP, and verified Isabelle/AFP
  factorizers) — speaks one JSON line protocol: request `{"coeffs":[…]}`,
  reply `{"ok":…}`. Per-call protocol overhead is measured on a trivial
  input and recorded with each sweep, per the external-comparator overhead
  clause above.
- **Differential correctness.** A sweep cross-checks factor degree
  multisets against the corpus's expected factor degrees and pairwise
  across every system that answered; a mismatch fails the sweep, so the
  sweep doubles as a differential-correctness test of hex against the
  others.
- **Cactus-plot convention.** Per system, sort its solved instances by
  median runtime and plot cumulative time (log y) against instances solved
  (x); a curve ends at that system's solved count. Declines and timeouts
  are both "unsolved", not distinguished. One chart per polynomial family
  plus one balanced combined mixture (each family capped at an equal count
  so none dominates). Charts regenerate deterministically from the
  committed record, and every number in the sweep report traces to a
  SHA-256-pinned artifact per [§Artefact traceability](#artefact-traceability).

#### Core pinning when measurements can overlap

A comparator sweep and the factorization diagnostic drivers pin the measured
process to one core so the scheduler cannot perturb their timings. Pinning to a
*fixed* core is only correct while one measurement runs at a time. Several
concurrent measurements pinned to the same core each measure the others, and
the usual health signal does not show it: on a 96-core host, three measurement
processes sharing core 0 left the load average at 2 to 5 while inflating about
a quarter of a sweep's rows by roughly 1.9x, with the affected rows differing
run to run. `ps -eo pid,psr` reveals it at once; load average never does.

So: **pin to a verified-idle core, not to a fixed one.** `python3
scripts/bench/idle_core.py` prints a logical CPU that is idle on itself and on
every SMT sibling, sampled from `/proc/stat`.

- `scripts/bench/factor_phase_profile.py` and
  `scripts/profile/factor_sampling_profile.py` take `--cpu auto` and do this
  themselves by default; the chosen CPU is recorded in the run's `config`.
- `scripts/bench/factor_sweep.py` is deliberately *not* changed, because
  `scripts/bench/check_factor_sweep_freshness.py` treats it as a shared source
  path: editing it marks every system's committed record stale, including the
  external comparator records that cannot be cheaply re-measured. Invoke it
  through the helper instead:

  ```sh
  taskset -c "$(python3 scripts/bench/idle_core.py)" \
    python3 scripts/bench/factor_sweep.py --systems hex-factor
  ```

A release-quality verdict under the designated-shared-host protocol above still
preregisters and records an explicit CPU; this clause is about not colliding,
not about relaxing that.

### Comparator classification: `gating` vs `informational`

Every external comparator named by a per-library SPEC carries a
classification that determines whether it gates Phase-4 completion:

- **`gating`** — the comparator must be wired before Phase-4 can be
  claimed, the headline report records the measured ratio, and the
  per-library SPEC may state a performance goal against it (e.g.
  "at least as fast as X on shared canonical inputs"). A `gating`
  comparator is the right yardstick for the library — typically
  another implementation of the same algorithm at the same level of
  abstraction, where the constant-factor gap is meaningful.
- **`informational`** — the comparator's ratio is recorded in the
  headline report but does not gate Phase-4. Use this when the
  comparator is structurally different (e.g. a floating-point
  implementation versus an integer-only verified one) but still
  useful as orientation. An `informational` comparator may be
  scheduled-only.

A comparator declared `gating` must end Phase-4 in exactly one of
these states:

- **implemented now** — registration and execution path land in the
  current Phase-4 work;
- **blocked** — a narrow repo-local issue is filed for the missing
  capability, and the library does not claim Phase-4 completion.

A comparator declared `informational` may additionally be
**scheduled-only**: registration lands now, but execution is
deferred to scheduled/release benchmarking, with the required
environment stated in the bench module docstring.

Do not stub comparator outputs. Do not silently omit a required
comparator. If the blocker is a missing lean-bench feature, file
both the upstream feature request and the repo-local blocking issue.

### Comparator naming

Per-library SPECs name the external comparators they require for
Phase 4. Naming has two surfaces:

- **SPEC text** in `SPEC/Libraries/<lib>.md` describes each
  comparator with enough specificity for a clean-room re-
  implementation to identify the same tool: project name, source
  link, and any structural variant (e.g. "fpLLL via fpylll", "the
  Haskell extraction of the verified Isabelle LLL from AFP entry
  `LLL_Basis_Reduction`, Zenodo deposit 2636367"). Version pinning
  is a per-comparator implementation choice; the SPEC names the
  tool, not its commit hash.
- **Structured metadata** in [`libraries.yml`](../libraries.yml)
  carries the same comparator list under the per-library
  `phase4.comparators` key. Each entry has `tool`, `class`, and an
  optional `rationale` (for `informational`) or `goal` (for
  `gating`). Mechanical scripts read this; SPEC text carries the
  narrative.

A library SPEC must not name a comparator without classifying it.
Phase 4 is blocked until every `gating` comparator is wired and
its measured ratio recorded in the headline report ([§Headline
reports](#headline-reports)).

A comparator may be **scoped to a specific bench-target subset** — one
comparator gates one bench target while another bench target in the
same library declares absence — provided the per-library SPEC names
which bench target each comparator covers. This is the common shape
when an external tool exposes some of a library's surfaces as
user-callable functions but not others.

Where a bench target has no external comparator, or where the library
has no bench target at all, the per-library SPEC declares the absence
with a library-specific reason identifying exactly one of:

- **implementation-is-extern** — the surface is an external library
  via `@[extern]`; there is nothing algorithmically distinct to
  compare against.
- **structural-layer** — the surface is in a structural layer over a
  named dependency library whose declared comparator already covers
  it.
- **input-source-only** — the only published external implementation
  is itself the input source (e.g. a committed table), not an
  executable comparator.
- **mathlib-bridge** — the library is a `Hex*Mathlib` bridge whose
  comparison surface is a within-Lean `compare` group against
  Mathlib's native types.
- **no-comparable-surface-in-named-comparator** — the library
  declares a comparator for some surfaces but the named comparator
  tool does not expose this specific surface as a callable function
  (the tool builds it internally but doesn't surface it as user API).
- **correspondence-only-layer** — the library is a correspondence-only
  mathlib layer explicitly classified by `correspondence_only: true` in
  `libraries.yml` and therefore has zero bench targets (see
  [§Mathlib-free benches](#mathlib-free-benches)), so there is no
  surface of its own to compare. The declaration names the
  computational performance owner or owners whose bench targets carry
  the evidence for the operations it transports; more than one owner is
  normal, since a layer may transport operations from several
  Mathlib-free libraries.

Generic "not applicable" is not a valid declaration. Unwired-but-
required comparators are declared with the `blocked` state per
[§Comparator classification](#comparator-classification-gating-vs-informational)
and a tracking issue link, never silently omitted.

### The Attribution rule

Every asymptotically significant phase of an algorithm — whether
identified by the per-library SPEC, by profiling, or by both —
must be registered as its own `setup_benchmark` (or
`setup_fixed_benchmark`) **if it can be separated from the
surrounding code**. If profiling shows a dominant inclusive cost
that is not attributable to a registered target, Phase 4 cannot be
claimed (or must be rolled back) until either:

- the cost is attributed to a new target, with a derivation
  comment per [the cost-model derivation rule](#harness-lean-bench);
  or
- the per-library SPEC is amended with a written rationale for why
  the cost cannot be separated.

This is a hard rule, not discretionary. The motivation: an end-to-
end registration whose dominant cost is hidden inside a setup or
prep step that is itself sized non-trivially in the parameter does
not detect a wrong-asymptotic implementation in that step. The
attribution is what lets a future profiling finding be diagnosed
unambiguously.

## Fixed-problem benchmarks

Some benchmarks are absolute-wall-clock measurements on canonical
hard inputs, not parameter sweeps:

- factoring `x^128 + 1` over `F_2`,
- LLL-reducing a Lagarias–Odlyzko knapsack basis at dim 30,
- verifying irreducibility of a committed Conway polynomial like
  `(2, 409)`,
- computing a `GF(p^n)` inverse for fixed `(p, n)` and chosen element.

For Phase-4 performance evidence, use `setup_fixed_benchmark` only through
mode 3 of [§Choosing the complexity claim](#choosing-the-complexity-claim),
after modes 1 and 2 have been ruled out. Fixed hash, comparator, and protocol
anchors have the narrower non-performance role stated there and do not need a
mode-3 justification. The bench module's adjacent comment or docstring records
the canonical input, the source it came from, and the absolute budget,
including the reference timing the project considers reasonable (typically:
time on the same canonical input in a comparator like FLINT or fpLLL). The
headline report repeats that budget and records the scientific measurement
against it.
Comparison against the comparator is then a `compare` invocation
across two `setup_fixed_benchmark` registrations, one per
implementation.

`setup_fixed_benchmark` targets must be callable: `Unit → α`,
`Unit → IO α`, or (legacy) `IO α`. Bare-value `def f : α := …`
registrations are rejected at elaboration. Thread workload inputs
through an `IO.Ref` so the body is not a closed expression — Lean
will otherwise constant-fold the work into the binary, and the
harness will measure a constant load. Canonical shape:

```lean
initialize fooInputRef : IO.Ref Nat ← IO.mkRef 1_000_000

def benchFoo : Unit → IO UInt64 := fun () => do
  return doExpensiveWork (← fooInputRef.get)

setup_fixed_benchmark benchFoo where {
  expectedHash := some 0xdeadbeefdeadbeef
}
```

Sub-millisecond bodies are expected: the harness auto-tunes inner
repeats within one child process up to `minTotalSeconds` (default
`0.001`) before recording per-call time, mirroring the parametric
warm-mode contract. Per-call time is `total_nanos / inner_repeats`;
each fixed JSONL row carries an `inner_repeats` field. Do not
hand-roll inner loops to clear the noise floor.

Every fixed benchmark sets `expectedHash` in its `where` clause to
catch silent value regressions — the cross-repeat hash-agreement
check alone is vacuous on small-cardinality result types like
`Bool`. Workflow: register, run once, copy the printed `observed
hash:` value into the `where` clause, commit. A sub-microsecond `‼`
advisory in the harness output means the body is still being folded
(typically `pure (closedExpression)`); add an `IO.Ref` read. The
auto-tuner runs the body until `minTotalSeconds` is cleared, so a
sub-microsecond advisory after that is constant folding by
definition — fix with the `IO.Ref` read of a runtime input, not a
longer workload.

## Conway tier separation

Conway-polynomial benchmarks reflect the three-tier design and must
be reported separately:

- **Tier 1.** Verify irreducibility of committed Conway polynomials.
  One `setup_fixed_benchmark Hex.Conway.tier1.<p>_<n>` per
  committed entry being measured.
- **Tier 2.** Full Conway-table verification (irreducibility,
  primitivity, compatibility with divisor-degree entries) on
  committed entries. One `setup_fixed_benchmark Hex.Conway.tier2.<p>_<n>`
  per committed entry being measured.
- **Tier 3.** Search for missing Conway entries. Naturally
  parametric: `setup_benchmark Hex.Conway.tier3.gf2 n => ...`
  (sweep search-degree at fixed prime), or analogous registrations
  per prime family. Individual canonical search probes (e.g. the
  smallest unsolved degree at a given prime, like `(2, 410)`) may
  also be registered as `setup_fixed_benchmark
  Hex.Conway.tier3.gf2_410`.

The tier prefix is part of the registration name; reports and CI
gating MUST NOT aggregate tiers into a single "Conway runtime"
number. Named cases include existing entries near the top of the
Lübeck table (e.g. `(2, 409)`, `(3, 263)`, `(5, 251)`), entries for
medium and large primes (e.g. `(97, 127)`, `(521, 13)`,
`(65537, 7)`), just-beyond-table search probes (e.g. `(2, 410)`,
`(97, 128)`), and large-degree irreducibility stress tests over
`F_2` at degrees `512`, `1024`, `2048` and beyond when feasible.

## Mathlib-free benches

Benchmarks measure the computational kernel. The project's
architectural premise is the Mathlib-free split: `Hex*` libraries are
computational and Mathlib-free; `Hex*Mathlib` libraries are
proof-only bridges. Computational benchmark executables therefore obey two
hard invariants:

1. **`Hex*Mathlib` libraries do not have computational benchmarks.** No
   `Hex*Mathlib/Bench.lean`, no `Hex*Mathlib/Bench/`, no
   `lean_exe *mathlib*_bench` in `lakefile.lean`. The Mathlib bridge
   modules are proof-only; there is nothing computational to
   benchmark in a bridge.
2. **No bench reaches Mathlib.** For every bench executable declared
   as `lean_exe X_bench where root := ...` in `lakefile.lean`, the
   root module and every module transitively reachable from it via
   `import` must NOT name any `Mathlib.*` module. Pulling Mathlib
   into a bench's link chain forces thousands of native-object
   (`.c.o`) compilations per CI job (a measured 12-minute hit per
   offending bench at this repo's scale), and silently defeats the
   Mathlib-free split that the rest of the project rests on. The
   constraint is on the upstream Mathlib package only; intra-project
   `Hex*Mathlib.*` modules are not what this rule forbids — but per
   invariant (1) above, no bench imports them either.

There is one narrow, non-computational exception. A `mathlib: true` library may
declare recursive directory roots in `libraries.yml: proof_probes` for the
fresh-module evidence specified above. No suffix or library flag grants an
implicit exception, and files outside the exact declared roots remain ordinary
Mathlib-free bench sources. A probe is not a LeanBench registration and must
not import `LeanBench`, use `setup_benchmark` or `setup_fixed_benchmark`, define
`main`, perform an in-process timing loop, or serve as the root of any
`lean_exe`. This exception covers proof encodings and elaboration/replay costs;
it does not permit computational timing through Mathlib.

Both invariants are enforced by
`scripts/ci/check_benches_mathlib_free.py`, invoked from the `build`
job in `ci.yml`. The script:

- Parses `lakefile.lean` for each benchmark executable's literal `root` and
  effective `srcDir`, failing closed on missing roots or computed source
  directories.
- Walks each root's transitive `import` graph through repository and configured
  package source roots, recognizing module headers, `prelude`, import
  visibility/meta modifiers, and `import all`.
- Fails on the first reachable `Mathlib.*` import, printing the
  offending bench root and the full chain (e.g.
  `HexPolyMathlib.Bench → HexPolyMathlib.Euclid → Mathlib.Algebra.Polynomial.FieldDivision`).
- Globs `Hex*Mathlib/Bench.lean` and `Hex*Mathlib/Bench/` and fails
  if any such path exists.
- Reads exact proof-probe roots from `libraries.yml`, validates their ownership
  and physical containment, scans every probe for `LeanBench` imports,
  benchmark registrations, `main`, in-process clocks, or an executable root,
  and rejects every undeclared bench source whose transitive closure reaches
  Mathlib.

A computational bench that needs Mathlib is a category error, not an oversight
to work around: either it is measuring through Mathlib (slow and missing the
computational kernel) or it accidentally dragged Mathlib into a native link
chain. Either way, the fix is structural — file the finding, roll back if
necessary, and either remove the bench or move what it measures into a
Mathlib-free location. A genuine proof-elaboration question instead uses the
build-only probe exception above.

## CI integration

Every library at `done_through ≥ 4` with a compiled track extends the existing
CI job with:

```sh
lake exe hexfoo_bench list
lake exe hexfoo_bench verify
```

The `verify` subcommand is the smoke gate: it spawns each
registered benchmark at a tight inner-tuning budget, checks the
child exits cleanly, and verifies hashable benchmarks emit hashes.
It does NOT assert timing values — the gate detects bitrot of the
bench module itself, not regressions in the implementation.

A proof-only track instead builds its reduced declared probes in that same
single CI job and runs the structural lint. A mixed library does both. Proof
probes never add a second job, matrix, executable, or `list`/`verify` command.

The `Bench verify` step lives in `ci.yml`'s `build` ubuntu job (per
[SPEC/CI.md §Job-count budget](CI.md)), one sequential block, no
matrix. New compiled tracks at `done_through ≥ 4` append their bench target to
that block.

### Time budget

The `Bench verify` step has two enforced budgets:

- **Per-library soft warning at 30 s.** Any library whose `verify`
  crosses 30 wallclock seconds is logged as a warning in the CI
  output for visibility. This is a warning, not a fail —
  GitHub-hosted runner perf variance is real (2-3× single-run noise
  is normal), and a single-PR flake should not block merges.
- **Repo-wide hard cap configured in CI**. The total time for the
  `Bench verify` step (build + run, summed across all libraries)
  MUST be under the cap. Crossing it fails the build with a
  per-library breakdown so the offender is obvious. The cap may carry
  a small variance buffer for GitHub-hosted runner noise, but the
  long-term target remains **5 wallclock minutes** once slow fixed
  smoke rungs are remediated.

When a library trips either:

- If the smallest honest smoke input is fast at the bench's
  scientific complexity model but slow at its currently-registered
  smoke settings, tighten the smoke settings (or add a
  smoke-specific override clause to the registration) so the smoke
  path uses a budget appropriate for "does this module compile and
  run". Scientific settings are unchanged.
- If the smallest honest smoke input is genuinely minutes at any
  setting, that's a bench-found finding per
  [§verdict-as-bug-trigger](#the-verdict-as-bug-trigger-model):
  file the issue, roll back `done_through`, fix the underlying
  implementation at the rolled-back phase.

**Smoke settings may be tightened to fit budget; scientific
settings MUST NOT be weakened to dodge the budget.** That's
verdict-laundering per [§Anti-patterns](#anti-patterns). The
distinction matters because `verify` and `run` consume
different settings layers — see [§Harness](#harness-lean-bench).

The cap is enforced by
`scripts/ci/check_bench_verify_budget.sh`, invoked at the tail of
the `Bench verify` step. It wraps the per-library `lake exe X_bench
verify` invocations (capturing wallclock per invocation), prints a
sorted breakdown, logs the soft warnings, and exits non-zero if the
total exceeds the hard cap.

### Scientific timing runs

Full timing runs (`lake exe hexfoo_bench run NAME` with a real
budget) are not part of merge-gating CI. They run on a scheduled
workflow or release-candidate workflow, on dedicated hardware where
timing comparisons are meaningful. Each release names the libraries
whose timing runs must succeed; a release is blocked by a failing verdict in
the registration's declared mode or a comparator divergence even when proofs
are complete.

## Reproducibility contract

Every benchmark run is reproducible from committed inputs and
metadata:

- Each registered benchmark has a stable name (the
  `setup_benchmark` declaration name); renaming or removing a
  registration is a tracked PR-level change.
- Randomized inputs are generated from a seed derived from the
  benchmark name (so the seed is itself stable across runs).
- Generated inputs that matter for a comparison are committed under
  `HexFoo/Bench/Inputs/` or regenerated deterministically from the
  seed plus the parameter.
- The JSONL emitted by lean-bench is the canonical machine-readable
  artefact. Schema (fields per row, `kind` discriminator for
  fixed-mode rows, status enum) is defined by lean-bench; do not
  re-specify it here.
- Run metadata (git SHA, Lean toolchain, hostname, CPU model) is
  recorded by the harness or by the script that invokes it.
- Failures, timeouts, and budget skips are recorded explicitly via
  the `status` field rather than silently dropped.

Rendering JSONL into HTML, posting to GitHub Pages, or building a
benchmark dashboard are downstream concerns and not required for
the SPEC's contract to be met.

## Relationship to conformance

Conformance and benchmarking share one bug-finding loop:

- Conformance asks: do Lean and the oracle agree on outputs?
- Benchmarking asks: does the implementation match its declared
  complexity?

Both failure modes route to the same response — file an issue, roll
back `done_through`, fix at the rolled-back phase — and the same
canonical issue body shape (with the **Symptom** section described
in [Conventions.md](../PLAN/Conventions.md#bench-found-and-conformance-found-issues)).
Where a SPEC names the same canonical input for both views (a
committed hard polynomial, a committed lattice basis), the same
`setup_benchmark`-style registration carries both signals: timing
in the JSONL output, agreement via the result hash and `compare`.

## Headline reports

Every library at `done_through ≥ 4` must have a headline performance
report at `reports/<lib>-performance.md`. The report is the
single, scannable place a reviewer can land on to see whether
Phase-4 coverage is real and what is known about the library's
performance shape.

A `libraries.yml` entry explicitly declaring `correspondence_only: true` is
the one exception: it has zero bench targets and no proof-track probes of its
own, so it has nothing to report, and no headline report is required of it.
Its performance evidence lives in the computational owners named by its
`correspondence-only-layer` declaration ([§Comparator
naming](#comparator-naming)). A report already committed for such a
library is a historical artefact and need not be deleted.

The report contains five subsections:

1. **Bench targets.** The registered compiled targets and their declared
   complexities, copied (not paraphrased) from the `setup_benchmark`
   registration sites. A mixed/proof library also lists every fresh-module
   probe, its matched baseline, and the generic requirements that probe
   replaces.
2. **Verdicts.** Each performance-evidence registration's selected mode, the
   reasons the preceding stronger modes do not apply, and its result at
   scientific settings. Fixed hash/comparator anchors instead name their
   limited non-performance purpose. For a parametric performance registration
   this includes the harness verdict ("consistent with
   declared complexity", "inconclusive", with the verdict text); until the
   one-sided harness mode lands, a mode-2 report also records the direction and
   the distinct manual result *within declared upper bound (observed faster)*
   or *within declared upper bound (observed matching)*.
   Each mode-3 fixed registration records its absolute budget, median per-call
   time, and observed-hash agreement. Fixed hash, comparator, and protocol
   anchors record their median per-call time and observed-hash agreement but
   do not acquire a performance budget. Proof-track entries report
   all raw rotated fresh-build samples and paired deltas, never a complexity
   verdict. When the sweep has null controls, their raw deltas, absolute and
   relative ranges, and medians precede the substantive proof deltas in
   `config.order` and remain descriptive only.
3. **Comparator ratios.** Each comparator named in the per-library
   SPEC ([§Comparator naming](#comparator-naming)) — `gating` and
   `informational` alike — with measured ratios across the full
   parameter ladder (parametric registrations) or every canonical
   input (fixed-benchmark families), and a narrative paragraph
   naming the trend across rungs. A single number anchored at the
   bottom is structurally flattering to whichever side has the
   better startup characteristics; what's needed is a curve across
   the eligible range. Five clauses, all binding on the report:

   - **Define eligible range.** A rung is *eligible* for the
     gating-goal verdict when both: (a) the comparator's per-call
     overhead is ≤ 50% of measured wall time on that rung — below
     this floor the rung is a process-startup measurement, not an
     algorithm one; and (b) per-call wall time is ≤ 10 s hard /
     ≤ 1 s soft — exceed the soft target only when needed to give
     the trend enough range to read cleanly, and never exceed the
     hard ceiling. The eligible range for a `gating` verdict is the
     intersection of these floor and ceiling constraints.

   - **Ratios across the full ladder, with adjusted values inside
     the eligible range.** The §"Comparator ratios" subsection
     records the measured ratio at every shared rung of the
     parametric schedule (or every canonical input for
     fixed-benchmark families). Per-call overhead is measured once
     per process-call comparator per
     [§External comparators — Process call](#external-comparators)
     and shown as one line per comparator. On any rung where overhead
     exceeds 5% of measured wall time, both the raw ratio and the
     overhead-adjusted ratio (comparator wall time minus overhead,
     then divide) are recorded. Rungs outside the eligible range
     are reported for completeness only.

   - **Enough rungs inside the eligible range to see a trend.** Two
     or three points are at best a single slope; the ratio's shape
     across the eligible range — flat, climbing, accelerating,
     decelerating — must be unambiguous from the data alone. A
     doubling-only parameter schedule typically does not provide
     enough eligible rungs; the ladder is densified with in-fill
     rungs between existing points, never extended past the
     wallclock ceiling. The headline report records the actual
     ladder (including in-fill) so a reader sees what was measured,
     not just the family's default.

   - **Trend narrative and adverse-trend Concerns.** The
     §"Comparator ratios" subsection includes a paragraph naming
     the trend, with reference to the rungs that establish it. The
     baseline shape is a ratio that converges to a small constant
     past the regime where startup or fixed costs dominate; a
     diverging trend (one side steadily losing ground as the
     parameter grows) is an audit-found Concern when it contradicts
     the comparator's declared algorithm-class expectation or a
     `gating` goal, even when the highest-rung verdict happens to
     pass. Expected divergence against an `informational` comparator
     with a documented different complexity class is recorded as a
     finding in the trend narrative, but is not by itself a Concern.

   - **Gating-goal verdict at the top eligible rung.** When the
     per-library SPEC states a performance goal against a `gating`
     comparator, the verdict is computed at the largest-parameter
     eligible rung of each input family. The bottom rung is
     reported for context; it is never the rung that meets or
     fails the goal.

   - **Comparator-runtime plot (≥ 2 comparators).** A library
     whose `phase4.comparators` block declares two or more
     comparators commits one plot per `phase4.input_families`
     entry at `reports/figures/<lib>-comparator-<family>.svg`,
     log-y wall-time per call across the family's eligible
     range. Each plot draws the Lean curve alongside one curve
     per comparator with at least two committed data points on
     that family; comparators below that threshold are listed
     in §Concerns instead. The generator at
     `scripts/plots/<lib>-comparator.py` takes a `--family`
     argument and reads the same JSONL the ratio numbers cite.
     Plots disagreeing with the §"Comparator ratios" values are
     an audit-found issue.
4. **Profile.** Per [profiling.md §Coverage requirement](profiling.md),
   one representative compiled case per `phase4.input_families`. Dominant
   inclusive costs are named and explained, with leaf cost
   categorised across {own code, GMP, allocation, Lean runtime}.
   Any inclusive cost the author cannot attribute to a registered
   bench target is filed as an audit-found issue per
   [Conventions.md §Bench-found, conformance-found, and audit-found
   issues](../PLAN/Conventions.md#bench-found-conformance-found-and-audit-found-issues)
   and linked from the next subsection. Proof-track surfaces cite their
   fresh-build artefacts and state that timed-region sampling does not apply.
5. **Concerns.** Audit-found issues filed against this library
   that have not yet resolved. The library cannot **remain** at
   `done_through: 4` while any Concern is unresolved (see
   [PLAN/Phase4.md §Exit criteria](../PLAN/Phase4.md#exit-criteria)
   for the rollback rule). Each Concern entry is a one-line
   summary linking the open HO issue.

### Artefact traceability

Every numeric claim in a headline report is traceable: the report cites the
exact bench/probe case name, command line, seed or parameter, JSONL row or raw
fresh-build sample path/hash, applicable profile artefact location, source
hash, host/toolchain/commit, and comparator source. A narrative without
traceable artefacts does not satisfy this requirement.

For the published integer polynomial factorization comparison, the current
snapshot additionally covers the complete committed corpus for Hex, FLINT,
NTL, PARI, Isabelle BZ, and Isabelle LLL. The sweep records the clean source
commit and corpus hash, performs factor-degree cross-checking, and retains
timeouts as explicit rows. Relevant source changes require fresh measurements
for the affected systems. All cactus and runtime-by-degree figures are then
regenerated from the newest current-corpus measurement of each system; CI
checks both freshness and byte-for-byte figure regeneration on every PR.

The `reports/<lib>-performance.md` file is overwrite-on-rerun:
when the report is regenerated against a newer build, the previous
content is replaced and `git log -- reports/<lib>-performance.md`
is the history channel. There is one current snapshot per library
in `reports/`.

### Reports vs SPEC

The headline report is observed state at a specific commit on
specific hardware; per-library SPEC text under `SPEC/Libraries/`
states the requirements the library must meet. They live in
different directories deliberately: `reports/` is mutable observed
state, `SPEC/` is normative and follows the immutability rules in
[Conventions.md](../PLAN/Conventions.md).

## Anti-patterns

These behaviours have surfaced in past benchmarking work and are
explicitly forbidden:

- **Importing `Mathlib.*` into a bench module.** See
  [§Mathlib-free benches](#mathlib-free-benches). Bench targets
  compile to native executables, and Mathlib's `.c.o` chain is not
  in the upstream cache — every transitively-Mathlib bench inflates
  the CI `Bench verify` step's wallclock by ~12 minutes per
  uncached link chain. This is a category error to remove (delete
  the bench, move what it measured into a Mathlib-free location),
  not an oversight to argue around. Enforced by
  `scripts/ci/check_benches_mathlib_free.sh`.
- **Weakening scientific settings to fit a CI time budget.** The
  `Bench verify` time budget is on the smoke path, which has its
  own settings layer (see [§Harness](#harness-lean-bench)).
  Tightening smoke settings to fit the cap is allowed; lowering the
  scientific `setup_benchmark` parameters or `targetInnerNanos` is
  verdict-laundering. If the smallest honest smoke input is
  genuinely minutes, the response is a bench-found rollback at the
  rolled-back phase, never a scientific-settings shrink.
- **Lowering the parameter range to make a budget-skip go away
  without naming the implementation bug.** If a benchmark would
  exceed its wallclock cap at the declared range, the implementation
  is too slow at that range — file an issue, roll back, fix. Don't
  shrink the scientific settings to dodge the verdict.
- **Declaring a complexity model that matches the buggy current code.** The
  mode-1 model is the independently derived expected family scaling, and the
  mode-2 model is a cited published bound. Observation disagreeing with the
  applicable claim is a finding; changing that claim to agree with a buggy
  implementation is a cover-up.
- **Top-level `def` of proof-carrying context structures evaluated
  at module init.** A module-level `def ctx : BarrettCtx p := …`
  whose initializer transitively calls a heavy computation
  deadlocks the bench exe at module load. Construct such contexts
  inside the benchmarked function or, preferably, hoist them out
  of the timed loop via `setup_benchmark`'s `with prep := …`
  clause (see [§Harness](#harness-lean-bench)) — `prep` runs once
  per child-process spawn and its result is `blackBox`'d before
  timing starts, which is exactly the lifetime an expensive
  context wants.
- **Benchmarking `decide`, `#eval`, or kernel reduction.** Out of
  scope per [§What we don't measure](#what-we-dont-measure).
- **Runtime-`n` dispatch wrappers around dimension-typed
  operations.** Lean accepts dependent types fine at runtime; pass
  the dimension and its bound as parameters and let the caller
  fill them in. A pattern-match-on-dimension ladder buried inside
  the bench module is over-engineering and ties dimension choices
  to Lean rather than to the bench parameter.
- **Committed expected-output tables that the harness never reads.**
  The hash-agreement check via `compare` is the conformance leg of
  the harness; do not duplicate it in committed expected-output
  fixtures.
- **Calling `verify` success a Phase-4 pass.** `verify` proves
  registration wiring, not scientific validity.
- **Marking a comparator requirement complete after documenting that
  the tool is missing.** Missing tool support is either
  `scheduled-only` or `blocked`; it is not completion.
- **Rolling a hex-local benchmark harness.** lean-bench is the
  harness; gaps in its API are filed against it, not papered over
  locally — including hand-rolled `repeatXChecksum` /
  `mixHash`-fold inner loops in user code. lean-bench auto-tunes
  inner repeats; user-side iteration scaffolding is removed in the
  next touch of any bench module that still has it.
- **Tautological `#guard f x = some y` where `y` is a hand-typed
  copy of `f x` in the same file.** Verifies the literal was copied
  correctly, nothing more. Compare against an upstream fixture or
  use a content-bearing check (e.g. `#guard rabinTest f _ = true`
  for irreducibility). For benchmarks specifically, the harness's
  `expectedHash` is the right place for value-correctness
  assertions.
- **Shipping a registration that produces no verdict-eligible rows.**
  A parametric `run` whose every rung is filtered out by the
  warmup-trim or signal-floor filter exits with code `2` and reports
  `only 0 verdict-eligible row(s) survived…`. That is the harness
  telling you the schedule, the per-call cap, or the target inner
  nanos was set too low for the host the benchmark is supposed to
  run on. CI treats exit 2 the same as a verdict mismatch: file an
  issue, roll back, fix. Don't shrink scientific settings to dodge
  the verdict.
- **Treating an "inconclusive" verdict as a passing two-sided scientific
  run.** Phase-4 exit criteria require a passing verdict in the registration's
  declared mode ([PLAN/Phase4.md](../PLAN/Phase4.md) §Exit criteria). A
  faster-than-declared harness result is a pass only for a registration that
  independently satisfies mode 2's citation-and-attribution conditions; the
  report records the distinct upper-bound result while lean-bench #70 is open.
  An inconclusive verdict whose root cause is a too-narrow schedule
  (rungs too close to the per-spawn floor, even when some survive
  the filter) is miscalibration, not a finding, and the registration
  must be re-tuned before the library advances through Phase 4.
- **Verdict-fitting: rewriting the algorithm, fixture, or declaration
  so an inconclusive verdict converges.** The declared complexity is
  the contract, derived from the algorithm a priori; the verdict only
  checks it. Rewriting the implementation under test, rescaling
  `degree := f(n)`, or raising `verdictWarmupFraction` until the
  harness reports "consistent" is not a fix — it is laundering the
  verdict. Inconclusive means raise the schedule or file a
  finding-issue against the implementation, never re-declare.
- **Best-case / short-circuit inputs as sole Phase-4 evidence.**
  Inputs the algorithm walks past in its happy path — even when
  they don't formally fail any precondition — cannot be the sole
  Phase-4 evidence. They may appear as supplemental smoke or fixed
  cases, alongside at least one input family that demonstrably
  exercises every claimed-significant phase of the algorithm.
  Required Phase-4 input families are specified in the per-library
  SPEC and cross-referenced as `phase4.input_families` in
  `libraries.yml`. Exemplar to avoid: an LLL end-to-end bench whose
  only input is the identity basis — the LLL outer loop visits every
  k but does no row update and no swap fires, so the registration
  measures the loop's traversal cost and nothing about size
  reduction or Lovász swaps.
- **Dominant profiled cost left unattributed.** A profile run
  (per [profiling.md](profiling.md)) that finds a dominant
  inclusive cost not attributable to a registered bench target
  triggers the [§Attribution rule](#the-attribution-rule):
  Phase-4 cannot be claimed (or must be rolled back) until the
  cost is attributed to its own target, or the per-library SPEC
  is amended explaining why it cannot be separated. Exemplar:
  an LLL `setup_benchmark` for `lll` whose dominant cost is
  inside an `LLLState.ofBasis` prep step that is itself
  sized in `n` — that step is its own asymptotically significant
  phase and needs its own registration.
- **Comparator process overhead reported as algorithmic difference.**
  Per-call subprocess on inputs small enough that startup dominates
  the comparator's wall time is a measurement-shape problem, not an
  algorithmic one. Recognisable in a headline report by a comparator
  ratio of multiple orders of magnitude at the smallest rungs that
  collapses to a small constant factor at larger rungs — the
  small-rung gap is process startup, not algorithm. Fix per
  [§External comparators — Process call](#external-comparators) and
  [§Headline reports — Comparator ratios](#headline-reports):
  persistent-subprocess (or FFI) protocol, or explicit per-call
  overhead subtraction. The raw ratio is never published without that
  adjustment when overhead is non-negligible.
- **Bottom-rung-only comparator evaluation.** Declaring a `gating`
  comparator goal met on the basis of the bottom-of-ladder ratio
  alone hides asymptotic shape: two same-algorithm implementations
  can show wildly different bottom-rung ratios driven by startup and
  constant-factor differences while diverging steadily at larger
  parameters; the bottom rung is the rung most flattering to
  whichever side has the better warm-up. The verdict is evaluated
  at the largest eligible rung across enough in-fill rungs to see
  the trend, per
  [§Headline reports — Comparator ratios](#headline-reports).

Every `setup_benchmark` registration must carry an adjacent comment
deriving its `n => …` from the algorithm: which step dominates, and
how the prep fixture's parameter maps onto that step's input size.
Changes to a declaration require a commit message re-deriving the
model independently of harness output.
