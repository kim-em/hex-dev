# Benchmarking

This document specifies the performance-measurement contract for the
project. It complements [testing.md](testing.md): testing asks
whether the implementation is correct against an oracle, benchmarking
asks how useful operations behave on representative inputs and whether
their costs agree with the intended algorithms. Both are bug-finding tools;
a performance verdict starts an investigation rather than establishing a
correctness failure by itself.

## Why benchmark

Benchmarking serves three purposes, in priority order:

1. **Detect wrong implementations** by checking declared algorithmic
   complexity against observed scaling. A Phase-1 commit ships a
   `def` with the *real* algorithm at the *intended* complexity (per
   [design-principles.md §7](design-principles.md)). A Phase-4
   benchmark whose verdict disagrees with the declared model starts an
   investigation of the implementation, model and measured input range.
   A confirmed implementation defect must be fixed.
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

### What needs performance evidence

Performance coverage is a judgement call, not a per-operation quota.
A performance check belongs wherever it can find a bug or settle a
question: an operation users will call at scale, a kernel with a known
complexity, a hot path a downstream library depends on, or a choice
between algorithms. Where a timing would be pure ceremony (a thin
wrapper, a constant-size helper, an operation nobody calls in a loop),
it should not exist.

A fixed registration that only checks an output hash (`expectedHash`)
is a correctness and bitrot check. It is useful, and `verify` runs it
on every PR, but it is not performance evidence and makes no
performance claim.

### Shared-host measurement policy

Hex has no dedicated performance machine. Scientific runs therefore use the
available shared host and make claims from schedules that tolerate ordinary
scheduler noise:

- lean-bench complexity registrations use their fixed trial-major schedule and
  decide the declared model from the retained samples;
- before/after measurements keep the two arms adjacent and alternate `AB`/`BA`
  order over a fixed even number of blocks;
- host, CPU, affinity and load observations are retained as context, but host
  activity, SMT-sibling activity and process sightings never reject or remove a
  completed sample;
- an inconclusive run may be repeated once with the identical registered
  protocol. Both runs remain evidence. There is no quiet-core wait,
  contamination retry or retry-until-green campaign;
- profiles are collected when needed to explain an unexpected result or a
  surprising constant factor. A profile remains reusable while the measured
  code path and input are unchanged.

Pinning to an automatically selected CPU is useful placement: it prevents
concurrent Hex measurements from deliberately sharing one logical CPU. It is
not an isolation claim and the selected CPU need not pass an activity ceiling.
Absolute wall-clock results describe the recorded host. CI timeouts remain
operational safeguards rather than scientific budgets.

## The verdict-as-bug-trigger model

Every parametric benchmark has a timing model, an upper bound, or an explicitly
descriptive operation-count formula declared *at the
registration site* in the per-library `Bench.lean`. The benchmark harness
([§Harness](#harness-lean-bench)) fits the observed scaling against that model.
Its current two-sided mode emits one of two verdicts:

- **consistent with declared complexity**: observed scaling matches
  the model within tolerance.
- **inconclusive**: observed scaling does not match. Investigate the
  implementation, the model and the finite input range; the verdict alone
  does not distinguish defects from explained lower-order costs.

The latter case is the **valuable** outcome of a benchmark run.
"Everything looks consistent and within a small constant factor of
the external comparator" is acceptable but unexciting; "the verdict
came back inconclusive and the slope is `+0.4` over `n`" is the run
that earned its keep.

### Choosing the complexity claim

A parametric registration declares one of two claims, and its adjacent
comment says which:

- **An independently derived model.** The intended algorithm's expected
  scaling on the registered input family, derived before measurement and
  never read off observed timings. This is the default when such a model
  usefully predicts the measured work. Deviations in either direction prompt
  investigation. They can reflect an implementation defect, a mistaken model,
  or lower-order work dominating the measured range. An arithmetic-operation
  count is not automatically a wall-time model when it combines operations
  with substantially different costs.
- **A cited upper bound**, when no family-specific model is derivable. The
  bound is a published result that covers the work the family exercises.
  Slower than the bound is a finding; faster satisfies it. lean-bench has
  no one-sided verdict yet
  ([lean-bench #70](https://github.com/kim-em/lean-bench/issues/70)), so a
  result faster than the bound can read `inconclusive`; that result
  satisfies the bound, and whoever records it says so.

A valid cited upper bound covering actual timing costs remains a one-sided
check even when it is loose; it need not predict elapsed time accurately.
When neither a useful timing model nor such a bound is available, representative
observations are permitted. First fix identified implementation defects and
consider practical improvements justified by intended use. Consider correcting
the model for operand sizes or choosing inputs with bounded per-operation cost.
If those do not yield a useful independently derived claim, identify from the
source which costs vary and why; existing observations must support that
explanation with operand inventories or attribution. Keep the source operation
bound and record time and memory at at least two sizes covering the intended
downstream range. Growth exceeding what known operation and operand-size bounds
allow remains a finding. The observations establish no scaling law.
This route is unavailable when the intended model already has bounded
per-operation costs, such as fixed-precision word operations. Do not use it merely
because a fitted verdict is inconvenient, and do not infer a model from timings.
The same standard applies before and after measurement, to production as well
as references. Explicit performance targets and implementation defects remain
obligations; this route requires no exhaustive optimization campaign.

Representative measurements may use fixed-problem registrations. A parametric
registration retained for paired sampling may instead label its formula as an
operation count with a descriptive fitted verdict in its adjacent comment and
report. It makes no timing-scaling claim. Preserve historical formulas,
observations and verdicts when replacing an invalidated timing claim.

A fixed registration makes no performance claim; see
[§Fixed-problem benchmarks](#fixed-problem-benchmarks). The operation's
worst-case bound stays in its per-library SPEC whatever the registration
declares, and the adjacent comment explains how the registered family
relates to it.

Use measurements to assess useful operations on representative inputs and
detect unexpected costs. Do not require a parametric model for an auxiliary
reference computation merely because it can be timed. An auxiliary computation
is not performed by production at the sizes over which scaling is assessed
and has no separately mandated performance target. Required algorithm
comparisons remain required.
When no useful timing
model is available, fixed-problem measurements and required comparisons can
still document time and memory, with explicit limits on what they establish.
They do not prove scaling or replace a mandated performance target.
Required runtime comparisons do not require a useful timing model for every
arm. If the paired sampler retains a source operation-count formula for an
auxiliary reference arm with mixed costs, state that limitation at the
registration and in its
report. Its fitted verdict is descriptive; the comparison uses actual times,
matching results and any separately stated ratio target. If an independently
demonstrated mismatch between operation counts and timing costs invalidates a
production timing model, retain its old formula, observations and verdict as
historical evidence. Explain the mismatch from the actual algorithm and operand
sizes, and replace the unsupported timing claim with the appropriate bound or
representative observations. Do not drop a model merely because its fitted
verdict is inconvenient.

An inconclusive harness verdict is a finding to resolve, not an automatic
requirement for a larger collection. Retain its original verdict and samples.
A resolution may identify a defect and fix it, correct an independently
demonstrated model error, or explain the finite-range behavior using source
work counts and representative phase measurements or attribution. State the
evidence, the operation's relevance, and any remaining limitation in the
performance report. A small difference from a fitted-slope threshold alone
does not justify an expensive collection whose only purpose is to cross that
threshold. Unexplained excessive growth, unsuitable time or memory on intended
inputs, and unmet explicit comparison targets remain unresolved requirements.

A finite-range explanation must predict the deviation's direction and rough
size from the actual source work, supported by phase measurements or attribution
where their relative costs matter. Naming a possible overhead without evidence
is insufficient. Additional nonnegative lower-order work can reduce the observed
finite-range growth exponent below the leading-term prediction; it cannot
explain an exponent above that prediction. Excess growth requires a demonstrated
model error, such as previously unaccounted operand growth, or an implementation
fix. Models are corrected from
independent source or mathematical reasoning, never by fitting exponents or
constants to the observations.

When investigation establishes an implementation defect, including a violated
explicit performance target, follow the defect response below. Unexplained
findings block performance completion; an evidence-based model correction or
finite-range explanation does not by itself require implementation rollback.
An orders-of-magnitude discrepancy from an external reference also requires
investigation even when the scaling verdict passes.

1. **File a GitHub issue.** Use the bench-found-bug template in
   [PLAN/Conventions.md](../PLAN/Conventions.md#bench-found-and-conformance-found-issues).
2. **Roll the library's `done_through` back** to the phase
   predating the broken `def`, per
   [PLAN/Conventions.md §Rollback is a normal action](../PLAN/Conventions.md#rollback-is-a-normal-action).
3. **Re-enter the rolled-back phase** to fix the implementation;
   the benchmark stays as written.

Worked examples (the bugs are real; the verdicts are predicted, not
observed: the prototype that found these bugs ran a hand-rolled
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
  `swapStep` directly; you bench `lll`, which performs `O(n)`
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

A library's compiled benchmarks live in a `HexFoo.Bench` exe rooted at
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
  declared model (e.g. `n`, `n * n`, `n * Nat.log2 (n + 1)`, `2 ^ n`).
  Optional `with prep := <prepFn>` hoists per-param setup out of the
  timing loop, useful when the hot path takes `σ → α` and `σ` is
  expensive to construct (random matrices, pre-canonicalised
  polynomials).
- **`setup_fixed_benchmark <name>`** for absolute-time measurements
  on a single canonical input. `<name> : α` (pure) or `<name> : IO α`
  (effectful, required when the input must be read from disk or
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

Every `setup_benchmark` registration carries an adjacent comment deriving
its `n => …` from the algorithm: which step dominates, and how the prep
fixture's parameter maps onto that step's input size.
`scripts/check_phase4.py` checks that changed registrations have one.

Each benchmark therefore has two settings layers:

- **scientific settings**: the canonical parameter domain or fixed
  input used for real timing runs;
- **verify settings**: the reduced budget `verify` uses to prove the
  registration works.

Verify settings may lower tuning budget and repeat count. They may
not redefine the benchmark family, replace a canonical fixed input
with an easier one, or shrink the scientific comparison domain.

The CLI surface is `lake exe hexfoo_bench <subcommand>`:

- `list`: print every registered benchmark, annotating fixed ones.
- `run NAME`: run a single benchmark, print the result table and
  verdict.
- `compare A B [C…]`: run multiple benchmarks (all parametric or
  all fixed), report `allAgreed` / `divergedAt` based on result
  hashes at common parameters, plus a relative-timing summary.
- `verify [NAMES…]`: fast check of registration wiring: spawn each
  benchmark with a tight inner-tuning budget, check the child exits
  cleanly and emits a hash where one is expected. Run by CI on every
  PR; see [§CI integration](#ci-integration).

Per-library SPECs declare the worst-case complexity contract for each
operation in their API surface. **Do not declare a complexity model that
matches the buggy current code.** If the intended algorithm has expected
family scaling `O(n²)` but the current implementation is `O(n³)`, declare
`O(n²)`, let the verdict fail, file the issue, and roll back.

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
- The registered rungs are fixed by the library SPEC and already clear
  the algorithmic signal needed for the declared complexity or
  comparator-ratio question.
- The measuring host has a high executable startup floor that would
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
proof-producing API, Phase 4 covers that surface through the proof-probe
example files below; it must not disguise elaboration or kernel time as
compiled benchmark time.

CPU profiling of compiled benchmark binaries is a diagnostic tool, used to
explain an unexpected verdict or a surprising constant factor; see
[profiling.md](profiling.md). It is not a phase deliverable.

## Proof-probe example files

A library that advertises a tactic, elaborator, or proof generator keeps a few
example files that run it on representative inputs. Ordinary theorem
applications and instance-law proofs need correctness tests, not probes.

The files live recursively below a directory listed in the owning library's
`libraries.yml: proof_probes`. The directory is below `bench/<Owner>/`, resolves
physically inside `bench/`, and contains no symlinks; before a library claims
`done_through: 4` it exists and contains at least one Lean source. A
`mathlib: true` library's probes may import Mathlib. A probe subtree may
coexist with an ordinary Mathlib-free `bench/<Owner>/Bench.lean` executable;
a declaration of `bench/HexFoo/ProofProbe` admits neither
`bench/HexFoo/Bench.lean` nor `bench/HexFoo/ProofProbeExtra`.

A probe and every repository-local source it imports may not import
`LeanBench`, register a benchmark, define `main`, read an in-process clock, or
contain a timing loop, and a probe cannot root a `lean_exe`.

CI builds every probe root on every PR. That build is the whole Phase-4
requirement for the proof track. When a build-cost problem needs
investigating, `scripts/bench/fresh_module_sweep.py` times fresh builds of
matched probe modules; its output is diagnostic, not a phase deliverable.
[Proof examples and paired measurements](proof-examples.md) records which
declared roots have an independent SPEC decision justifying a larger suite.

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

Where an external system (FLINT, fpLLL, NTL, PARI, a verified Isabelle
extraction, …) is the natural yardstick for an operation, register it
alongside the Lean implementation in the same `Bench.lean` and let
`compare` join them. Whether a comparator is worth wiring is the same
judgement as any other performance check. A per-library SPEC that sets a
performance target against a comparator states it as a plain
**Performance target** sentence, naming the tool precisely enough to
identify it (project, source, and any structural variant).

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
  paths in `moreLinkArgs`**: that field is for link-time flags,
  not source compilation, and putting `.c` paths there silently
  produces no extern resolution. The same `@[extern]` boundary
  rules from [Conventions.md](../PLAN/Conventions.md) apply.
- **Process call, acceptable when FFI isn't viable.** The external
  tool is scripted (Sage, python-flint, GAP, PARI) or has a foreign
  runtime that doesn't interop cleanly with Lean's RTS. Use
  `setup_fixed_benchmark` with an `IO α` body that drives the
  comparator. Swept process-call comparisons register one
  `setup_fixed_benchmark` per parameter value (e.g.
  `Hex.LLL.fpLLL.dim10`, `Hex.LLL.fpLLL.dim20`,
  `Hex.LLL.fpLLL.dim30`), because the parametric `setup_benchmark`
  form takes `Nat → α`, not `Nat → IO α`. If a true `Nat → IO α`
  parametric form matters more than the per-rung-fixed encoding,
  file an issue against lean-bench rather than rolling a hex-local
  harness.

  Process startup is not algorithm. Prefer a **persistent subprocess**:
  wrap the comparator in a driver that loops on stdin (one problem per
  request, length- or delimiter-framed) and emits answers on stdout. For a
  fixed benchmark, the harness spawns one Lean child per outer warmup or
  repeat. Configure `warmupFirstIter` so that each child starts its driver
  before the timed region, then reuses the file descriptors across the
  auto-tuned inner-repeat batch. This amortises one driver startup across
  the measured calls in that child; driver state is not shared across
  outer repeats. Fixed registrations using the shared
  `Hex.BenchOracle.Flint` driver are checked by
  `scripts/ci/check_persistent_flint_warmup.py`. Document the protocol and
  lifetime in the bench module docstring. Spawning a fresh process per
  call is acceptable only when neither FFI nor a persistent driver is
  feasible and the per-call work dwarfs the measured startup cost; when
  quoting a ratio from such a comparator, measure its overhead on a
  trivial input and say whether the ratio is adjusted for it.

Where a SPEC asks for a comparison lean-bench cannot directly model,
file the gap as a feature request against lean-bench. Do not invent
a parallel hex-local benchmark harness; one harness is the rule.

### Cross-system comparator sweeps

The one-harness rule governs **hex-internal** performance claims: any
number about hex's own scaling comes from lean-bench. It does *not*
forbid a re-runnable multi-system *comparator sweep* whose purpose is a
publication-quality cross-implementation picture, because such a sweep
makes no hex-internal claim: it measures several independent factorizers
under one protocol and plots them side by side. The Berlekamp–Zassenhaus
factorization comparison is the motivating case. A comparator sweep:

- **is not CI.** No workflow under `.github/workflows/` runs it. Sweeps
  run manually on the shared host, and their records are committed under
  `reports/bench-results/`, keyed as described in
  [§Figure freshness](#figure-freshness);
- **uses one warm-process protocol** for every measured system: request
  `{"coeffs":[…]}`, reply `{"ok":…}`, with per-call protocol overhead
  measured on a trivial input and recorded with each sweep;
- **cross-checks results**: factor degree multisets are compared against
  the corpus's expected degrees and pairwise across every system that
  answered, and a mismatch fails the sweep;
- **plots cactus curves**: per system, sort solved instances by median
  runtime and plot cumulative time (log y) against instances solved;
  declines and timeouts are both "unsolved". One chart per polynomial
  family plus one balanced combined mixture. Charts regenerate
  deterministically from the committed record.

#### Core pinning when measurements can overlap

Comparator sweeps and the factorization diagnostic drivers pin the measured
process to one core. Pin to an **automatically selected** core, never a fixed
one: several concurrent measurements pinned to the same core measure each
other, and load average does not show it (on a 96-core host, three processes
sharing core 0 inflated about a quarter of a sweep's rows by roughly 1.9x
while the load average stayed at 2 to 5; `ps -eo pid,psr` reveals it at
once). `python3 scripts/bench/idle_core.py` selects a logical CPU with low
recent activity on itself and its SMT sibling; this is placement only, never
an acceptance check. `scripts/bench/factor_phase_profile.py` and
`scripts/profile/factor_sampling_profile.py` do this by default (`--cpu
auto`). `scripts/bench/factor_sweep.py` is a shared source path of the
factorization freshness check, so editing it marks every system's record
stale; invoke it through the helper instead:

```sh
taskset -c "$(python3 scripts/bench/idle_core.py)" \
  python3 scripts/bench/factor_sweep.py --systems hex-factor
```

The artifact records the selected CPU and observed activity as context.

## Fixed-problem benchmarks

Some benchmarks are absolute-wall-clock measurements on canonical
hard inputs, not parameter sweeps:

- factoring `x^128 + 1` over `F_2`,
- LLL-reducing a Lagarias–Odlyzko knapsack basis at dim 30,
- verifying irreducibility of a committed Conway polynomial like
  `(2, 409)`,
- computing a `GF(p^n)` inverse for fixed `(p, n)` and chosen element.

A fixed registration is a correctness and bitrot check: it pins the output
hash, and `verify` runs it on every PR. It makes no complexity claim. Its
recorded time is useful context and the natural endpoint for an external
comparator (`compare` across two `setup_fixed_benchmark` registrations, one
per implementation), but a fixed timing is not evidence that an operation
scales as intended. The bench module's adjacent comment or docstring records
the canonical input and the source it came from.

`setup_fixed_benchmark` targets must be callable: `Unit → α`,
`Unit → IO α`, or (legacy) `IO α`. Bare-value `def f : α := …`
registrations are rejected at elaboration. Thread workload inputs
through an `IO.Ref` so the body is not a closed expression; Lean
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
catch silent value regressions; the cross-repeat hash-agreement
check alone is vacuous on small-cardinality result types like
`Bool`. Workflow: register, run once, copy the printed `observed
hash:` value into the `where` clause, commit. A sub-microsecond `‼`
advisory in the harness output means the body is still being folded
(typically `pure (closedExpression)`); add an `IO.Ref` read. The
auto-tuner runs the body until `minTotalSeconds` is cleared, so a
sub-microsecond advisory after that is constant folding by
definition: fix it with the `IO.Ref` read of a runtime input, not a
longer workload.

## Mathlib-free benches

Benchmarks measure the computational kernel. The project's
architectural premise is the Mathlib-free split: `Hex*` libraries are
computational and Mathlib-free; `Hex*Mathlib` libraries are
proof-only Mathlib layers. Computational benchmark executables therefore obey
two hard invariants:

1. **`Hex*Mathlib` libraries do not have computational benchmarks.** No
   `Hex*Mathlib/Bench.lean`, no `Hex*Mathlib/Bench/`, no
   `lean_exe *mathlib*_bench` in `lakefile.lean`. The Mathlib layer
   modules are proof-only; there is nothing computational to
   benchmark in them.
2. **No bench reaches Mathlib.** For every bench executable declared
   as `lean_exe X_bench where root := ...` in `lakefile.lean`, the
   root module and every module transitively reachable from it via
   `import` must NOT name any `Mathlib.*` module. Pulling Mathlib
   into a bench's link chain forces thousands of native-object
   (`.c.o`) compilations per CI job (a measured 12-minute hit per
   offending bench at this repo's scale), and silently defeats the
   Mathlib-free split that the rest of the project rests on. The
   constraint is on the upstream Mathlib package only; intra-project
   `Hex*Mathlib.*` modules are not what this rule forbids, but per
   invariant (1) above, no bench imports them either.

There is one narrow, non-computational exception. Any library may declare
recursive directory roots in `libraries.yml: proof_probes` for the proof-probe
example files specified above. A declaration owned by a `mathlib: true` library may
import Mathlib; a declaration owned by a Mathlib-free library remains
Mathlib-free. No suffix or library flag grants an implicit directory-wide
exception, and files outside the exact declared roots remain ordinary
Mathlib-free bench sources. A probe is not a LeanBench registration and must
not import `LeanBench`, use `setup_benchmark` or `setup_fixed_benchmark`, define
`main`, perform an in-process timing loop, or serve as the root of any
`lean_exe`. This exception covers proof encodings and elaboration/replay costs;
it does not permit computational timing through Mathlib.

Both invariants and the probe restrictions are enforced by
`scripts/ci/check_benches_mathlib_free.py`, invoked from the `build` job in
`ci.yml`. It walks each bench root's transitive imports, prints the full
chain to the first reachable `Mathlib.*` module (e.g.
`HexPolyMathlib.Bench → HexPolyMathlib.Euclid → Mathlib.Algebra.Polynomial.FieldDivision`),
rejects `Hex*Mathlib/Bench.lean` and `Hex*Mathlib/Bench/`, and lints every
declared proof-probe root.

A computational bench that needs Mathlib is a category error, not an oversight
to work around: either it is measuring through Mathlib (slow and missing the
computational kernel) or it accidentally dragged Mathlib into a native link
chain. Either way, the fix is structural: file the finding, roll back if
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

The `verify` subcommand is a required fast check: it spawns each
registered benchmark at a tight inner-tuning budget, checks the
child exits cleanly, and verifies hashable benchmarks emit hashes.
It does NOT assert timing values; it detects bitrot of the bench
module and value regressions caught by `expectedHash`, not
performance regressions in the implementation.

A proof track instead builds its declared probes in that same single CI job
and runs the structural lint. Proof probes never add a second job, matrix,
executable, or `list`/`verify` command.

The `Bench verify` step lives in `ci.yml`'s `build` ubuntu job (per
[SPEC/CI.md §Job-count budget](CI.md)), one sequential block, no
matrix. New compiled tracks at `done_through ≥ 4` append their bench target to
that block.

### Time budget

The CI smoke wrapper enables `LEAN_ABORT_ON_PANIC=1` for
`hexnumberfield_bench` and `hexrealalgebraic_bench` in a per-executable
subshell. Their audited fixtures must not take a panic fallback: without
this guard, Lean can return a default value and let a result-hash check pass.
The guard applies to both direct-binary and `lake exe` verification.

The `Bench verify` step has two enforced budgets:

- **Per-library soft warning at 30 s.** Any library whose `verify`
  crosses 30 wallclock seconds is logged as a warning in the CI
  output for visibility. This is a warning, not a fail:
  GitHub-hosted runner perf variance is real (2-3× single-run noise
  is normal), and a single-PR flake should not block merges.
- **Repo-wide hard cap configured in CI**. The total time for the
  `Bench verify` step (build + run, summed across all libraries)
  MUST be under the cap. Crossing it fails the build with a
  per-library breakdown so the offender is obvious. The cap must sit
  above the step's time on the slowest runners CI is assigned, not
  between the fast and slow figures: the same step takes about 225 s
  on a fast GitHub-hosted runner and about 385 s on a slow one, every
  library slower by the same factor of roughly 1.8, so a cap between
  those fails about half of all runs for no change of code. The cap is
  therefore 600 s. The long-term target remains **5 wallclock minutes
  on a slow runner** once slow fixed rungs are remediated.

When a library trips either:

- If the smallest honest input is fast at the bench's scientific
  complexity model but slow at its currently-registered verify
  settings, tighten the verify settings (or add a verify-specific
  override clause to the registration) so `verify` uses a budget
  appropriate for "does this module compile and run". Scientific
  settings are unchanged.
- If the smallest honest input is genuinely minutes at any
  setting, investigate whether the implementation or the measurement plan is
  responsible. A confirmed implementation defect is a bench-found finding per
  [§verdict-as-bug-trigger](#the-verdict-as-bug-trigger-model):
  file the issue, roll back `done_through`, fix the underlying
  implementation at the rolled-back phase.

**Verify settings may be tightened to fit budget; scientific
settings MUST NOT be weakened to dodge the budget.** That's
verdict-laundering per [§Anti-patterns](#anti-patterns). The
distinction matters because `verify` and `run` consume
different settings layers; see [§Harness](#harness-lean-bench).

The cap is enforced by
`scripts/ci/check_bench_verify_budget.sh`, invoked at the tail of
the `Bench verify` step. CI passes explicit `Library=X_bench` ownership
pairs so pull-request filtering cannot depend on executable-name inference.
The script wraps the per-library `lake exe X_bench verify` invocations,
captures wallclock per invocation, prints a
sorted breakdown, logs the soft warnings, and exits non-zero if the
total exceeds the hard cap.

### Scientific timing runs

Full timing runs (`lake exe hexfoo_bench run NAME` with a real budget)
are run manually on the shared host under the policy above. They are
never part of merge CI, and no workflow schedules them.

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

Both failure modes route to the same response (file an issue, roll
back `done_through`, fix at the rolled-back phase) and the same
canonical issue body shape (with the **Symptom** section described
in [Conventions.md](../PLAN/Conventions.md#bench-found-and-conformance-found-issues)).
Where a SPEC names the same canonical input for both views (a
committed hard polynomial, a committed lattice basis), the same
`setup_benchmark`-style registration carries both signals: timing
in the JSONL output, agreement via the result hash and `compare`.

## Reports and figures

The evidence for a performance claim is the raw lean-bench JSONL of the
scientific run, linked from the PR that advances the library. A written
report under `reports/` is optional; when one exists it cites the JSONL
and commands it was produced from. Reports are observed state at a
specific commit on a specific host; normative requirements stay in the
per-library SPEC. Existing reports are history and need not be kept in
step with later rule changes.

### Figure freshness

A published figure is a claim about the current code, so the data it is
rendered from must keep describing the source that was measured. Each
enforced figure family declares a relevant set of source paths; its data
is keyed by a content fingerprint of that set and committed with a
manifest, and CI fails when no committed measurement covers the current
fingerprint, unless every differing path carries a blob-transition
exemption or passes a checked rule. The mechanism, its exemption format
and the checked rules are documented in the module docstring of
`scripts/bench/sweep_freshness.py`, with family-specific rules in
`scripts/bench/check_factor_sweep_freshness.py` and
`scripts/bench/check_graphiso_sweep_freshness.py`. Comparator figures
outside those families carry no freshness check; adopting one is a
per-family judgement.

## Anti-patterns

These behaviours have surfaced in past benchmarking work and are
explicitly forbidden:

- **Importing `Mathlib.*` into a bench module.** See
  [§Mathlib-free benches](#mathlib-free-benches). Bench targets
  compile to native executables, and Mathlib's `.c.o` chain is not
  in the upstream cache: every transitively-Mathlib bench inflates
  the CI `Bench verify` step's wallclock by ~12 minutes per
  uncached link chain. Enforced by
  `scripts/ci/check_benches_mathlib_free.py`.
- **Weakening scientific settings to fit a CI time budget.** The
  `Bench verify` time budget applies to the verify settings layer
  (see [§Harness](#harness-lean-bench)). Tightening verify settings
  to fit the cap is allowed; lowering the scientific
  `setup_benchmark` parameters or `targetInnerNanos`, or shrinking the
  declared range to make a budget skip go away, is verdict-laundering.
  A cap hit remains a recorded failed observation. Determine whether it
  exposes an implementation defect or an unsuitable measurement plan; it
  does not by itself establish a scientific time bound. Correct the defect
  or plan without omitting completed samples or weakening an explicit target.
  A cap hit on intended user inputs is an unsuitable-time finding. A plan
  correction cannot lower scientific parameters merely to hide such a result.
- **Declaring a complexity model that matches the buggy current code.**
  The declared model is the independently derived expected family
  scaling, or a cited published bound. Observation disagreeing with the
  claim is a finding; changing the claim to agree with a buggy
  implementation is a cover-up.
- **Verdict-fitting: rewriting the algorithm, fixture, or declaration
  so an inconclusive verdict converges.** The declared complexity is
  the contract, derived from the algorithm a priori; the verdict only
  checks it. Rewriting the implementation under test, rescaling
  `degree := f(n)`, or raising `verdictWarmupFraction` until the
  harness reports "consistent" is not a fix; it is laundering the
  verdict. Retire an inconclusive registration only for an auxiliary computation
  as defined above, retaining its archived samples, verdict and written
  disposition.
  Production registrations may be consolidated around the same measured operation
  only with all findings carried forward; retirement never clears a finding.
  Investigate inconclusive results and record their disposition;
  a larger schedule is warranted only when it answers a useful unresolved
  performance question. An inconclusive verdict
  whose root cause is a too-narrow schedule (rungs too close to the
  per-spawn floor) is miscalibration, not a finding, and the
  registration must be re-tuned. A demonstrated error in the
  declaration is different: record an independent mathematical or
  source-level counterexample, retain the old declaration and every
  sample, and derive the corrected cost model before collecting new
  measurements. A corrected declaration requires fresh validation; it
  does not turn an earlier inconclusive run into a pass. Selecting
  exponents or constants from observed slopes remains verdict-fitting.
- **Degenerate inputs as the only evidence.** Inputs the algorithm
  walks past in its happy path, even when they don't formally fail
  any precondition, cannot be the only input family behind a
  performance claim. Include at least one family that exercises the
  work the claim is about. Exemplar to avoid: an LLL end-to-end bench
  whose only input is the identity basis: the LLL outer loop visits
  every k but does no row update and no swap fires, so the
  registration measures the loop's traversal cost and nothing about
  size reduction or Lovász swaps.
- **Top-level `def` of proof-carrying context structures evaluated
  at module init.** A module-level `def ctx : BarrettCtx p := …`
  whose initializer transitively calls a heavy computation
  deadlocks the bench exe at module load. Construct such contexts
  inside the benchmarked function or, preferably, hoist them out
  of the timed loop via `setup_benchmark`'s `with prep := …`
  clause (see [§Harness](#harness-lean-bench)); `prep` runs once
  per child-process spawn and its result is `blackBox`'d before
  timing starts, which is exactly the lifetime an expensive
  context wants.
- **Benchmarking `decide`, `#eval`, or kernel reduction.** Out of
  scope per [§What we don't measure](#what-we-dont-measure).
- **Calling `verify` success, or a fixed registration's hash match,
  performance evidence.** Both prove wiring and correctness, not
  scaling.
- **Rolling a hex-local benchmark harness.** lean-bench is the
  harness; gaps in its API are filed against it, not papered over
  locally, including hand-rolled `repeatXChecksum` /
  `mixHash`-fold inner loops in user code. lean-bench auto-tunes
  inner repeats; user-side iteration scaffolding is removed in the
  next touch of any bench module that still has it.
- **Shipping a registration that produces no verdict-eligible rows.**
  A parametric `run` whose every rung is filtered out by the
  warmup-trim or signal-floor filter exits with code `2` and reports
  `only 0 verdict-eligible row(s) survived…`. That is the harness
  telling you the schedule, the per-call cap, or the target inner
  nanos was set too low for the host the benchmark is supposed to
  run on. Treat it like a verdict mismatch: re-tune or file an issue;
  don't shrink scientific settings to dodge the verdict.
- **Comparator process overhead reported as algorithmic difference.**
  A comparator ratio of orders of magnitude at the smallest rungs that
  collapses to a small constant factor at larger rungs is process
  startup, not algorithm. Use a persistent subprocess or FFI per
  [§External comparators](#external-comparators), and read ratios
  across the ladder rather than at the bottom rung.
