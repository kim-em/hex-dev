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

Every benchmarked operation has a textbook complexity model declared
*at the registration site* in the per-library `Bench.lean`. The
benchmark harness ([§Harness](#harness-lean-bench)) fits the
observed scaling against that model and emits one of two verdicts:

- **consistent with declared complexity** — observed scaling matches
  the model within tolerance.
- **inconclusive** — observed scaling does not match. The
  implementation is either wrong, or the model was misdeclared.

The latter case is the **valuable** outcome of a benchmark run.
"Everything looks consistent and within a small constant factor of
the external comparator" is acceptable but unexciting; "the verdict
came back inconclusive and the slope is `+0.4` over `n`" is the run
that earned its keep.

When a verdict is `inconclusive`, or when the verdict is consistent
but the constant is wildly off an external reference — orders of
magnitude, not a small constant factor — the response is mandatory
and uniform:

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
  textbook complexity (e.g. `n`, `n * n`, `n * Nat.log2 (n + 1)`,
  `2 ^ n`). Optional `with prep := <prepFn>` clause hoists per-param
  setup out of the timing loop, useful when the hot path takes
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

Per-library SPECs declare the complexity for each operation in their
API surface. The textbook model is the contract; the benchmark
checks observation against it. **Do not declare a complexity model
that matches the buggy current code.** If the textbook model says
`O(n²)` but the current implementation is `O(n³)`, declare `O(n²)`,
let the verdict come back inconclusive, file the issue, roll back.

### Adaptive ladder

The harness picks the parameter ladder (doubling vs. linear) at
runtime by probing the declared complexity at small parameters.
Polynomial complexity gets a doubling ladder (`2, 4, 8, …`)
extending to the configured `paramCeiling`; exponential complexity
gets a narrow linear ladder bracketing the productive band before
the wallclock cap kicks in. The user just declares the model
correctly; the harness handles ladder shape.

### What we don't measure

`lean-bench` measures compiled-code execution. The following are
**out of scope** for this contract; their performance is a separate
concern:

- elaboration-time `decide` and `decide +kernel`,
- `#eval` and `#eval!`,
- kernel reduction (proof terms, `decide` after elaboration),
- proof-search tactics inside `Bench.lean`.

If a tactic's compile time matters, it's a Lean / tactic-author
issue and goes to a different tracker.

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
  tool is scripted (Sage, python-flint, GAP, PARI) or the per-call
  cost is large enough that process-spawn overhead is negligible.
  Use `setup_fixed_benchmark` with an `IO α` body that shells out,
  parses the output, and returns it. This covers both single
  canonical-input comparisons *and* "swept" process-call
  comparisons, by registering one `setup_fixed_benchmark` per
  parameter value (e.g. `Hex.LLL.fpLLL.dim10`,
  `Hex.LLL.fpLLL.dim20`, `Hex.LLL.fpLLL.dim30`) — the parametric
  `setup_benchmark` form itself takes `Nat → α`, not `Nat → IO α`,
  so the per-rung-fixed pattern is the canonical workaround. If a
  true `Nat → IO α` parametric form matters more than the
  per-rung-fixed encoding, file an issue against lean-bench rather
  than rolling a hex-local harness.

Where a SPEC asks for a comparison lean-bench cannot directly model,
file the gap as a feature request against lean-bench. Do not invent
a parallel hex-local benchmark harness; one harness is the rule.

Each SPEC-required external comparator must end in exactly one of
these states:

- **implemented now** — registration and execution path land in the
  current Phase-4 work;
- **scheduled-only** — registration lands now, but execution is
  deferred to scheduled/release benchmarking, with the required
  environment stated in the bench module docstring;
- **blocked** — a narrow repo-local issue is filed for the missing
  capability, and the library does not claim Phase-4 completion.

Do not stub comparator outputs. Do not silently omit a required
comparator. If the blocker is a missing lean-bench feature, file
both the upstream feature request and the repo-local blocking issue.

## Fixed-problem benchmarks

Some benchmarks are absolute-wall-clock measurements on canonical
hard inputs, not parameter sweeps:

- factoring `x^128 + 1` over `F_2`,
- LLL-reducing a Lagarias–Odlyzko knapsack basis at dim 30,
- verifying irreducibility of a committed Conway polynomial like
  `(2, 409)`,
- computing a `GF(p^n)` inverse for fixed `(p, n)` and chosen element.

Use `setup_fixed_benchmark` for these. The bench module's docstring
records the canonical input, the source it came from, and the
reference timing the project considers reasonable (typically: time
on the same canonical input in a comparator like FLINT or fpLLL).
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

Every fixed benchmark sets `expectedHash` in its `where` clause to
catch silent value regressions — the cross-repeat hash-agreement
check alone is vacuous on small-cardinality result types like
`Bool`. Workflow: register, run once, copy the printed `observed
hash:` value into the `where` clause, commit. A sub-microsecond `‼`
advisory in the harness output means the body is still being folded
(typically `pure (closedExpression)`); add an `IO.Ref` read.

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

## CI integration

Every library at `done_through ≥ 4` ships a CI job that runs:

```sh
lake exe hexfoo_bench list
lake exe hexfoo_bench verify
```

The `verify` subcommand is the smoke gate: it spawns each
registered benchmark at a tight inner-tuning budget, checks the
child exits cleanly, and verifies hashable benchmarks emit hashes.
It does NOT assert timing values — the gate detects bitrot of the
bench module itself, not regressions in the implementation.

Per-library `verify` budget is up to ~15 s for libraries whose
smallest registered input genuinely needs that long; most libraries
should run in a few seconds. The repo-wide CI step's total budget is
the sum, with a soft target of a few minutes — not a hard cap. A
library exceeding 15 s on `verify` needs either tighter
smoke settings or a closer look at why its tiniest invocation is
slow. It is not a license to weaken the scientific settings.

Full timing runs (`lake exe hexfoo_bench run NAME` with a real
budget) are not part of merge-gating CI. They run on a scheduled
workflow or release-candidate workflow, on dedicated hardware where
timing comparisons are meaningful. Each release names the libraries
whose timing runs must succeed; a release is blocked by an
inconclusive verdict or a comparator divergence even when proofs
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

## Anti-patterns

These behaviours have surfaced in past benchmarking work and are
explicitly forbidden:

- **Lowering the parameter range to make a budget-skip go away
  without naming the implementation bug.** If a benchmark would
  exceed its wallclock cap at the declared range, the implementation
  is too slow at that range — file an issue, roll back, fix. Don't
  shrink the scientific settings to dodge the verdict.
- **Declaring a complexity model that matches the buggy current
  code instead of textbook.** The model is the contract. Observation
  disagreeing with textbook is a finding; observation agreeing with
  a buggy implementation that itself disagrees with textbook is a
  cover-up.
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
- **Treating an "inconclusive" verdict as a passing scientific run.**
  Phase-4 exit criteria require either "consistent with declared
  complexity" or a tracked finding-issue explaining the mismatch
  ([PLAN/Phase4.md](../PLAN/Phase4.md) §Exit criteria). An
  inconclusive verdict whose root cause is a too-narrow schedule
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

Every `setup_benchmark` registration must carry an adjacent comment
deriving its `n => …` from the algorithm: which step dominates, and
how the prep fixture's parameter maps onto that step's input size.
Changes to a declaration require a commit message re-deriving the
model independently of harness output.
