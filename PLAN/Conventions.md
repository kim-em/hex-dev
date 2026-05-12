# Conventions

Cross-phase conventions that apply across the entire project. Read
once per session.

---

## Hard rules

### SPEC immutability

**Do not modify files under `SPEC/`.** The only exception is the
"scope of autonomous SPEC edits" rule in `SPEC/design-principles.md`:
agents may fix SPEC clauses that are internally contradictory or
mathematically impossible, with rationale in the PR description.

### Placeholders are for proofs only

`sorry` is permitted in proofs (`theorem` bodies, propositional
`structure` fields). It is **not** permitted as a data-level body,
and neither is any other placeholder shape: wrong-but-plausible
trivial returns, identity casts, `axiom` stand-ins, native-typed
functions that detour through `Nat`/`Int`, `@[extern]` shims that
trampoline back to a Lean fallback, alternative implementations
with the wrong complexity. Every committed `def` ships with its
intended-final implementation. See
[design-principles.md §7](../SPEC/design-principles.md), the rule
restated in [PLAN/Phase1.md](Phase1.md), and the bench-discovery
rollback path in [SPEC/benchmarking.md](../SPEC/benchmarking.md).

The word "scaffold" in this project refers to *adding a declaration
to the Lean source*, not to filling that declaration with a stub. A
scaffolded `def` is fully implemented; only its proofs may be
`sorry`. Phrases like "Phase 1 scaffold returns <trivial>",
"scaffold for the eventual <X> bridge", "honest placeholder", and
"for now ..." are forbidden in committed code.

### Read the SPEC, not just the issue body

When you pick up an issue, re-read every SPEC file linked in its
**Context** section in full before starting. Issue bodies paraphrase;
the SPEC is the source of truth.

Read adjacent SPEC and PLAN files when they look plausibly relevant —
sibling library SPECs, `SPEC/design-principles.md`, the Phase K
conventions for your phase. The extra tokens are cheap.

### PR workflow

Every PR gets auto-merge at creation:

```bash
gh pr create --title "…" --body "…"
gh pr merge "$(gh pr view --json number --jq .number)" --auto --squash
```

At the start of every planner cycle, merge all mergeable+green open
PRs before creating new work. Downstream agents are blocked on `main`
until merged PRs land.

`main` is branch-protected: auto-merge only fires once every required
status check (`build`, `build-macos`, `conformance`) is green. CI
gating is non-negotiable — see [SPEC/CI.md](../SPEC/CI.md).

### CI work expansion

When adding a new conformance check, oracle, benchmark, or build
target, **extend the script of the existing single ubuntu job** in
the relevant workflow (`conformance.yml` for conformance/oracle work,
`ci.yml` for build/check/benchmark work). Do **not** add a new
top-level job, a new `strategy.matrix`, or a new workflow file. The
full rationale and the trigger / concurrency / Mathlib-cache rules
every workflow must satisfy live in [SPEC/CI.md](../SPEC/CI.md); read
it before editing any file under `.github/workflows/`.

For benchmark targets specifically, the structural and timing rules
in [SPEC/benchmarking.md §Mathlib-free benches](../SPEC/benchmarking.md)
and the "Time budget" subsection of
[SPEC/benchmarking.md §CI integration](../SPEC/benchmarking.md)
constrain what a new bench is allowed to look like (no Mathlib in
the link chain; per-library smoke warn at 30 s; repo-wide hard cap).

---

## Lexical conventions

### Naming

| Context | Convention | Example |
|---------|-----------|---------|
| SPEC library files | kebab-case | `hex-poly-z-mathlib.md` |
| Lean modules/dirs | PascalCase | `HexPolyZMathlib` |
| `libraries.yml` keys | PascalCase | `HexPolyZMathlib:` |
| `lakefile.lean` names | PascalCase | `lean_lib HexPolyZMathlib where` |

The PascalCase form is a direct transliteration of the kebab-case
name: each hyphen-separated segment becomes capitalised and joined
(`hex-poly-z-mathlib` → `HexPolyZMathlib`).

**Acronym exception.** Segments that are recognised acronyms keep
all their letters upper-case rather than capitalising only the first.
The current acronym list is:

| kebab segment | PascalCase form |
|---------------|-----------------|
| `gf2`         | `GF2`           |
| `lll`         | `LLL`           |
| `gfq`         | `GFq`           |
| `fp`          | `Fp`            |
| `crt`         | `CRT`           |

So `hex-gf2` → `HexGF2`, `hex-lll` → `HexLLL`, `hex-lll-mathlib`
→ `HexLLLMathlib`, `hex-gfq-field` → `HexGFqField`. (`gfq` is
"Galois field GF(q)" where `q = p^n` — the `q` is a variable, so
lower-case; `fp` is "F_p" with `p` variable, lower-case.)

Extend this table when adding libraries whose names involve further
acronyms. Do not silently introduce a mixed-case spelling.

> **Current state note (2026-04-23).** The existing modules
> `HexGF2` / `HexGF2Mathlib` / `HexLLL` / `HexLLLMathlib` in the
> repository predate this rule and still use the un-exceptioned
> transliteration. A global rename PR will align them with this
> convention; until that lands, agents must not rename these
> identifiers in isolation. New libraries should follow the acronym
> rule from the start.

### FFI

Libraries that use `@[extern]` (e.g. `hex-arith` for GMP wrappers,
`hex-gf2` for CLMUL) keep their C shims in a `ffi/` subdirectory
within the library (e.g. `HexArith/ffi/wide_arith.c`). Compile those
sources in `lakefile.lean` via an `extern_lib` block; use
`moreLinkArgs` only for system linker flags such as `-lgmp`, never for
listing `.c` sources.

For ad hoc interpreter smoke tests of extern-backed declarations, use
`lake lean <file>` (or pass the module dynlibs explicitly via
`--load-dynlib`). Plain `lake env lean <file>` imports the workspace's
`.olean` files but does not auto-load per-module dynlibs, so `#eval`
of `@[extern]` declarations can fail with `Could not find native
implementation`.

### Library umbrella discipline

Each library `Foo` has a root file `Foo.lean` (the *umbrella*) and a
directory `Foo/` containing its modules. The umbrella **must import
every regular module** under `Foo/`. The only exempt files are those
declared as `lean_exe` roots in `lakefile.lean` (typically
`Foo/Bench.lean` and `Foo/EmitFixtures.lean`).

Why this matters: with `precompileModules := true` (the default), Lake
builds a per-library shared object `libHex_Foo.dylib`/`.so` from the
`.c.o.export` files of the modules the umbrella imports, and lists
that shared object as a plugin when elaborating any downstream library.
A module file under `Foo/` that the umbrella does **not** import is
absent from the shared object even though it is imported individually
by downstream code. On Linux, flat-namespace lazy binding hides the
gap by resolving the missing symbols against per-module dylibs that
happen to be loaded for the same elaboration run. On macOS, dyld's
stricter symbol resolution aborts with `dyld[..]: missing symbol
called` on the first downstream elaboration that needs the absent
symbols. This is exactly the failure mode that motivated adding macOS
to CI in [Phase0.md §6](Phase0.md).

`scripts/check_dag.py` enforces this rule mechanically: every
`Foo/X.lean` is either listed as a `lean_exe` root in `lakefile.lean`
or imported (directly or transitively) by `Foo.lean`. Any PR that adds
a new module under `Foo/` must also update `Foo.lean` (or chain the
import through an existing intermediate module).

---

## Issue creation

The project stays **GitHub-native** for orchestration. The canonical
task tracker is GitHub issues plus whatever structured fields GitHub
Projects or issue forms can provide. Do not introduce a separate
committed task-graph file that has to be kept in sync with issues.

Prefer the **issue body** over custom GitHub metadata unless there
is a clear need for the metadata. The issue body should contain the
canonical task description in a stable, easy-to-scan format.

### Narrow, not umbrella

- Use **many narrow issues** rather than a few large umbrella issues.
- Prefer issues scoped to one API surface, one proof cluster, one
  algorithmic subcomponent, or one benchmark/conformance target.
- Large umbrella issues are fine for human orientation, but
  execution should happen in smaller child or blocking issues.

Good issue sizes include:

- one major structure plus its immediate API;
- one SPEC subsection with a coherent implementation target;
- one theorem cluster that obviously belongs together;
- one conformance or benchmark slice for a single subsystem.

Avoid issues that mix:

- multiple libraries with weak coupling;
- implementation plus broad cleanup across unrelated files;
- an entire library's worth of declarations unless the library is tiny.

### Canonical issue body shape

Keep issue bodies simple Markdown, but standardize the section
headings so agents can read and write them consistently. Default
shape:

- **Current state** — what is already true, and what assumptions the
  worker should begin from.
- **Deliverables** — the concrete outputs expected from this issue.
- **Library placement** — the file path the deliverables will land in,
  the SPEC § that governs that path (quote 1–3 lines), and a one-line
  answer to each of the four placement questions in
  [Library placement is a hard precondition](#library-placement-is-a-hard-precondition).
  If any answer is "unknown" or "blocked", file the prerequisite issue
  first and add `depends-on:` here; do not file the dependent issue.
- **Context** — links to every SPEC file the worker should re-read,
  including adjacent ones likely to be relevant (the library being
  touched, sibling library SPECs whose contracts cross the boundary,
  `SPEC/design-principles.md` when complexity or extern policy is in
  play). Plus related issues, PRs, conformance/bench artefacts, and
  any PLAN sections that govern the phase.
- **Verification** — the checks to run for this issue.
- **Out of scope** — nearby work that should not be folded into this
  issue.

For hard blockers, include explicit dependency lines in the body:

```text
depends-on: #123
depends-on: #124
```

Keep these lines literal and easy to grep. They are the only
dependency syntax the orchestration layer should rely on by default.

### Library placement is a hard precondition

Every issue that adds or modifies a Lean declaration names its target
file *and justifies it*. Decomposition inherits the parent's
placement only if the parent's placement was justified; otherwise
re-justify in the child. A worker who picks up an issue whose Library
placement is missing or wrong stops, fixes the issue, and re-queues —
they do not "fix it in the PR".

Answer all four. One line each is enough.

1. **Which SPEC § governs this file?** Quote the sentence that pins
   the deliverable to a library or file. If no SPEC § names this
   placement, the issue is not ready: file a SPEC-clarification
   issue first.
2. **Does the natural strategy use Mathlib?** If yes, the file lives
   in a `*-mathlib` bridge library. Mathlib-free libraries cannot
   host a proof whose shortest path goes through `Matrix.adjugate`,
   the universal polynomial ring, `MvPolynomial`,
   `IsIntegralClosure`, or similar. "We will reprove the Mathlib
   lemma locally" is not a justification; it is the failure mode
   this rule exists to catch.
3. **Is this result already in Mathlib, or in an open Mathlib PR?**
   Choose one strategy:
   - **Import** if it is on Mathlib `master` *now*.
   - **Inline with attribution** otherwise — including any open,
     draft, or stalled PR. Hex moves much faster than Mathlib's
     review cycle and treats Mathlib as a static artefact; do not
     gate hex on upstream merging. Copy the proof in, modify
     types/namespaces/proof shape as needed, credit the upstream
     author(s) in a file-level docstring linking the PR.
   What is *not* allowed: reproving from a blank page without
   consulting the upstream work.
4. **Does the deliverable presuppose missing infrastructure?**
   Type-class instances the statement quantifies over (`HPow`,
   `Module`, `Algebra`), helper definitions, kernel-reducible
   evaluators. If yes, file the infrastructure issue first and
   `depends-on:` it here. A claim against a non-statable theorem is
   churn, not progress.

A `depends-on:` answer to any of (1)–(4) is healthy. An unanswered
question is the failure shape.

### Bench-found, conformance-found, and audit-found issues

Issues filed in response to a benchmark verdict mismatch, a
conformance failure, or an **audit finding** use the [canonical
issue body shape](#canonical-issue-body-shape) plus a **Symptom**
section recording the evidence:

- **Declared expectation.** For a bench finding: the complexity model
  declared in `setup_benchmark` (e.g. `n => n * Nat.log2 (n + 1)`).
  For a conformance finding: the property the failing `#guard` was
  checking, or the oracle's expected output. For an audit finding:
  the SPEC clause the audited work was claimed to satisfy.
- **Observed result.** For a bench finding: the verdict text emitted
  by `lake exe ... run NAME` (e.g. `inconclusive (cMin=10.5,
  cMax=25.3, β=0.42)`), plus a copy of the relevant JSONL rows. For
  a conformance finding: the failing input, the Lean output, and the
  oracle output. For an audit finding: the specific evidence (a
  bench input the algorithm short-circuits past, a profile entry
  showing a dominant cost not attributed to a registered target,
  a comparator named in the per-library SPEC but not wired, etc.).
- **Root-cause hypothesis.** One paragraph: what algorithmic shape
  produces this observation? "Quadratic on `p` because we search
  `List.range p`," "factor of `n` slower because we rebuild
  Gram–Schmidt instead of incremental update," etc. Best guess is
  enough; the next agent verifies.

The **Deliverables** section lists two PRs:

1. The rollback PR setting `libraries.yml[L].done_through` backward
   (per [Rollback is a normal action](#rollback-is-a-normal-action)).
2. The implementation PR fixing the bug at the rolled-back phase.

Cross-link both PRs to this issue.

#### What "audit finding" means

A bench verdict mismatch and a conformance failure both fire from
an automated check. An audit finding fires from an author writing
a headline report, reviewing a Phase-4 claim, or otherwise
auditing existing work, and noticing something that warrants an
issue **even though no automated verdict fired**.

Examples (illustrative, not exhaustive):

- A bench input is degenerate so the algorithm short-circuits
  past it (e.g. an LLL bench whose only end-to-end target uses
  the identity basis, where no Lovász swap fires).
- A comparator the per-library SPEC requires is not wired.
- A profile shows a dominant inclusive cost the bench targets
  do not measure (per
  [SPEC/benchmarking.md §Attribution rule](../SPEC/benchmarking.md#the-attribution-rule)).
- An end-to-end target's empirical slope visibly disagrees with
  its declared complexity over the parameter ladder.
- A per-library SPEC names no comparator for an algorithm where
  external references obviously exist (LLL, factoring, GCD, ...)
  and Phase 4's comparator clause is being claimed satisfied
  vacuously.

When an audit finding occurs while writing a headline report:

1. File the canonical issue using the body shape above.
2. Link the issue from the report's §Concerns subsection.
3. Complete the rest of the report.

The library cannot **remain** at `done_through: 4` while the
Concern is unresolved (per
[PLAN/Phase4.md §Exit criteria](Phase4.md#exit-criteria)).
Resolution available to the orchestrator: act on the HO issue
tied to the Concern until the underlying problem is fixed and
the Concern entry is removed from the report.

### Decomposition is normal

If an agent is assigned an issue and concludes that it is too large
for one session, that is a normal outcome, not a failure.

Expected behavior:

- decompose the issue into smaller GitHub issues itself when it has
  enough context to do so well;
- link the new issues clearly as follow-up, blocking, or child work;
- add `depends-on: #N` lines where ordering matters;
- narrow the original issue if some subset is still tractable;
- if appropriate, stop after opening the smaller issues rather than
  attempting an oversized implementation.

Worker-created follow-up issues are encouraged when they improve
queue quality. Do not require a separate planning round-trip just
to split an issue that is clearly too large.

### Partial progress is valuable

Agents should not wait for total completion before contributing
useful work. Partial progress is encouraged when it leaves the
repository in a better state and makes follow-up work easier.

Good partial-progress outputs include:

- a PR that lands a coherent subset of the intended work;
- scaffolded declarations with correct boundaries and notes about
  what remains;
- proof skeletons or helper lemmas that unblock later work;
- benchmark or conformance harnesses without full coverage yet.

When an issue is only partially completed, the agent should
normally:

- open a PR for the finished subset if it is mergeable;
- open one or more follow-up issues for the remainder;
- record the new boundaries clearly so later agents can resume
  without re-discovering the decomposition.

---

## `libraries.yml` model

### Phase-dependency rule table

Notation: write `L.dt` for `libraries.yml[L].done_through`, `L.deps`
for L's direct dependencies. "Ready to start phase K" means all
prerequisites below are met.

| K | Name                       | Coupling    | Within-L prereq | Cross-lib prereq                   | Exit ⇒ set |
|---|----------------------------|-------------|-----------------|-------------------------------------|------------|
| 0 | Monorepo scaffolding       | global      | —               | —                                   | monorepo bootstrap lands on `main` |
| 1 | Library scaffolding        | dep-coupled | `L.dt ≥ 0`      | every `d ∈ L.deps: d.dt ≥ 1`        | `L.dt = 1` |
| 2 | Scaffolding review         | local       | `L.dt ≥ 1`      | —                                   | `L.dt = 2` |
| 3 | Conformance testing        | dep-coupled | `L.dt ≥ 2`      | every `d ∈ L.deps: d.dt ≥ 3`        | `L.dt = 3` |
| 4 | Performance & benchmarking | dep-coupled | `L.dt ≥ 3`      | every `d ∈ L.deps: d.dt ≥ 4`        | `L.dt = 4` |
| 5 | Implementation work loop   | local       | `L.dt ≥ 4`      | —                                   | `L.dt = 5` |
| 6 | Proof polishing            | local       | `L.dt ≥ 5`      | —                                   | `L.dt = 6` |
| 7 | User-facing documentation  | local       | `L.dt ≥ 6`      | —                                   | `L.dt = 7` |

This table is consumed mechanically by `scripts/status.py`. An agent
normally does not need to evaluate it by hand — run the script and
read its output.

### `done_through` semantics

- `done_through: K` means **phases 1..K are all complete** for L
  (linear, no skipping).
- `done_through: 0` is the seed state: no per-library phase is done,
  L is ready to start Phase 1 once the global Phase 0 bootstrap is
  complete.
- `done_through: 7` is fully done.
- Phase 0 is *global*, not per-library — its completion is observable
  via on-disk artifacts (`lakefile.lean`, `scripts/check_dag.py`,
  etc.), not via any `libraries.yml` field.
- "Dep-coupled" phases (1, 3, 4) require same-phase completion in
  every direct dep before L can start them. "Local" phases (2, 5,
  6, 7) require no cross-library gates.
- Strict linear: L cannot start Phase K before completing Phase K-1.
  `done_through` is an integer prefix, not an arbitrary set.
- Once deps reach `dep.dt ≥ 4`, the hardest cross-lib gate is
  satisfied and L can run through all subsequent local phases (5, 6,
  7) regardless of where deps go next.

### Rollback is a normal action

Bumping `done_through` *backward* is a normal, encouraged action
when conformance or benchmarking finds an implementation bug. The
forward bump records "phases 1..K are complete"; a backward bump
records "we discovered phase ≤K wasn't actually complete and we are
redoing it." Both directions are first-class.

Operationally, rolling library `L` back from `K` to `K-1` (or
further) means:

1. File a GitHub issue describing the bug; use the issue body shape
   in [Issue creation](#issue-creation), with the extra **Symptom**
   section described under [Bench-found and conformance-found
   issues](#bench-found-and-conformance-found-issues).
2. Close any open phase-K PRs whose work depends on the broken code
   (or convert them to draft and add `depends-on: <issue>`).
3. Edit `libraries.yml` to set the affected library's `done_through`
   to the new lower value, in a small dedicated PR. The PR
   description names the issue.
4. Mark any cross-library work that was unblocked by `L.dt ≥ K` as
   blocked again where appropriate. The phase-dependency table
   (above) makes this mechanical: any `M` with `L ∈ M.deps` and a
   dep-coupled phase ≥ K is now ineligible until L recovers.

The next agent picking up `L` enters the rolled-back phase with the
bug-finding evidence (the issue, the JSONL artefact for a bench
finding, the failing `#guard` for a conformance finding) as its
context.

Rollback is preferable to "weaken the test" or "lower the parameter
range to make the bench pass" — both forms of paving over the bug.
[SPEC/benchmarking.md](../SPEC/benchmarking.md) explicitly forbids
the latter.

### Where state lives

`libraries.yml` holds the mutable per-library phase counter plus
structural DAG data (`deps`, `mathlib`). Other state mechanisms:

- **GitHub issues** — the canonical work-item tracker; what is
  *being worked on right now*.
- **`status/hex-foo.<milestone>` tokens** — immutable point-in-time
  attestations (currently: `scaffolding-reviewed` for Phase 2
  sign-off). Complementary to `libraries.yml`, not subsumed by it.
- **`progress/` directory** — per-turn agent session notes (see
  [.claude/CLAUDE.md](../.claude/CLAUDE.md)).
- **`PLAN/` and `PLAN.md`** — reference material, not progress state.
  Do not modify them for progress tracking.

### Library status (active | planned | draft)

Every entry in `libraries.yml` carries an explicit `status` field
with exactly one of three values:

- **`active`** — implementation is in progress or complete. The
  orchestrator dispatches Phase work against this library.
- **`planned`** — SPEC is finished and ready for implementation,
  but implementation is deferred. The library appears in the dep
  graph as informational structure but no work is dispatched.
  Activation is a one-line edit (`status: planned → active`).
- **`draft`** — SPEC is a work-in-progress; ideas captured but the
  contract is not yet stable enough to implement against. Same
  orchestration treatment as `planned`. Promote to `planned` (or
  `active`) when the SPEC firms up.

The following invariants are normative and enforced at yml-load
time (parse errors, not lint warnings):

1. **`status` is required.** Every entry must declare exactly one
   of `active`, `planned`, `draft`. Missing or unrecognised values
   are parse errors.
2. **`planned` and `draft` ⟹ `done_through == 0`.** Non-active
   libraries cannot have Phase progress recorded against them.
   Pausing a mid-implementation library is *not* a supported state;
   roll `done_through` back per [§"Rollback is a normal action"](#rollback-is-a-normal-action)
   if you need to take a library out of dispatch.
3. **`active` libraries depend only on `active` libraries.**
   Activating a library commits its full transitive dependency
   closure to `active`. Non-`active` libraries may depend on
   anything (the dep graph is informational and may reference
   libraries in any state).

The following two structural rules apply per status:

4. **Lake alignment.** An `active` entry must have a corresponding
   `lean_lib` in `lakefile.toml`; a `planned` or `draft` entry
   must *not*.
5. **Root-file existence.** An `active` entry must have a root
   `<Name>.lean` at the repo top level; a `planned` or `draft`
   entry must *not*.

Reference implementation lives in `scripts/libgraph.py` (validation
of invariants 1–3) and `scripts/check_dag.py` (rules 4 and 5). If
those scripts are rewritten, the rewrite must implement these
invariants — the contract above is normative, the script names are
descriptive.
