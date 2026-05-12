# hex — agent-specific conventions

Conventions specifically for LLM agents working on this project.
General project doctrine (Mathlib-free split, SPEC/PLAN structure,
key files) lives in `SPEC/` and `PLAN.md`; start there for
orientation.

## Style

Don't add "research completed" timestamps, progress notes, or
meta-commentary about the history of our research process to any
file. The git history tracks that. SPEC files and `PLAN/` contain
the current state of the design, not a journal of how we got there.

## Per-turn progress files

Start of turn: read the most recent file in `progress/` (ISO-8601
timestamps sort chronologically). If only `progress/0000-init.md`
exists, the repo is freshly initialised — proceed with Phase 0.

End of turn: write `progress/<UTC-timestamp>.md` with sections
**Accomplished** / **Current frontier** / **Next step** / **Blockers**.
Scope these to *your* session — what you touched, where you stopped,
what you think comes next for your corner of the project.
Commits made during the turn should mention the progress file.

## Lean

Check diagnostics after every step; don't continue past errors. Build
via `lake build`, not `lean` directly. `native_decide` is banned (see
SPEC).

Never introduce an `axiom`. This includes converting an existing
`theorem`/`def`/`example` into an `axiom` when a refactor breaks its
proof — fix the proof or fix the API. For unfinished proofs use
`sorry`, which is grep-able and produces a warning; `axiom` is silent.

## CI: extend, don't fan out

Before touching anything under `.github/workflows/`, read
[SPEC/CI.md](../SPEC/CI.md). Each workflow runs in **exactly one
ubuntu job** (`ci.yml` also has one macOS job for the dyld
cross-check). New conformance targets and new oracles **extend the
script** of the existing single job — they do not introduce new
top-level jobs, `strategy.matrix` blocks, or new workflow files.
New oracles append a tuple to `scripts/ci/run_oracles.sh` and (if
needed) an entry to the existing apt/pip install step; see
[SPEC/testing.md § Adding a new oracle](../SPEC/testing.md).

Bench targets are not added by extending CI — see §Benchmarks.

GitHub-hosted Actions on a personal account is concurrency-capped at
~20 parallel ubuntu runners across all repositories the account
owns; a 10-entry matrix saturates the cap, a 40-entry matrix
produces 24-hour queue waits. Per-target parallelism does not
amortise the fixed Mathlib cache fetch and startup cost on this
project, so the rule is "no parallelism in CI." Routine timing-
sensitive runs live on a separate scheduled workflow on dedicated
hardware (per [SPEC/benchmarking.md](../SPEC/benchmarking.md)),
not on the merge-gating workflows.

## Benchmarks

`lake exe X_bench verify` runs worker-side, not in CI. Before
publishing a PR whose diff touches non-proof Lean files under
`Hex/*/`:

1. `scripts/bench/affected_benches.sh <changed-files...>` lists
   affected `*_bench` targets.
2. `lake exe X_bench verify` each one.
3. PR body must include `Affected benches: <list>` (or `none`).

Failure modes and the verify→fixture-commit rule live in
[SPEC/benchmarking.md §Worker affected-bench discipline](../SPEC/benchmarking.md).
A pre-merge `affected-benches-check` status check validates the PR
body matches the computed set; a nightly workflow on `main` is the
backstop.
