# Hex repo family

`hex-dev` is the development monorepo where new Hex sublibraries are
incubated before they are split out for release. `hex` is the released
aggregate repo; it depends on released split libraries at exact Lake
revisions.

The currently pinned upstream split repos for `hex` are:

- `hex-matrix`
- `hex-matrix-mathlib`
- `hex-gram-schmidt`
- `hex-gram-schmidt-mathlib`
- `hex-lll`
- `hex-lll-mathlib`

Treat this as the current pinned set, not a permanent exhaustive list:
more sublibraries may be released from `hex-dev` later. Computational
libraries are Mathlib-free; `*-mathlib` repos are the Mathlib bridge
layers and should contain correspondence proofs and Mathlib-facing APIs.

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

## Directives are hypotheses, not specs

When you claim a directive issue, the body is the author's *current
best understanding* of what the work looks like. It is not gospel.
Before opening a PR, sanity-check the premise:

- Does the type signature the directive asks for actually admit a
  proof, or is it unsoundly typed (allows non-canonical witnesses,
  missing hypotheses, vacuous quantifiers)?
- Does the existing infrastructure the directive points at actually
  support the claimed composition, or is a key bridge missing?
- Is the decomposition the directive proposes the right one, or
  would a different split close the obligation in fewer pieces?

If the premise is sound: execute. If the premise is wrong: **stop,
comment on the issue explaining what's wrong with concrete
evidence (counterexample, missing-lemma shape, infrastructure
gap), and leave the directive claimable for an updated version.**
Do *not* file a sub-decomposition issue as a workaround; that
escalates the problem rather than fixing it. Do *not* invent
sorries or axioms to bash through. Do *not* silently weaken the
theorem to make a proof go through; that hides the premise problem
from the next reviewer.

A worker who correctly diagnoses an unsound directive saves more
project time than one who lands a partial PR against it.

The author of a directive (often me or another agent) cannot see
every interaction with existing types and lemmas at directive-
authoring time. Reading the source, finding the contradiction, and
posting it back is the highest-leverage thing you can do when the
directive doesn't match reality.

## Naming: short verb-noun forms

Type / def / theorem names with more than ~3 qualifiers are a
smell. If you find yourself writing five or more qualifying words,
stop and rethink:

- Often the qualifiers belong in a namespace, not the name.
- Often the name is restating *use-site context* ("Initial",
  "Regular", "Step") rather than naming the *thing*. Find the
  noun.
- The Mathlib aesthetic to imitate: short verb-noun forms,
  qualifiers in namespaces. `Matrix.det`, not
  `MatrixLeibnizExpandedFiniteDeterminantValue`.

When you encounter an existing AI-slop name with 5+ qualifiers
(the pattern from a model adding defensive disambiguation), rename
it. Long names are tech debt; the next agent has to keep them
exactly as long. Renaming is cheap; preserving slop is expensive.

Concrete heuristic: if a name's qualifier list reads like a
sentence describing what it's used for, that sentence belongs in
the docstring, and the name should be the noun.

## CI: extend, don't fan out

Before touching anything under `.github/workflows/`, read
[SPEC/CI.md](../SPEC/CI.md). Each workflow runs in **exactly one
ubuntu job** (`ci.yml` also has one macOS job for the dyld
cross-check). New conformance targets, new oracles, and new bench
targets **extend the script** of the existing single job — they do
not introduce new top-level jobs, `strategy.matrix` blocks, or new
workflow files. New oracles append a tuple to
`scripts/ci/run_oracles.sh` and (if needed) an entry to the existing
apt/pip install step; see
[SPEC/testing.md § Adding a new oracle](../SPEC/testing.md).

Bench targets in particular must not import Mathlib (directly or
transitively) and must keep the `Bench verify` step under its
wallclock cap; see
[SPEC/benchmarking.md §Mathlib-free benches](../SPEC/benchmarking.md)
and the "Time budget" subsection of
[SPEC/benchmarking.md §CI integration](../SPEC/benchmarking.md).

GitHub-hosted Actions on a personal account is concurrency-capped at
~20 parallel ubuntu runners across all repositories the account
owns; a 10-entry matrix saturates the cap, a 40-entry matrix
produces 24-hour queue waits. Per-target parallelism does not
amortise the fixed Mathlib cache fetch and startup cost on this
project, so the rule is "no parallelism in CI." Routine timing-
sensitive runs live on a separate scheduled workflow on dedicated
hardware (per [SPEC/benchmarking.md](../SPEC/benchmarking.md)),
not on the merge-gating workflows.


# Pod Agent Session

You are running as an autonomous agent launched by `pod`. This is a
non-interactive session via `claude -p` — there is no human to answer
questions. Never ask for confirmation or approval. Just do the work.

Each agent runs in its own git worktree on its own branch, coordinating
via GitHub issues, labels, and PRs. The `coordination` script is already
on your PATH — just run it directly (e.g. `coordination orient`,
`coordination claim 42`). Do NOT search for it or try to locate it.

Session UUID is available as `$POD_SESSION_ID`.

## Agent Types

- **Planners** (`/plan`): create work items as GitHub issues, then exit
- **Workers** (`/feature`, `/review`, `/summarize`, `/meditate`): claim
  and execute issues using the `agent-worker-flow` skill
- **Repair** (`/repair`): salvage unhealthy PRs (merge conflicts, failed
  CI, stuck CI) using the `pr-repair-flow` skill. Dispatched by pod ahead
  of planners and workers whenever `coordination list-pr-repair` reports
  candidates. Two outcomes only: salvaged or abandoned (→ `replan` on the
  linked issue). No escalation to humans.

See your `/command` file and the relevant skill (`agent-worker-flow` or
`pr-repair-flow`) for the full workflow.

## Off-limits Files

Agents must not modify the project's top-level CLAUDE.md (`.claude/CLAUDE.md`)
or roadmap file (`PLAN.md`). PRs touching these files are rejected by
`coordination create-pr`. Update skills and commands instead.
