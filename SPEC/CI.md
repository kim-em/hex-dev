# CI doctrine

Normative rules for every GitHub Actions workflow under
`.github/workflows/`. Read this before editing any workflow file or
adding a new one.

The rules in this file are tight on purpose. CI for this repository
is shared with several other repositories under the same personal
account (`kim-em/pod`, `kim-em/bubble`, …); a fan-out here pushes
queue waits up to a day across all of them. The rules below cap that
exposure at the source.

## Triggers

Every workflow uses **exactly** this trigger shape:

```yaml
on:
  push:
    branches: [main]
  pull_request:
  # plus workflow_dispatch: where useful
```

The bare `on: [push, pull_request]` form is forbidden. It fires
twice on every PR commit (once for the push event, once for the
pull-request synchronize event) and once on every push to every
agent/feature branch even before a PR exists. Restricting `push:` to
`main` and relying on `pull_request:` for everything else makes each
PR commit fire each workflow exactly once.

`workflow_dispatch:` is allowed wherever an ad-hoc manual run is
useful (currently `conformance.yml`).

Other triggers (`schedule:`, `repository_dispatch:`, `release:`,
`merge_group:`) are case-by-case; they must be documented in the
workflow file with a comment explaining why they're justified.
`merge_group:` is **not** in use on this repo: GitHub's merge queue
is unavailable on the personal-account plan that owns the repo, so
adding a `merge_group:` trigger would just be dead configuration.
Revisit if the account ever moves to a plan that supports the queue.

## Concurrency

Every workflow MUST set:

```yaml
concurrency:
  group: ${{ github.workflow }}-${{ github.ref }}
  cancel-in-progress: true
```

The group is `<workflow>-<ref>` so different workflows don't cancel
each other but repeated commits to the same branch do. Without this,
agent branches that re-push during a session leave a tail of queued
runs that will all eventually pick up runners — pure waste.

`cancel-in-progress: true` is the default the project wants; do not
flip it to `false` without a documented reason. Conformance "almost
finished" on a now-superseded commit is not worth keeping.

## Job-count budget

**Each workflow run uses exactly one ubuntu job.** The CI workflow
also has one macOS job (the dyld cross-check). No other parallelism.

Concretely:

- `ci.yml`: one `build` ubuntu job (DAG checks, hex `lake build`,
  per-library `bench verify` smoke gate per
  [SPEC/benchmarking.md §CI integration](benchmarking.md), plus the
  structural and timing lints named there) and one `build-macos`
  macOS job (hex `lake build` only — the dyld cross-check).
  **Bench verify runs on ubuntu, not macOS**: the macOS job exists
  for symbol-resolution coverage, not benchmarking, and macOS runners
  are 10× the cost and a fraction of the concurrency. Per
  [SPEC/benchmarking.md §CI integration](benchmarking.md), `verify`
  is a smoke gate (does the bench module compile and run?), not a
  timing measurement; timing-relevant runs live on a separate
  scheduled workflow on dedicated hardware.
- `conformance.yml`: one ubuntu job that runs the full conformance
  matrix and every oracle (FLINT, PARI, fpLLL, Conway) sequentially
  inside that single runner.
- Future workflows: one ubuntu job, period. If a second runner is
  genuinely needed (e.g. a separate macOS bench cross-check), state
  the reason in a workflow-level comment.

**Do not introduce matrices.** GitHub-hosted Actions on a personal
account is concurrency-capped at ~20 parallel ubuntu runners across
*all* repositories owned by the account. A 10-entry matrix on one
push will saturate the cap by itself; a 40-entry matrix will create
24-hour queue waits. Per-target parallelism does not pay back in
this project — every job re-builds the project's own Lean libraries
on top of Mathlib, so a matrix entry that "only does one target"
still pays the same fixed startup cost as the consolidated job.

**New oracles, new conformance targets, and new bench targets
extend the script of the single existing job.** Add an apt step for
new system deps, a pip step for new Python deps, and a sequential
shell loop for new per-library checks. Do not add a new top-level
job, do not add `strategy.matrix`, and do not split a workflow. For
benches specifically, the structural and timing rules in
[SPEC/benchmarking.md §Mathlib-free benches](benchmarking.md) and
[SPEC/benchmarking.md §CI integration "Time budget"](benchmarking.md)
constrain what a new bench is allowed to look like.

## Mathlib cache is mandatory

Hex depends transitively on Mathlib (see `lakefile.lean`). Every
job that runs `lake build` MUST first run `lake exe cache get` and
then **hard-fail** if any Mathlib `.olean` would still be rebuilt
from source.

The hard-fail gate is `scripts/ci/check_no_mathlib_rebuild.sh`,
which is responsible for:

- running `lake exe cache get`;
- inspecting Lake's reported plan (e.g. via `lake build Mathlib
  --no-build` or by parsing `cache get`'s own output) to confirm
  every Mathlib module already has a fetched `.olean`;
- exiting non-zero with a clear message if any Mathlib module would
  be rebuilt from source.

The reason is operational, not aesthetic. Mathlib has thousands of
modules; rebuilding from source on each runner adds 30+ minutes of
compilation per job. Pre-cache, hex CI was spending the bulk of
every runner-minute recompiling Mathlib that someone had already
compiled upstream — that was the dominant cost driver of the
24-hour queue this doctrine exists to prevent.

A stale or missing cache is a fixable upstream problem (the
Mathlib `cache` service publishes oleans for every Mathlib commit
on `master`); the right response is to fix the upstream pin or the
cache step, not to silently rebuild.

## Branch protection

`main` requires every status check produced by `ci.yml` and
`conformance.yml` to pass before merge. The pod auto-merger
(`gh pr merge --auto`) respects branch protection, so this is the
mechanism that gates merges on CI.

Required contexts (kept in sync with the actual job names in the
workflow files):

- `build` (from `ci.yml`)
- `build-macos` (from `ci.yml`)
- `conformance` (from `conformance.yml`)

`required_status_checks.strict` is `false`. With `strict: true`,
every merge to `main` flips every other open PR to `BEHIND` and
auto-merge will not fire on a behind branch — without a merge queue
to serially rebase the queue (see Triggers above; the queue is
unavailable on this account's plan), this serialises the whole repo
on a manual "Update branch" click per PR per merge, which in
practice means PRs sit forever. Accepting `strict: false` means a
merged commit was tested against the tip of `main` *as of when its
PR's CI last ran*, not the current tip — for this repo's workload
(largely orthogonal proof additions on top of a green tree), that
trade-off is acceptable. Reconsider if a future change makes
cross-PR conflicts more likely.

`enforce_admins: false` is acceptable — humans occasionally need to
override (e.g. a known-good revert during incident response). PR
reviews are not required by branch protection; review policy lives
elsewhere.

When job names change, the protection contexts need to be updated
in the same PR via `gh api -X PUT
/repos/<owner>/<repo>/branches/main/protection`. Update this section
of `SPEC/CI.md` simultaneously so the source of truth doesn't
drift.

## Runners

GitHub-hosted runners only at this stage: `ubuntu-latest`,
`macos-latest`. Self-hosted runners would solve the concurrency
problem but introduce maintenance burden, secrets management, and a
trust boundary that this project hasn't decided on. If the
single-job budget plus the cache discipline isn't enough, revisit
self-hosted runners explicitly rather than drifting toward them.

## How to add new CI work

To add a new conformance check, oracle, benchmark, or build target:

1. **Default**: extend the script of the existing single job in the
   workflow that already covers this kind of work (`conformance.yml`
   for conformance/oracle, `ci.yml` for build/check/benchmark).
2. Add any new system dependency to the existing apt/brew step.
3. Add any new Python or Lean dependency to the existing install
   step.
4. Add a new sequential block to the helper script (e.g.
   `scripts/ci/run_oracles.sh`) that performs the new check.
5. Confirm the run still fits in one ubuntu job and the Mathlib
   cache fetch still passes the hard-fail gate.
6. Update the relevant SPEC and PLAN cross-references (this file,
   `PLAN/Phase0.md` §6, `SPEC/testing.md`'s "Adding a new oracle"
   section) if the change introduces a new category of check.

**Bench targets are constrained** by the structural and timing rules
in [SPEC/benchmarking.md §Mathlib-free benches](benchmarking.md) and
[SPEC/benchmarking.md §CI integration "Time budget"](benchmarking.md):
no bench may import any `Mathlib.*` module (directly or transitively),
and the per-PR `Bench verify` total has a hard wallclock cap. Both
are enforced by lint scripts named in those sections, invoked from
the `build` job.

A new top-level workflow is justified only by a clearly distinct
class of CI work that genuinely cannot share a runner with existing
work — e.g. a release workflow that runs on tag push only. Even
then, the trigger, concurrency, single-job, and cache rules above
all still apply.
