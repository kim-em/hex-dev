# hex-dev

Verified computational algebra in Lean 4.

**If you want to *use* Hex, you want https://github.com/leanprover/hex, not
this repository.** That is the released aggregate: it depends on the split
Hex libraries at exact Lake revisions and is what downstream projects should
add as a dependency.

**Documentation: https://kim-em.github.io/hex-dev/** is the Hex manual,
rendered from `HexManual/` and published on every push to `main`.

## What this repository is

`hex-dev` is the development monorepo. Every Hex library is developed here,
in one tree, so that a single `lake build` (plus the `bench/` and
`conformance/` sub-projects) builds the whole dependency graph together and
a change that breaks a downstream library shows up immediately.

The released repositories are **published mirrors**, not places to work: a
dispatchable CI workflow regenerates each one from the matching content
here, rewrites its cross-repo Lake pins, and commits to its `main`. Never
hand-edit a released repo; change it here and let the sync publish it.

The authoritative list of published libraries, in topological order and with
each one's cross-repo pins, is
[`scripts/release/released.yml`](scripts/release/released.yml).

## Orientation

- Specification: [SPEC/SPEC.md](SPEC/SPEC.md)
- Execution plan: [PLAN.md](PLAN.md)
- Library DAG and phase state: [libraries.yml](libraries.yml)
- Development setup and workflow: [DEV.md](DEV.md)
- Publish-out manifest: [scripts/release/released.yml](scripts/release/released.yml)
