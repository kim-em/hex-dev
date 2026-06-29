# Split plan hard review

## Accomplished

Reviewed `/Users/kim/.claude/plans/i-need-your-help-delightful-cerf.md`
against the current Lake config, manifests, CI workflows, conformance/oracle
scripts, library graph scripts, LLL FFI wiring, root umbrellas, and selected
SPEC rules. Ran small isolated Lake 5.0.0 experiments under `/private/tmp` for
sidecar `path = ".."`, diamond dependency name conflicts, and downstream
consumption of a Lean-lakefile package with an `extern_lib`.

## Current frontier

The main correctness issues are Lake's silent, order-dependent handling of
same-name dependency conflicts in a diamond; the current root modules
re-exporting conformance modules that the plan moves into sidecars; and
hex-dev scripts/CI still assuming the six released libraries are local
`lean_lib`s unless the surgery explicitly updates those checks.

## Next step

Before executing the split, revise the plan to require a manifest/pin
consistency gate for all Hex package names, remove sidecar-only conformance
imports from released root modules, and define exact script/workflow rewrites
for `libraries.yml` external entries, conformance targets, bench lints, oracle
paths, and phase/report checks.

## Blockers

Network is unavailable in this session, so I could not fully exercise
`lake exe cache get` in a freshly resolved downstream repo with Mathlib only
through a transitive Hex bridge. The local repo's `lake exe cache` works with
Mathlib direct, and the temp transitive test reached network resolution of
Mathlib's inherited dependencies before it could test cache execution.
