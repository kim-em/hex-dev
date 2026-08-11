# docgen plan review

## Accomplished

Reviewed the proposed `leanprover/hex` doc-gen4 API documentation plan
against the current `docgen-action` README/source, `lean-action` docs, and
the inspection clone at `/tmp/hex-inspect`. Verified that the released
aggregate uses `lakefile.toml`, has `defaultTargets = ["HexAll"]`, and
already uses an explicit Mathlib cache rebuild guard in CI.

## Current frontier

The plan is broadly viable, but the workflow needs corrections around
`workflow_dispatch`, preserving the existing Mathlib rebuild guard, action
pinning, concurrency, and the exact meaning of docgen's cache/build behavior.

## Next step

If implementing, copy the existing CI setup/cache/build guard into
`docs.yml`, keep `docgen-action` for the docs/deploy path, and either remove
manual-dispatch expectations or hand-roll the docs/deploy steps so manual
runs actually publish.

## Blockers

None for the review.
