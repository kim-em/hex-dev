# CI cache cleanup and post-upgrade repair

## Accomplished

- Replaced the per-run combined GitHub cache with dependency-scoped
  restore/save actions. Pull requests and Pages restore compatible snapshots,
  but only a fully verified `main` push saves one, avoiding branch-isolated
  snapshots that had filled the repository cache quota.
- Disabled `leanprover/lean-action`'s separate whole-`.lake` cache in both
  workflows, made the public Lake/R2 restore a fallback only on a GitHub cache
  miss, and moved both shared-cache publications after the fail-closed gate.
- Documented the cache ownership and the interim status of the rate-limited
  `r2.dev` endpoint. A custom domain remains the durable serving path once the
  `hex` Cloudflare account owns a zone.
- Repaired the post-v4.34 `main` freshness failure with an exact blob-to-blob
  runtime exemption for sparse-poly-only `lakefile.lean` registrations that
  landed while the factor sweep was running.
- Verified both workflow files parse as YAML, the exemption JSON parses,
  factor-sweep freshness passes, all 25 committed factor figures are current,
  and `git diff --check` passes.

## Current frontier

`ci/hex-cache-cleanup`, ready to push and exercise in pull-request CI.

## Next step

Open the pull request and inspect the Actions job directly. On this first
dependency-scoped run GitHub should miss (the old keys are intentionally
incompatible), so the R2 fallback should be attempted. After merge, verify a
successful `main` run saves the GitHub snapshot and uploads the Lake mapping;
then a later PR should restore GitHub and skip R2.

## Blockers

None.
