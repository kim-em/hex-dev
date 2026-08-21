# Second publishing token for the release sync

## Accomplished

- Created the seven `leanprover/` repositories for the next publish wave
  (hex-resultant, hex-resultant-mathlib, hex-number-field,
  hex-number-field-mathlib, hex-number-field-tower,
  hex-number-field-tower-mathlib, hex-rcf), empty and public, matching
  the state of the already-created hex-poly-fp-mathlib.
- The fine-grained `hex-publishing` token hit its selected-repository
  cap while adding them, so Kim created `hex-publishing-2` (carrying the
  two hex-resultant repos) and stores it as the `RELEASED_SYNC_PAT_2`
  secret on kim-em/hex-dev.
- Taught the sync to route across multiple tokens: `sync_released.py`
  now collects `$RELEASED_SYNC_PAT`, `$RELEASED_SYNC_PAT_2`, ... (or
  repeated `--token`), and the preflight probes each target repository
  against each token, assigning every clone and push the first token
  that can see that repository. No manifest bookkeeping of which
  library is on which token. Updated the workflow env, the
  released.yml header, and PLAN/Releases.md accordingly.
- Unit-tested the routing and env-collection helpers and smoke-ran a
  no-token `--dry-run --only hex-basic`.

## Current frontier

- Token approvals pending: the six-repo request on `hex-publishing`
  and the new `hex-publishing-2` need org-owner approval.
- The repos still need their un-managed Lake/CI skeletons
  (scripts/release/BOOTSTRAP.md) before released.yml entries can land.

## Next step

- After approvals: skeletons, then released.yml entries in pin order
  (hex-poly-fp-mathlib and hex-resultant first).

## Blockers

- Org-owner approval for both token requests.
