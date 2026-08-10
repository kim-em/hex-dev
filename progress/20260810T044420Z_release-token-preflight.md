# Publishing-token preflight

## Accomplished

The first real sync after the documentation change failed three
repositories in, with `403 Permission to leanprover/hex-arith.git denied
to kim-em`. Nothing was published: the two repositories ahead of it were
both "no changes", so no push had succeeded yet.

The cause is not an expired credential. `RELEASED_SYNC_PAT` holds a
fine-grained token (`hex-publishing`) scoped to an explicit list of
repositories, created 2026-07-01. `hex-arith` was created 2026-07-31 and
`hex-mv-poly` 2026-07-30, so neither can be on that list. Every library
published since the token was made has the same problem, and the same
thing will happen at the next release unless something checks.

- `sync_released.py` now preflights every target repository against the
  token before the first push and refuses to start, listing the
  repositories to add and both the token URL and the organization
  approval URL. A dry run skips it, having no token and pushing nothing.
- The probe distinguishes the two failure shapes: a repository outside a
  fine-grained token's selection answers 404 rather than reporting
  `push: false`, because the token cannot see it at all.
- Documented in `PLAN/Releases.md` §"Publishing a new library: widen the
  token first" and in the `released.yml` header, both saying that adding
  an entry to the manifest is only half of publishing a new library.
- Three tests cover the preflight; two existing `main()` tests were
  patching everything except the new network call, so they now stub
  `writable_check` too and no longer reach api.github.com.

Scope note: the token stays scoped to the hex repositories. "All
repositories" would remove the recurrence but is not acceptable here, so
the manual step stays and the preflight is what makes it unmissable.

## Current frontier

`docs/release-token-scope`. The token widening has been requested and is
waiting on an organization owner to approve at
https://github.com/organizations/leanprover/settings/personal-access-token-requests

## Next step

Once the request is approved, re-dispatch `sync-released.yml` with
`dry_run=false`. The preflight will now say up front whether the
approval covered every repository.

## Blockers

The publish itself is still blocked on that approval. Note that the
pending run will also carry `v4.32.2` to `v4.33.0-rc1` across the
repositories that still lag; `hex-basic` is already current.
