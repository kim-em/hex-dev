# Cloudflare documentation closeout

## Accomplished

- Reconciled the durable cache documentation with the completed account
  migration. `hex-cache`, both endpoint pairs, and the least-privilege
  publisher credential are in the dedicated `hex` account; the personal-account
  source bucket has been deleted.
- Documented the publisher credential's ownership, scope, GitHub secret format,
  and safe rotation sequence without recording any credential value or local
  recovery location.
- Closed out the acceptance work left by the earlier migration and cache-cleanup
  sessions. PRs #9440 and #9441 moved and verified the R2 cache. PR #9491 then
  made GitHub's dependency-scoped cache primary and R2 the fallback: main run
  `32696632216` restored and republished 1,205 R2 artifacts and saved the first
  trusted GitHub snapshot; Pages run `32696632192` deployed successfully. Later
  CI run `32725120481` and Pages run `32725881966` both restored a compatible
  GitHub snapshot, with CI correctly skipping the R2 fallback.

## Current frontier

The account migration and cache-policy acceptance are complete. The durable
documentation now describes the live account, endpoints, credential boundary,
and two-level restore path.

## Next step

Continue observing GitHub cache eviction and R2 usage under normal traffic. If
the `hex` account later owns a suitable Cloudflare zone, replace both public
`r2.dev` endpoint variables together with an R2 custom domain and exercise an
anonymous restore before disabling the development endpoint.

## Blockers

The custom-domain improvement requires a zone in the `hex` account. It does not
block the current GitHub-primary, R2-fallback cache path.
