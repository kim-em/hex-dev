# Lake artifact cache infrastructure

Where the build cache lives, who owns it, and which knob feeds which workflow.

## Cloudflare account

| | |
|---|---|
| Account | `kim@lean-fro.org` |
| Account ID | `d789bf36d237e0cb313be59b927c82bd` |
| Dashboard | https://dash.cloudflare.com/d789bf36d237e0cb313be59b927c82bd |
| R2 bucket | `hex-cache` |

The account ID is not a secret: it is the subdomain of the S3 endpoint below. If the dashboard
link 404s, the login you used is not a member of that account.

This is the **same Cloudflare account** used by `TauCetiProject/TauCeti`, which has its own bucket,
`tauceti-cache`. The two share nothing but the account.

## Endpoints

Reads are anonymous. Lake's download path issues plain unauthenticated `curl` GETs and has no way
to sign them, so the read host must be public; only uploads use a key.

| Purpose | Value | Used by |
|---|---|---|
| `LAKE_CACHE_ARTIFACT_ENDPOINT_PUBLIC` | `https://pub-b2d516317e7041aebd324550ac6cd1fa.r2.dev/artifacts` | `ci.yml` read |
| `LAKE_CACHE_REVISION_ENDPOINT_PUBLIC` | `https://pub-b2d516317e7041aebd324550ac6cd1fa.r2.dev/revisions` | `ci.yml` read |
| `LAKE_CACHE_ARTIFACT_ENDPOINT` | `https://d789bf36….r2.cloudflarestorage.com/hex-cache/artifacts` | `ci.yml` upload |
| `LAKE_CACHE_REVISION_ENDPOINT` | `https://d789bf36….r2.cloudflarestorage.com/hex-cache/revisions` | `ci.yml` upload |
| `LAKE_CACHE_KEY` (secret) | `<ACCESS_KEY_ID>:<SECRET>`, read-write | `ci.yml` upload only |

Lake service names: `hex-public` for reads, `hex-r2` for uploads.

## Known exposure: the read host is rate-limited

The read path is still on `pub-*.r2.dev`, which Cloudflare documents as rate-limited and "should
only be used for development purposes". `lake cache get` continues past failed downloads, so a
throttled fetch leaves the local cache holding input-to-output mappings whose artifact blobs never
arrived, and `ci.yml` discards its exit status:

```
lake cache get --service hex-public --repo kim-em/hex-dev \
  || echo "::warning::lake cache miss for this revision; building from source"
```

For this repository the consequence is mild. `ci.yml` builds with plain `lake build`, so an
unresolvable cache entry makes Lake log a warning and rebuild the module from source, and the build
stays green. The cost is redundant rebuilds, not red CI.

That is only true because no `--fail-level` is raised. Adding `--iofail` or `--wfail` would turn
each of those warnings into a build failure, via
https://github.com/leanprover/lean4/issues/14670. TauCeti hit exactly that: 28 of 40 consecutive
build failures had no Lean error at all.

If CI volume grows, or a stricter fail level is ever wanted, the fix is the one TauCeti took: put an
R2 custom domain in front of `hex-cache` and repoint the two `*_PUBLIC` variables. That requires a
zone in this same Cloudflare account. `taucetiproject.org` already sits there, though a name of its
own would read better for this project.

## Cost

Egress from R2 is free. Reads are Class B operations: 10M per month free, then $0.36 per million.

## Related

- https://github.com/leanprover/lean4/issues/14670, open: Lake fails a build over a cache miss it
  has already recovered from. Only bites under `--iofail` or `--wfail`.
- https://github.com/leanprover/lean4/pull/14651, merged: `lake cache get` could log download
  failures and still exit 0, so its exit status is untrustworthy before v4.34.0.
