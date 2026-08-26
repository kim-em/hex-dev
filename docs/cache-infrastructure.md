# Lake artifact cache infrastructure

Where the build cache lives, who owns it, and which knob feeds which workflow.

## Cloudflare account

This table records the required destination. During the 2026 account migration,
the live cache and repository variables remain on the older personal account
until the destination copy has passed verification and both the upload and
newly allocated `r2.dev` endpoints are changed together.

| | |
|---|---|
| Account | `hex` (accessible to `kim@lean-fro.org`) |
| Account ID | `5acf032f740d48aa656788e28cabcf2e` |
| Dashboard | https://dash.cloudflare.com/5acf032f740d48aa656788e28cabcf2e |
| R2 bucket | `hex-cache` |

The account ID is not a secret: it is the subdomain of the S3 endpoint below. If the dashboard
link 404s, the login you used is not a member of that account.

This account is the Hex boundary. It should contain no TauCeti or Palomar resources.

## Endpoints

Reads are anonymous. Lake's download path issues plain unauthenticated `curl` GETs and has no way
to sign them, so the read host must be public; only uploads use a key.

| Purpose | Value | Used by |
|---|---|---|
| `LAKE_CACHE_ARTIFACT_ENDPOINT_PUBLIC` | `https://pub-1ad7cebeb89e49d5afe6887b57e7956a.r2.dev/artifacts` | `ci.yml` read |
| `LAKE_CACHE_REVISION_ENDPOINT_PUBLIC` | `https://pub-1ad7cebeb89e49d5afe6887b57e7956a.r2.dev/revisions` | `ci.yml` read |
| `LAKE_CACHE_ARTIFACT_ENDPOINT` | `https://5acf032f740d48aa656788e28cabcf2e.r2.cloudflarestorage.com/hex-cache/artifacts` | `ci.yml` upload |
| `LAKE_CACHE_REVISION_ENDPOINT` | `https://5acf032f740d48aa656788e28cabcf2e.r2.cloudflarestorage.com/hex-cache/revisions` | `ci.yml` upload |
| `LAKE_CACHE_KEY` (secret) | `<ACCESS_KEY_ID>:<SECRET>`, read-write | `ci.yml` upload only |

Lake service names: `hex-public` for reads, `hex-r2` for uploads.

## Read path and the interim `r2.dev` host

GitHub Actions cache is the primary CI read path. Its key is scoped by runner platform, Lean
toolchain, and Lake manifest; pull requests restore the latest compatible snapshot saved by a
fully verified `main` build. The workflow calls the public Lake/R2 cache only when that restore has
no match. This avoids both redundant R2 requests and per-PR GitHub cache snapshots that cannot be
shared with other pull requests.

Fallback reads currently go through `pub-*.r2.dev`, Cloudflare's public bucket URL. Cloudflare
documents `r2.dev` as a non-production development endpoint with variable rate limiting and
recommends a custom domain for production traffic. It remains useful here as a reduced-volume
fallback because it needs no domain name, but it is not the desired permanent serving model.

The limit is real, so it is worth knowing the shape of it. `lake cache get` continues past failed
downloads, so a throttled fetch can leave the local cache holding input-to-output mappings whose
artifact blobs never arrived, and `ci.yml` discards its exit status:

```
lake cache get --max-revs=20 --service hex-public --repo kim-em/hex-dev \
  || echo "::warning::lake cache miss for this revision; building from source"
```

The 20-revision window bounds serial public-cache requests while still reaching
the recently published base of an ordinary pull-request merge commit. A
HEAD-only lookup cannot work: pull-request merge SHAs are never published, and
a main SHA is published only after the current run completes.

The consequence here is mild. `ci.yml` builds with plain `lake build`, so an unresolvable cache
entry makes Lake log a warning and rebuild the module from source, and the build stays green. The
cost is a redundant rebuild, not red CI.

That holds only because no `--fail-level` is raised. Adding `--iofail` or `--wfail` would turn each
such warning into a build failure, via https://github.com/leanprover/lean4/issues/14670. Raising the
fail level and staying on `r2.dev` do not combine well. The durable fix is an R2 custom domain,
which first requires a Cloudflare zone in the `hex` account; the account currently has none. Once
one is available, replace both public repository variables together and exercise an anonymous
restore before removing the `r2.dev` URL.

## Cost

Egress from R2 is free. Reads are Class B operations: 10M per month free, then $0.36 per million.

## Related

- https://github.com/leanprover/lean4/issues/14670, open: Lake fails a build over a cache miss it
  has already recovered from. Only bites under `--iofail` or `--wfail`.
- https://github.com/leanprover/lean4/pull/14651, merged: `lake cache get` could log download
  failures and still exit 0, so its exit status is untrustworthy before v4.34.0.
