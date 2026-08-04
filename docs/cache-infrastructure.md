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

The account holds other buckets unrelated to this project. Only `hex-cache` is ours.

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

## The read host, and why it is `r2.dev`

Reads go through `pub-*.r2.dev`, Cloudflare's public bucket URL. This is a deliberate choice: it
needs no domain name, and this repository's CI volume is low enough that its rate limit is not a
practical concern.

The limit is real, so it is worth knowing the shape of it. `lake cache get` continues past failed
downloads, so a throttled fetch can leave the local cache holding input-to-output mappings whose
artifact blobs never arrived, and `ci.yml` discards its exit status:

```
lake cache get --service hex-public --repo kim-em/hex-dev \
  || echo "::warning::lake cache miss for this revision; building from source"
```

The consequence here is mild. `ci.yml` builds with plain `lake build`, so an unresolvable cache
entry makes Lake log a warning and rebuild the module from source, and the build stays green. The
cost is a redundant rebuild, not red CI.

That holds only because no `--fail-level` is raised. Adding `--iofail` or `--wfail` would turn each
such warning into a build failure, via https://github.com/leanprover/lean4/issues/14670. Raising the
fail level and staying on `r2.dev` do not combine well; wanting both means putting an R2 custom
domain in front of `hex-cache` first, which needs a zone in this same Cloudflare account.

## Cost

Egress from R2 is free. Reads are Class B operations: 10M per month free, then $0.36 per million.

## Related

- https://github.com/leanprover/lean4/issues/14670, open: Lake fails a build over a cache miss it
  has already recovered from. Only bites under `--iofail` or `--wfail`.
- https://github.com/leanprover/lean4/pull/14651, merged: `lake cache get` could log download
  failures and still exit 0, so its exit status is untrustworthy before v4.34.0.
