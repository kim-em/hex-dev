# Cloudflare account migration documentation

## Accomplished

- Updated the cache ownership documentation to name the dedicated Hex
  Cloudflare account and destination S3 endpoint.
- Switched both public-read and S3 upload endpoints to the dedicated Hex
  account, together with a non-expiring account-owned credential restricted to
  objects in `hex-cache`.

## Current frontier

The final incremental copy followed a successful trusted main publication on
2026-08-23. Source and destination then matched at 21,509 objects and
7,416,429,539 bytes, with zero differences in the recursive comparison. The
repository variables now use account `5acf032f740d48aa656788e28cabcf2e`
and public host `pub-1ad7cebeb89e49d5afe6887b57e7956a.r2.dev`; the upload
secret was rotated in the same maintenance window. The source bucket remains
temporarily intact for acceptance only and is no longer an endpoint.

## Next step

Let this pull request's unprivileged build prove reads from the destination,
then let its trusted post-merge build prove publication with the new key. Delete
the source bucket only after both checks succeed.

## Blockers

None.
