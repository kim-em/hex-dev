# Cloudflare account migration documentation

## Accomplished

- Updated the cache ownership documentation to name the dedicated Hex
  Cloudflare account and destination S3 endpoint.
- Made the staged state explicit: the live bucket, public `r2.dev` hostname and
  GitHub variables remain unchanged until the destination copy is verified.

## Current frontier

The destination Hex account exists and Wrangler can select it, but R2 has not
yet been enabled there. Cloudflare returns API error 10042, so the destination
bucket and its public hostname do not exist yet.

## Next step

Enable R2 in the Hex dashboard, copy and verify `hex-cache`, then rotate the
upload key and both endpoint variable pairs in one cutover.

## Blockers

R2 checkout must be completed once in the Hex Cloudflare dashboard.
