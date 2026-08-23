# Cloudflare account migration documentation

## Accomplished

- Updated the cache ownership documentation to name the dedicated Hex
  Cloudflare account and destination S3 endpoint.
- Made the staged state explicit: the live bucket, public `r2.dev` hostname and
  GitHub variables remain unchanged until the destination copy is verified.

## Current frontier

R2 is enabled in the destination Hex account. The `hex-cache` bucket was copied
there in ENAM on 2026-08-23: all 21,508 objects and 7,416,377,295 bytes matched
the source by key, size and available checksum. Representative artifact and
revision downloads from the new `r2.dev` hostname also matched the source
byte-for-byte. Live repository variables and the upload credential still point
to the source account pending the coordinated cutover.

## Next step

Pause cache publication, make a final incremental copy, then rotate the upload
key and both endpoint variable pairs in one cutover.

## Blockers

None before the coordinated cache cutover.
