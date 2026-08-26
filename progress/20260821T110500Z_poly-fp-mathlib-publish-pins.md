# hex-poly-fp-mathlib publish manifest entry and consumer pins

## Accomplished

- Added the `leanprover/hex-poly-fp-mathlib` entry to
  `scripts/release/released.yml`, placed after `hex-mod-arith-mathlib`
  (its last dependency) with the computed pin closure.
- Added `hex-poly-fp-mathlib` to the pins of `hex-berlekamp-mathlib` and
  `hex-berlekamp-zassenhaus-mathlib`, whose monorepo sources import
  `HexPolyFpMathlib` since the extraction in #9295; without the pin the
  next real sync would have published repos that cannot build. Also added
  it to the `leanprover/hex` aggregate pins, which must equal the
  complete split set.
- Authored `HexPolyFpMathlib/README.md` per `SPEC/readme.md`, required
  for the new manifest entry's managed-path check.
- `python3 scripts/release/check_released_manifest.py` passes: 36 split
  repositories + 1 aggregate.
- The GitHub repository `leanprover/hex-poly-fp-mathlib` exists (created
  this session, empty), along with the other six repos for the
  finite-field publishing batch.

## Current frontier

- The new repo has no Lake/CI skeleton yet, so a sync dispatched now
  fails safe at skeleton validation. Do not dispatch `sync-released.yml`
  until the skeleton lands and the `hex-publishing` token has been
  widened and approved for the new repositories.

## Next step

- Author the `leanprover/hex-poly-fp-mathlib` skeleton per
  `scripts/release/BOOTSTRAP.md`, then continue the batch: READMEs and
  manifest entries for hex-conway, hex-gfq-field, hex-gf2,
  hex-gf2-mathlib, hex-gfq, hex-gfq-mathlib, plus the phase work
  recorded in progress/2026-08-21T10-46-37Z.md.

## Blockers

- Token widening needs an organization owner's approval before any real
  sync.
