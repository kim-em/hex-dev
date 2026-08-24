# hex-sparse-poly + companion: published

## Accomplished

- Both split repositories are live and fully validated:
  `leanprover/hex-sparse-poly` (skeleton + synced source; fresh-clone
  validation green for the root library, kernel tests, conformance
  sidecar with exact fixture round-trip, and the bench with all 22
  registrations verifying) and `leanprover/hex-sparse-poly-mathlib`
  (Mathlib entirely from cache, lint tests, correspondence
  conformance).
- Publication surfaced and fixed three infrastructure gaps:
  - the token router probed `GET /repos`, which any fine-grained token
    answers for a public repository, so repositories carried only by
    the second publishing token failed at push time; the preflight now
    probes the smart-HTTP receive-pack advertisement (#9522);
  - the sympy oracle broke under python-flint ground types
    (`Fraction(fmpz, fmpz)`); fixed on the conformance branch before
    merge;
  - the bench sidecar needs `HexModArith` and `HexPolyFp` requires the
    monorepo build could not miss (everything builds together there);
    pinned via a new `bench_pins` manifest field symmetric to
    `conformance_pins` (#9543), with the skeleton-only released-repo
    commit reconciled into the `release-sync-baseline` branch.
- The stale-mirror backlog from the v4.34.0-rc2 toolchain bump was
  staged-synced for the dependency closure (hex-basic, hex-test-kit,
  hex-arith, hex-poly, hex-mod-arith, hex-poly-fp, hex-poly-mathlib),
  then the sparse pair re-pinned against it.

## Current frontier

The `leanprover/hex` aggregate does not yet require the sparse pair:
adding it is a hand-edit to the aggregate's un-managed lakefile and
umbrella plus a `lake update`, but a coherent aggregate manifest wants
every mirror on the new toolchain, and a full no-`only` sync fails at
`leanprover/hex-char-poly` (manifest entry present, phases recorded at
0, no skeleton; see issue 9523).

## Next step

Resolve char-poly (author its skeletons and record its phases, or
withdraw its manifest entries), run a full dry-run + real sync, then
add the sparse pair to the aggregate lakefile/umbrella and dispatch
`only=hex`.

## Blockers

The char-poly decision (issue 9523).
