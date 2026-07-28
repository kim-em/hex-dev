# HexRCF FLINT comparator review

## Accomplished

- Addressed the independent review's measurement findings by using one shared
  warmed fixed-benchmark config for both engines and by precomputing the full
  FLINT request line outside the timed body.
- Added build guards for every constructor in the version-1 sentence wire
  schema, made the input lookup degree-keyed, and isolated an unavailable RCF
  oracle from the driver's other comparator families.
- Rebuilt `hexrcf_bench`, rechecked all thirty oracle sentences, passed the
  focused Python tests, and verified all twenty benchmark registrations with
  python-flint 0.9.0.

## Current frontier

- The comparator implementation and review fixes are complete locally.
- No scientific timing or ratio claim has been made from this development
  machine.

## Next step

- Run the repository structural checks from the committed state, update draft
  PR #9024, and let CI validate the corrected stack.
- Carry the reviewed comparator into the release-evidence milestone.

## Blockers

- None for the comparator implementation.
- Release-quality timings still require the named benchmark host.
