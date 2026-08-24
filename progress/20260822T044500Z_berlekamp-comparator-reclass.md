# Berlekamp FLINT comparators: paired refresh and reclassification

## Accomplished

- Refreshed the stale paired Rabin/DDF comparator measurements on
  chungus2 (CPU-0 pinned, machine idle-checked, warmed persistent
  python-flint 0.9.0 driver, steady-state medians): FLINT ahead
  10x-373x on the Rabin ladder (n = 8..64) and 44x-749x on the DDF
  ladder (n = 12..96) at f396965d. Artifacts:
  reports/bench-results/hex-berlekamp-{rabin,ddf}-compare-f396965d-chungus2.json.
- Reclassified both comparators from gating to informational in
  libraries.yml with structural-gap rationales, and added the
  mirroring External comparators section to
  HexBerlekamp/SPEC/hex-berlekamp.md. Kim authorized this
  reclassification on 2026-08-22 (session decision recorded in the
  wave plan): the parity goal was aspirational and the measured gap is
  a structural constant-factor cost of verified generic FpPoly
  arithmetic against FLINT's hand-tuned C kernels, consistent with the
  informational FLINT declarations in hex-poly, hex-bareiss, and
  hex-gf2.

## Current frontier

- With no gating comparator outstanding, HexBerlekamp Phase 4 is
  blocked only on its headline report conforming to the five-section
  shape with an empty Concerns section (wave task B5), which also
  needs a sampling-profiler trace and the distribution-coverage
  disposition.

## Next step

- B5: rewrite reports/hex-berlekamp-performance.md against the
  refreshed artifacts and bump HexBerlekamp to 4.

## Blockers

- None.
