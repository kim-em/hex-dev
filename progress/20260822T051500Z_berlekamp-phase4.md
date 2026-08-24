# HexBerlekamp Phase 4: report refresh and bump to 4

## Accomplished

- Re-ran the four parametric verdict ladders at f396965d on chungus2
  (CPU-0 pinned, idle-checked): all four consistent with declared
  complexity. Export hex-berlekamp-f396965d-chungus2.json.
- Captured sampling profiles (samply 0.13.1, ~999 Hz, timed-region
  filtered) for one representative rung of each declared input family
  and committed the leaf-cost categorisation
  (berlekamp-leafcost-f396965d-chungus2.txt): boxed closure dispatch,
  refcounting, and allocator traffic take 55-66% of wall time with the
  remainder in the DensePoly kernels, matching the declared cost
  models and explaining the structural FLINT gap.
- Rewrote reports/hex-berlekamp-performance.md into the five mandated
  sections with full artifact traceability. The three prior Concerns
  are resolved substantively: the comparator gap is now a measured
  informational ratio (reclassification authorized 2026-08-22, see
  progress/20260822T044500Z_berlekamp-comparator-reclass.md), the
  profile is now a sampling-profiler trace covering every input
  family, and the report states the declared input_families as the
  coverage contract in Bench Targets.
- Bumped HexBerlekamp done_through 3 -> 4; check_phase4 validates the
  report's comparator strings and family names.

## Current frontier

- HexBerlekampZassenhaus 0 -> 4 (wave task B6) is now unblocked on the
  Berlekamp edge; its own headline-report rewrite is next.

## Next step

- B6: rewrite reports/hex-berlekamp-zassenhaus-performance.md into the
  five-section shape and bump BZ.

## Blockers

- None.
