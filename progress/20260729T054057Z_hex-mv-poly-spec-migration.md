# hex-mv-poly SPEC migration

## Accomplished

- Removed the multivariate-polynomial design entry from
  `SPEC/future-work.md` now that the library has a dedicated SPEC.
- Preserved the content and primitive-part requirement in the
  multivariate-gcd entry, where that later work belongs.
- Expanded `SPEC/Libraries/hex-mv-poly.md` into an implementation-facing
  contract for comparator laws, monomial operations, the core and
  Mathlib APIs, coefficient laws, kernel probes, conformance, benchmarks,
  file layout, and implementation order.
- Added `hex-mv-poly` and `hex-mv-poly-mathlib` to the library catalogue,
  dependency summary, DAG, and index.
- Incorporated an independent review of the mathematical API and
  repository integration. The resulting SPEC keeps Mathlib-only
  equivalences out of the computational library and assigns kernel
  elaboration measurements to a Mathlib proof-probe root.

## Current frontier

The SPEC and catalogue are ready to guide implementation. The
representation remains `Std.ExtTreeMap` unless the specified
module-boundary proof probes select the sorted-list alternative at the
recorded threshold.

## Next step

Build the exact consumer-facing API stub, compile `sos` and the two
CompPoly recursive-view consumers against it, then implement arithmetic
and the coefficient laws in the order listed by the SPEC.

## Blockers

None.
