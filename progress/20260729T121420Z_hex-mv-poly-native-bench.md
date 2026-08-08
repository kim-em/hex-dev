# HexMvPoly native benchmark slice

## Accomplished

- Added the Mathlib-free `hexmvpoly_bench` executable and registered it in the
  existing single-job CI build and sequential bench verification gate.
- Added deterministic LeanBench families for sparse addition, low- and
  high-collision multiplication, cancellation-heavy `Int`/`Rat` arithmetic,
  collision-heavy structural maps, and sum-of-squares-shaped arithmetic.
- Registered each separable phase independently: three addition orders, two
  multiplication collision regimes, two coefficient domains, and the three
  structural operations are distinct timed targets.
- Hoisted input construction out of timed regions and made every target return a
  structural checksum of the canonical result.
- Added bounded genuine-fraction coefficients, typed axis indices, and
  duplicate-free corpus guards so comparator inputs exercise rational
  normalization without silently collapsing their supports.
- Made the SOS monomial mixer preserve a genuinely quadratic output support;
  a content guard fixes the three-square result at `3n(n+1)/2` terms.
- Verified all eleven registrations, the Mathlib-free import boundary, the
  repository source lints, and the CI smoke wall-clock budget.
- Ran the scientific ladders. All eleven targets are consistent with their
  declared models; the multiplication-high and sum-of-squares ladders extend
  through 512 so their logarithmic tree factor is visible above narrow-range
  noise. Focused reruns measured an executable-spawn floor near 22 ms, below
  the approximately 200 ms autotuned in-process batches.
- Extracted `HexMvPolyBench.Corpus`, a LeanBench-free shared term generator for
  the later CompPoly and Mathlib `MvSparsePoly` adapters.

## Current frontier

The native ExtTreeMap workload families are implemented and locally green. All
eleven attribution-isolated scientific ladders are consistent with their
declared textbook models.

## Next step

Publish this slice after the conformance slice. Build the CompPoly and Mathlib
`MvSparsePoly` comparator drivers once the Mathlib companion is available so
all three implementations can consume the same deterministic corpus.

## Blockers

The comparator report, plots, and profiles depend on the not-yet-implemented
Mathlib companion and comparator adapters. They are later Phase 4 work, not part
of this native registration slice.
