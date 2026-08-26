# hex-sparse-poly: Phase 4 benchmarking

## Accomplished

- `bench/HexSparsePoly/Bench.lean` (`lean_exe hexsparsepoly_bench`)
  with all six SPEC input families: 22 registrations, every one
  returning *consistent with declared complexity* at scientific
  settings, including the two required internal checks (degree
  independence of `add`/`mul` on the sparse families; `substPow` flat
  in `k` at β = −0.001).
- The sparse-multiplication selection: three candidates
  (sort-and-combine, `ExtTreeMap` accumulation, Johnson heap merge)
  benched on genuinely low- and high-collision inputs with both
  compare groups reporting `allAgreed`. The **tree accumulation wins
  both shapes by ≈3×**; the heap loses on constants as the SPEC
  predicted. One measurement bug found and fixed along the way: the
  evenly-spread "low collision" generator actually collided (equal
  steps make pairwise sums coincide) — replaced by scattered
  pseudo-random exponents, after which every selection ladder fits its
  model to β ≤ 0.06.
- Crossover numbers (add `t ≈ n/8`, mul `t ≈ n/4`, eval parity
  extrapolating to `t ≈ n/6`) and the convert-gcd conversion share
  (≈5%) measured and written back into the SPEC as it requires,
  together with the CommRing placement note for the transported laws.
- Six samply profiles (one per input family), all passing the filter's
  calibration/retention/sensitivity checks, categorised and narrated in
  `reports/hex-sparse-poly-performance.md` (five subsections, empty
  Concerns). SymPy informational ratio measured (Lean ≈2.6× faster on
  the shared mul rung; parity on add); python-flint recorded as
  scheduled-only per its informational classification.
- CI smoke wiring (`hexsparsepoly_bench` in the exe-targets list and
  the bench-verify budget step). `done_through: 4`.

## Current frontier

The selected `@[csimp]` multiplication twin (tree accumulation with
`addCoeff` steps) is not yet in the library: its value-equality proof
is the next substantial piece, scheduled with the Phase-5 sorry
closure.

## Next step

Phase 5: the tree `mulImpl` with its proved `@[csimp]` equality, the
compose agreement pack, `coeff_substScale`, and the `divExactMonic?`
iff lemmas; then `done_through: 5`.

## Blockers

None.
