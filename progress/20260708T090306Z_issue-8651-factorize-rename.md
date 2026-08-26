# Rename `factor` → `ZPoly.factorize`, add `ZPoly.factors` (#8651)

## Accomplished
Renamed the Berlekamp-Zassenhaus integer entry point `Hex.factor` to
`Hex.ZPoly.factorize` (in the `ZPoly` namespace, so `f.factorize`
dot-notation works) and added the convenience accessor
`Hex.ZPoly.factors f := (f.factorize).factors` returning the irreducible
factors with multiplicities (`f.factors`).

- `def factor` → `def ZPoly.factorize` in `FactorEntryPoints.lean`; added
  `def ZPoly.factors`.
- Renamed the 32 associated `factor_*` theorems → `factorize_*` across
  `HexBerlekampZassenhaus/`, `HexBerlekampZassenhausMathlib/`, and the two
  SPECs. These are disjoint from the unrelated mod-p `factor_*` names
  (`factor_ne_zero_of_ne_zero`, `factor_degree_lt*`), which were left alone.
- Fixed every bare `factor` def-reference (compiler-driven) → `ZPoly.factorize`,
  including the capstone `FactorSoundness.lean`/`PublicSurface.lean`
  (`Hex.factor` → `Hex.ZPoly.factorize`). Bound variables named `factor`
  (e.g. `fun factor => …`, `{factor g : ZPoly}`) were preserved.
- Updated SPEC `hex-berlekamp-zassenhaus.md` (signature block + prose), the
  `#guard` examples, the conformance drivers, bench drivers/service, and the
  manual Coppersmith tutorial (now iterates `gz.factors` via the new accessor).

Note on dot-notation: `ZPoly` is `abbrev ZPoly := DensePoly Int`. Field
notation `x.factorize` resolves to `ZPoly.factorize` only when `x`'s declared
type is the abbrev `ZPoly`; on a value typed directly as `DensePoly Int`
(e.g. `DensePoly.ofCoeffs g`) it resolves to `DensePoly.*`. The manual
therefore binds `let gz : ZPoly := DensePoly.ofCoeffs g` before `gz.factors`.

The conformance/bench protocol string `"factor"` (CLI `--entry` name, oracle
key) was intentionally kept — it is an interface name, not the Lean symbol —
so no fixtures need regenerating.

## Current frontier
`lake build` green for `HexBerlekampZassenhaus`,
`HexBerlekampZassenhausMathlib`, `HexConformance`, and the BZ bench/service
exes: 0 errors, 0 sorries.

## Next step
Second opinion, then PR.

## Blockers
None for this rename. Pre-existing, unrelated: `HexManual` does not build
because `HexLLL.lean`/`Coppersmith.lean` reference `lllReducedInt`, renamed to
`lllReduced` by #4655/#8658 without updating the manual (present on `main`, in
files this PR does not touch). All factor-related manual code is correct.
`HexManual` is not in the CI merge-gating target set (only the pages deploy).
