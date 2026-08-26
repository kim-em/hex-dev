**Accomplished**

Investigated the M1 `hvalid` obligation for the honest scaled factor
`scale (leadingCoeff q) fac`. Located the executable definition of
`Hex.ZPoly.defaultFactorCoeffBound` in `HexPolyZ/Mignotte.lean` and checked the
Mathlib bridge in `HexBerlekampZassenhausMathlib/Basic.lean` and
`HexPolyZMathlib/Mignotte.lean`.

Confirmed that the existing proved theorem `defaultFactorCoeffBound_valid`
only bounds bare integer divisors `g | f`, and found no existing lemma that
directly bounds `leadingCoeff cofactor * factor` by `defaultFactorCoeffBound`.

**Current frontier**

The numeric Mignotte formula used by `defaultFactorCoeffBound` should be strong
enough for the leading-coefficient-scaled factor, but the repo currently lacks
the stronger theorem exposing that fact.

**Next step**

Add a Mathlib-side scaled Mignotte theorem, then transport it to a Hex-facing
lemma of the shape:
`∀ i, ((Hex.DensePoly.scale (Hex.DensePoly.leadingCoeff q) fac).coeff i).natAbs
≤ Hex.ZPoly.defaultFactorCoeffBound core` under `core = fac * q` and
`core ≠ 0`.

**Blockers**

None for the investigation. The implementation work needs the stronger Mahler
measure step `|leadingCoeff q| ≤ M(q)` rather than the existing bare-divisor
step `1 ≤ M(q)`.
