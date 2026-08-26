# HexRoots `invFloor` agreement

## Accomplished

- Added `Dyadic.invFloor_eq_invAtPrec_of_pos`, proving that the kernel-reducible
  reciprocal used by `nkWitnessCheck` agrees with `Dyadic.invAtPrec` on every
  positive dyadic at every integer precision.
- Covered both grid-exponent cases: ordinary integer-division rounding when
  `q + k ≥ 0`, and the zero floor when `q + k < 0`.
- Verified `lake build HexRoots.Kantorovich` and the full `lake build` (9357 jobs).

## Current frontier

The computational bridge requested by issue #8731 is complete and build-green.

## Next step

Use the equality in the Mathlib companion's Newton--Kantorovich completeness
slice to reuse `invAtPrec_mul_le_one` and `one_lt_invAtPrec_add_inc_mul`.

## Blockers

None.
