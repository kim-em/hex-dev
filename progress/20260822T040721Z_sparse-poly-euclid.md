# hex-sparse-poly: Euclidean layer through the conversions (milestone 5a)

## Accomplished

- `HexSparsePoly/Euclid.lean`: `divModMonic`, `divMod`, `gcd`, and
  `divExactMonic?` defined by conversion through `DensePoly` exactly as
  the SPEC authorises, the `Div`/`Mod` instances, and `divMonomial?` as
  the one division that stays sparse (with `mulMonomial_divMonomial`
  proved).
- Transported law packages: `divMod_spec`, `divMod_degree_lt`,
  `divModMonic_spec` (deliberately under `[Div S]` + `[DivModLaws S]`),
  `gcd_dvd_left`, `gcd_dvd_right`, `dvd_gcd`, with the
  `dvd_of_toDense_dvd` / `toDense_dvd` transports and
  `degree?_ofDense`.
- A `Decidable Monic` instance so `by decide` discharges monicity
  side conditions.
- `libraries.yml`: `HexSparsePoly.done_through: 1` — every SPEC
  declaration is now implemented with its intended-final body (the
  `mul` `@[csimp]` twin is the SPEC-sanctioned Phase-4 deferral).

## Current frontier

Eight sorried proofs remain, all theorem-level (Phase-1-legal):
the compose agreement pack and `coeff_substScale` in `Eval.lean`, and
the two `divExactMonic?` iff lemmas here (their reverse directions need
the dense uniqueness of monic division,
`DensePoly.divMod_eq_of_reconstruction`).

## Next step

Phase 2: an independent (non-author) scaffolding review against the
SPEC, then the `status/hex-sparse-poly.scaffolding-reviewed` token and
`done_through: 2`.

## Blockers

None.
