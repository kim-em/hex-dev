# hex-primality: the multiplicative order (milestone 2a)

## Accomplished

- `HexPrimality/Order.lean`: `orderOf a n` as a bounded least-search
  with junk value `0` off the `1 < n ∧ Coprime a n` domain, per the
  SPEC. Full lemma stack, Mathlib-free:
  `coprime_of_pow_mod_eq_one`, coprime cancellation, `pow_pred_mod`
  (multiplicative Fermat from hex-arith's residue form),
  `orderOf_pow_mod` / `orderOf_min`, `orderOf_pos_of_pow_eq_one`
  (least witness bounded by pigeonhole through
  `HexBasic.ListShim.nodup_subset_length_le`),
  `orderOf_dvd_of_pow_eq_one` and its converse
  `pow_eq_one_of_orderOf_dvd`, `orderOf_dvd_pred`,
  `prime_pow_dvd_orderOf` (no valuation API, per SPEC),
  `sq_roots_of_one` (Euclid via `Prime.dvd_mul`), and the general
  `orderOf_pos` (pigeonhole run in the contrapositive, avoiding
  classical extraction over dependent `getElem` binders).
- `#guard` regression block covering real orders and every junk
  branch. Module builds in well under a second.

## Current frontier

The order development is the prerequisite for Miller-Rabin (milestone
2b), the Pocklington soundness proof (milestone 3), and
hex-int-factor's primitive-root API.

## Next step

MillerRabin.lean: `oddSplit`, `mrWitnessLoop`, `millerRabin` with the
SPEC's exact branch table, `isProbablePrime`, and
`not_prime_of_millerRabin_false`.

## Blockers

Stacked on the table PR (library scaffolding only; no table content
used).
