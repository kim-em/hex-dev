# hex-primality: SPEC routes for downstream factoring uptake

## Accomplished

- `HexPrimality/SPEC/hex-primality.md`: new subsection "Taking up
  downstream factoring advances" fixing the three routes by which
  hex-int-factor's stronger factorization reaches this library's
  search without inverting the proof dependency: (1) certificate
  hand-off through `checkPrime` on externally built `PrimeCert` data,
  works today; (2) Pollard `p − 1` stage 1 sited here beside
  `rhoFactor?` under the same validated proper-factor contract when
  hex-int-factor lands, ECM staying downstream; (3) a deferred
  `primeCert?With` search parameter plus the elaboration-time
  provider-registration hook (the `Hex.FactorTactic.Provider`
  pattern) for the tactic. The rho/`p − 1`/ECM sentence and the
  "move rho to hex-arith" open question updated to match.
- `SPEC/Libraries/hex-int-factor.md` mirrored: dependency-direction
  paragraph points at the new subsection; scope and milestone 4 name
  the shared `p − 1` stage-1 primitive as sited upstream; route 2
  opens with the siting note; `PMinusOne.lean` becomes an adapter in
  the file layout.

## Current frontier

SPEC-only change; no code moved. `p − 1` stage 1 and `primeCert?With`
are specified as future work keyed to hex-int-factor's arrival.

## Next step

A manual chapter for hex-primality (separate branch,
`primality-manual`).

## Blockers

None.
