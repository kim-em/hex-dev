# hex-primality: cap the rho inner budget

## Accomplished

- `rhoInnerFuel` is now `min (16 * (sqrt (sqrt n) + 2)) (1 <<< 22)`.
  Uncapped, one Brent restart at 256+ bits had an effectively
  unbounded iteration budget, so a search whose smallest factor was
  out of reach hung inside the first restart instead of returning
  `RhoStop.exhausted`. The cap binds only past `n ≈ 2^72` and still
  covers factors to about `2^44`, beyond rho's documented `~10^12`
  remit. Docstrings on `rhoInnerFuel` and `rhoFactor?` updated;
  `rhoFactor?_spec` and every downstream proof are fuel-agnostic, so
  no proof changed.
- Measured with a scratch driver (not committed): a semiprime with
  two ~`2^35` factors still splits in 182 ms; a semiprime with two
  ~`2^60` factors now returns a clean `exhausted` after 4 restarts in
  9.3 s (~2.3 s per capped restart) where it previously never
  returned.
- The `#guard` regressions in `Search.lean` use inputs far below the
  cap threshold and replay unchanged; full graph rebuilt green.

## Current frontier

Exhaustion at `defaultPrimeFuel` for a 320-bit input is now bounded
(~minutes at seconds per restart) rather than infinite. If that is
still too slow for the tactic's interactive use, the next knob is a
smaller cap or a total (restart × iteration) budget, which is a bench
question.

## Next step

None for this patch; the search-hook SPEC route (`primeCert?With`)
is where a smarter factorization would land.

## Blockers

None.
