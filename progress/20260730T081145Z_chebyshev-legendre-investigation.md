# Chebyshev and Legendre factorization performance investigation

## Accomplished

- Compared the current merged Hex factor-sweep rows against Isabelle BZ for
  every Chebyshev and Legendre case.
- Attributed representative costs to modular prime selection, Hensel lifting,
  recursive sub-floor probing, and exhaustive recombination.
- Measured the existing original-coordinate (`M1`) lift on the same selected
  primes and modular factors. It reduces the required lift precision and lift
  time by roughly an order of magnitude on the high-degree non-monic rows.
- Costed an unverified original-coordinate classical recombination prototype
  and checked that its returned factors multiply to the input on the sampled
  Chebyshev and Legendre rows.
- Confirmed that Isabelle's verified BZ implementation lifts the original
  polynomial and uses a modular-factor-degree-aware bound, rather than lifting
  Hex's coefficient-swollen `toMonic` dilation.

## Current frontier

The leading candidate is a verified original-coordinate classical path using
`coreLiftData`/`monicTarget` and the M1 recovery infrastructure already present
in `HexBerlekampZassenhausMathlib/M1Recovery.lean`. After that change, modular
prime selection becomes the dominant Legendre cost.

## Next step

Implement and prove a core-coordinate analogue of the smart classical
recombination path, retain the current adaptive prime choice, and benchmark the
full factor sweep. Then add a degree-aware Mignotte bound and optimize the
modular factorization kernel if the projected gains survive integration.

## Blockers

None. The runtime primitives and much of the Mathlib-side M1 correspondence
infrastructure already exist; the missing work is the classical search
integration and its coverage proof.
