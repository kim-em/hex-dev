# Release 1 integration example

## Accomplished

- Added `Examples/Release1.lean`, the integration example the Release 1
  readiness predicate names in `PLAN/Releases.md`. It builds `GF(2⁸)`
  (`Hex.GF2n` under the Rijndael modulus, using `hex-gf2`'s committed
  `GF2Poly.aes_modulus_irreducible`) and `GF(9) = F₃[x]/(x² + 1)`
  (`Hex.GFqField.FiniteField` with a hand-supplied irreducibility proof), and
  checks field identities at elaboration time with `#guard`.
- Irreducibility of `x² + 1` over `F₃` is discharged without any
  irreducibility engine: `FpPoly.size_mul_eq_add_sub_one` forces any proper
  factorization of a size-three polynomial to be a product of two linear
  factors, `FpPoly.Enumeration.polysBelowDegree 3 2` enumerates the nine
  candidates, and `decide` rules out all 81 products in the kernel. Axioms are
  the standard `propext`, `Classical.choice`, `Quot.sound`.
- Registered the module in `lakefile.lean`'s `HexReleaseExamples` glob, so
  `lake build HexReleaseExamples` (the `HEX_LIB_TARGETS` entry in `ci.yml`)
  covers it.

The import closure is deliberately narrow: the module-level closure of
`Examples.Release1` reaches only `HexBasic`, `HexArith`, `HexModArith`,
`HexPoly`, `HexPolyFp`, `HexGFqRing`, `HexGFqField`, `HexGF2`. No
`HexBerlekamp`, `HexConway`, `HexGFq`, or Mathlib, which is what makes the
release's explicit non-claim (irreducibility evidence is user-supplied)
legible in the artifact itself. That is why the example imports
`HexGFqField.Operations` rather than the `HexGFqField` umbrella: the umbrella
pulls in `HexGFqField.Example`, which depends on `HexBerlekamp`.

## Current frontier

`python3 scripts/status.py release 1` reports `exists: yes`, `builds: yes`,
and `ready: no` — the only remaining blocker is `HexBerlekamp:
done_through 4`, which is in the Release 1 *library* closure because
`libraries.yml` gives `HexGFqField.deps = [HexGFqRing, HexBerlekamp]` (from
the committed `GF(5⁴)` example field, not from the field constructor).

## Next step

Nothing further on the example. Release 1 readiness is now purely a
`HexBerlekamp` Phase 5-7 question.

## Blockers

None.
