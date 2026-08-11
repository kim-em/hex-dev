# A test module's Bounds instances leaking into emitted terms

## Accomplished

`factor_poly` on a `Polynomial ℤ` failed to elaborate inside
`HexBerlekampZassenhausMathlib/FactorPolyTests.lean`:

    Unknown constant `HexBerlekamp.FactorTacticTests.instBoundsOfNatNat_hexBerlekamp_1`
    Note: A public declaration ... exists but is imported privately

The same expression elaborates fine from a module that only imports
`HexBerlekampZassenhausMathlib`, which is what made it look like a tactic
bug. It is not. The emitted-term path is correct:
`Hex.CertificateSyntax.reifyBounds` builds `boundsOfDecide p (Eq.refl true)`
and never references an instance.

The leak is ambient instance search. `HexBerlekamp/FactorTacticTests.lean`
declared four *anonymous* `instance : ZMod64.Bounds n` inside a
`public section`. Anonymous instances get auto-generated names, they are
visible to instance search in every importing module, and elaboration picked
one up and baked that constant into the result, where the private import
makes the reference illegal.

Every other test, conformance and bench module in the repository already
uses named `private instance` (`boundsFive`, `conformanceBoundsFive`, ...);
this one file was the outlier. Naming them and marking them private matches
that convention and removes the leak.

With the leak gone, the readback example belongs in
`HexBerlekampZassenhausMathlib/FactorPolyTests.lean`, where it also pins the
`simp` attributes on `Hex.FactoredPoly.ofZ` and
`HexPolyMathlib.toPolynomial_ofCoeffs`: nothing inside the repository
exercised the short `simp` call before, which a review of #9187 called out.

Full `lake build`: 9754 jobs, green.

## Current frontier

`fix/bounds-instance-leak`.

## Next step

Two anonymous public `Bounds` instances remain in *library* modules
(`HexBerlekamp/Irreducibility.lean`, `HexConway/Table.lean`). Those are
legal to reference, so they cause no error today, but they are auto-named
and globally visible; naming them would be tidier.

## Blockers

None.
