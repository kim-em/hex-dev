# Module migration: Berlekamp (HexBerlekamp, HexBerlekampMathlib); Conway deferred

## Accomplished

Migrated `HexBerlekamp` (Basic/DistinctDegree/Factor/Irreducibility/
RabinSoundness/umbrella) and `HexBerlekampMathlib` (Basic/umbrella). Full
`lake build` and `HexConformance` green.

### Risk 1 (ZMod64.Bounds) root cause + fix

`HexBerlekamp.Irreducibility`'s `FpPoly 2`-specialized pow-chain checkers need a
`ZMod64.Bounds 2` instance. Under the pre-module import model this was supplied
by a **private** `instance : ZMod64.Bounds 2` in `HexPolyFp.SquareFree` that
leaked through typeclass resolution. The module system correctly hides private
instances, so synthesis failed (82 errors). Fix: declare a local
`instance : ZMod64.Bounds 2` in `HexBerlekamp.Irreducibility` (the checkers
legitimately need it). This is the correct fix, not a workaround — the prior
reliance on a leaked private instance was accidental.

### Exposures
`@[expose]` added to the executable defs that exported `rfl`/`unfold`/`simp`
proofs reduce through: `berlekampColumnPolys`, `basisSize`, `coeffVector`,
`vectorToPoly`, `fixedSpaceKernel(Vectors)` (Basic); `frobeniusDiffMod`,
`properDivisors`, `maximalProperDivisors`, `isUnitPolynomial`,
`rabinDividesTest`, `rabinCoprimeTest`, `rabinWitnesses`, `rabinTest`
(Irreducibility); `factorProduct`, `splitFactorAt`, `Factorization.product`
(Factor); `xPowSubX` (RabinSoundness). A handful of `leadingCoeff 0`/`coeffs`
`rfl`/`change` proofs rewritten to `simp` or `DensePoly.leadingCoeff_zero`.

## HexConway deferred

`HexConway/Basic` has ~101 errors, almost all `decide`/`rfl` kernel
computations over concrete Conway-polynomial coefficient arrays (e.g.
`#[4,1,0,0,0,1].back? ≠ some 0`). Making these reduce under the module system
requires exposing a deep slice of the executable `ZMod64`/`FpPoly`/`GFqRing`
stack — including `HexModArith`, which is `precompileModules` (the Risk-2 LCNF
hazard). Conway is a leaf (only `HexGFq` imports it, already deferred), so this
is left legacy for a dedicated follow-up. Not attempted here to avoid a large,
fragile, possibly-LCNF-blocked exposure pass.

## Deferred set (legacy), final

`HexGF2`, `HexGF2Mathlib` (Risk-2 LCNF+precompileModules); `HexGFq`,
`HexGFqMathlib` (import legacy GF2); `HexConway` (decide-heavy, above);
`HexBerlekampZassenhaus`(+Mathlib) and `HexManual` (out of scope by plan).
