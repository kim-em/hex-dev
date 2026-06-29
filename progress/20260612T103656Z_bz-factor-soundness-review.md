# Progress: BZ factor soundness review

## Accomplished

Reviewed `HexBerlekampZassenhaus/Basic.lean` and
`SPEC/Libraries/hex-berlekamp-zassenhaus.md` for the reported non-monic cubic
counterexample `DensePoly.ofCoeffs #[3,10,9,2]`.

Confirmed from the spec that public `factor` is intended to return irreducible
primitive polynomial factors for arbitrary non-monic inputs, not merely a
product-preserving singleton. Inspected the executable dispatch and found two
relevant unsound singleton paths: the fast-path modular singleton branch in
`factorFastFactorsWithBound`, and the modular exhaustive wrapper
`exhaustiveCoreFactorsWithBound` returning `#[core]` when recombination returns
empty.

Located the normalization mismatch: lift data is built from `(toMonic core).monic`,
but both BHKS and scaled exhaustive recombination verify candidates against the
original non-monic core while reconstructing candidates by scalar multiplication
with `leadingCoeff core`.

## Current frontier

No source fix was attempted in this turn. A stdin `lake env lean` exploratory
check confirmed the trial path factors the cubic as three linears, but modular
calls through the interpreter hit the expected ZMod64 native implementation
linking limitation, so the linked-module evidence supplied by the user remains
the executable confirmation for the modular/fast result.

## Next step

Patch the pipeline so non-monic cores are normalized consistently: either run
recombination on the monic transform and map recovered factors back through a
proper inverse `toMonic` factor transform, or route non-monic cores to a correct
fallback until that transform is implemented. Add the cubic as a regression
fixture asserting `factor`, `factorFastFactorsWithBound`, and
`factorSlowModularFactorsWithBound` do not accept `#[core]` unless certified
irreducible.

## Blockers

None for diagnosis. The proof surface around `factor_irreducible_of_nonUnit`
cannot be closed honestly while the executable can emit this reducible singleton.
