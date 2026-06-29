# Certified LLL dispatch plan review

## Accomplished

Reviewed the proposed certified invisible-dispatch LLL plan against the current
LLL theorem surface, executable `lll` wrapper, `isLLLReduced`, the
noncomputable conformance checker, integer Gram-Schmidt `Data`, existing extern
policy, and Lake extern-library wiring.

## Current frontier

The plan is plausible at the property level but needs tighter acceptance
criteria around the opaque extern hook, dynamic symbol lookup, candidate
validation contract, and the exact link between the integer checker and the
short-vector theorem hypotheses.

## Next step

If the plan moves forward, strengthen Part A and D4 before filing worker
directives: specify the extern hook as an IO/world-tokened or explicitly
runtime-only candidate source, require ABI/version/shape validation for the FFI
symbol, and make `certCheck_sound` the single theorem D4 is allowed to trust.

## Blockers

None for this review turn.
