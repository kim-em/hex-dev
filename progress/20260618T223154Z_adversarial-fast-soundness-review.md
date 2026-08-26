# Progress - adversarial fast-soundness review

## Accomplished

Reviewed the proposed separation-free end-to-end plan against the current
Lean sources. Checked the latest progress note, the fast-core irreducibility
wrappers in `HexBerlekampZassenhausMathlib/PartitionRefinement.lean`, the
recovery packages in `HexBerlekampZassenhausMathlib/Recovery.lean`, the UFD
count lemmas in `HexBerlekampZassenhausMathlib/Basic.lean`, and the public
contract surface in `HexBerlekampZassenhausMathlib/FactorSoundness.lean`.

Found that the plan as stated does not match `main`: the available fast-core
irreducibility route still needs `ExpectedTrueFactors` for the actual emitted
array, and the canonical-indicator recovery package currently requires
`L' = W`, not merely `W <= L'`. Also found that the current `count_ge` lemma is
not a cut-derived lower bound; it consumes emitted-factor irreducibility.

## Current frontier

The proposed separation-free correctness path is not closed on current APIs.
The hard dependency is the identification of executable recovered indicators
and emitted factors with the true-support/canonical expected factors. That
identification is currently supplied through the `L' = W` recovery machinery.

## Next step

Either reintroduce separation on the fast-core correctness path, or design a
new soundness theorem for arbitrary successful recovered indicators that proves
each emitted factor is irreducible without first identifying the recovered
partition with true supports. The latter would need a genuinely new argument,
not the existing `ExpectedTrueFactors`/count wrapper.

## Blockers

No tooling blocker. The blocker is mathematical/API-level: current Lean
statements do not provide the advertised cut-only `of_cut` fast soundness
theorem.
