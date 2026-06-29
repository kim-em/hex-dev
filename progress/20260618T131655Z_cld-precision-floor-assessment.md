# Progress — CLD precision floor assessment

## Accomplished

Reviewed the proposed soundness/precision diagnosis for the fast BHKS/van Hoeij
path. Checked the current progress note, the executable fast recovery gate in
`HexBerlekampZassenhaus/Basic.lean`, the project BHKS spec, and the BHKS paper
text around Lemmas 3.3/3.4 and the CLD lattice setup.

Attempted to run the configured Claude second-opinion workflow, but it failed
with a transport-level `ConnectionRefused` error before returning substantive
output.

## Current frontier

The diagnosis looks correct for the existing proof route: product verification
certifies exact factor multiplication/reconstruction, not the CLD coefficient
separation hypothesis needed to place true-factor indicators in the projected
short-vector lattice. An acceptance floor `p^k >= 2 * max_j B_j + 1` is a
conservative local fix for deriving that hypothesis from a successful fast-core
return.

## Next step

If implementing the fix, add the floor as an acceptance predicate in the fixed
precision recovery loop and expose a success lemma that returns the per-column
`2 * bhksCoeffBound f j < p^k` hypothesis. Keep the existing larger BHKS
separation cap/slow fallback logic separate.

## Blockers

No code blocker found. External Claude review was unavailable due to transport
failure.
