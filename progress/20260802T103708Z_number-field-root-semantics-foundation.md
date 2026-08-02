# Number-field root-semantics foundation

## Accomplished

- Read the Resultant, NumberField, and NumberFieldTower specifications and their Mathlib companions to identify the next dependency-ordered stage.
- Proved lazy algebraic-root comparison sound and total.
- Proved fixed-field coefficient conversion, exact Horner evaluation, certified ball Horner evaluation, and duplicate merging are sound or total as appropriate.
- Connected fixed-field dense-polynomial coefficients, zero detection, and degree to the selected complex embedding.
- Proved the fixed-field and algebraic root drivers return positive multiplicities.
- Reduced `HexNumberFieldMathlib/Roots.lean` from 21 to 14 public `sorry` obligations without adding axioms or new sorries.
- Verified the focused target, the NumberField Mathlib/manual/conformance/fixture/bench targets, and the full repository build.
- Repaired the factor-sweep freshness gate so source-identical measurements survive the repository's required squash-merge workflow; this unblocks the already-failing `main` CI introduced by PR #9134.

## Current frontier

The semantic plumbing beneath the root drivers is complete. The remaining fixed-field obligations are the substantive Yun decomposition, norm-root isolation, candidate disambiguation, duplicate/order, and multiplicity-completeness proofs. The algebraic-coefficient driver remains downstream of those fixed-field results.

## Next step

Merge this cohesive foundation PR, then prove fixed-field root-driver totality and correctness as the next larger stage before lifting the result to algebraic coefficients. Begin NumberFieldTower root work only after the fixed-field and algebraic layers are complete.

## Blockers

PR CI initially exposed a pre-existing mainline failure: the factor-sweep checker required the pre-squash measurement commit to remain an ancestor. The branch now repairs that incompatible ancestry check while preserving exact relevant-source comparison. The remaining fixed-field completeness block is substantial but its required evaluation, conversion, and merging lemmas are available.
