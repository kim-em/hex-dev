# Bounds strictness, noncomputable specs, DensePoly.toList

Session type: feature follow-ups to issue #8606, stacked branches
`bounds-lt-word` <- `noncomputable-specs` <- `toList-spec`.

## Accomplished

- `ZMod64.Bounds.pLeR (p <= 2^64)` -> `pLtR (p < 2^64)` (PR #8612): the word
  modulus had no consumer; `addImpl`/`subImpl`/`neg` lose the per-call
  `p = 2^64` branch, their `toNat` proofs lose a case, prime selection and
  `CertReify.boundsOfDecide` use the strict test.
- The four csimp'd kernel-facing specs (`ZMod64.add`/`sub`, `DensePoly.mul`,
  `DensePoly.trimTrailingZeros`) are `noncomputable` (PR #8614). Verified that
  `@[csimp]` alone keeps all consumers compilable and that the spec bodies
  vanish from the generated C entirely.
- `noncomputable def DensePoly.toList := toArray.toList` (PR #8615), used by
  the `mul` spec and the migrated core characterisations
  (`toList_getD_eq_coeff`, `toList_eq_coeff_range`, `ofList_toList`,
  `length_toList`, `compose_eq_composeScalarCoeffList*` and their HexPolyFp
  users). No `@[csimp]` twin on purpose: the compiler rejects runtime uses.
- One-sentence SPEC extension of design principle 11 (PR #8616, docs-only).

## Current frontier

All three full-tree builds green (4142 jobs each). CI running on the stack.

## Next step

Merge order once green and approved: #8612 -> #8614 -> #8615 -> #8616.
Follow-up candidate: give `eval`/`scale`/`shift`/`compose` the same
spec/impl split so their specs move onto `toList` and their runtime
bodies stop round-tripping through lists.

## Blockers

None.
