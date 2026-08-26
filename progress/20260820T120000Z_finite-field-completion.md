# Finite-field libraries: completion pass

## Accomplished

Landed earlier in this session (merged):

- `HexPolyFpMathlib`, extracted from `HexBerlekampMathlib`, plus
  `GF2Poly ≃+* Polynomial (ZMod 2)` (#9295).
- CLMUL path coverage: both the portable and the intrinsic compiled
  paths are cross-checked on every CI run (#9296).

Open on branches:

- #9297 `ff-gf2-grind`: the `Lean.Grind` tower for `GF2nPoly` and the
  `HexGF2/Field.lean` split. Split three ways rather than two, because
  the line-count lint applies a 2000-line budget to *new* files, not the
  3000-line one: `Field/Poly.lean` (representation and arithmetic),
  `Field/Roots.lean` (root counting and Frobenius), `Field/Grind.lean`
  (the bundled instances). Four private helpers were published to cross
  the new boundary; two others turned out to duplicate lemmas
  `HexGF2.Multiply` already proves and were deleted.
- #9298 `ff-spec-reconcile`: the SPEC reconciliation. The `hex-gfq`,
  `hex-conway`, and `hex-gfq-field` API blocks now match the shipped
  signatures, `hex-gfq-mathlib`'s SPEC is written to the depth of the
  computational ones, and the composite `GF2q n ≃+* GaloisField 2 n`
  that both SPECs named is defined. `CommittedEntry` and
  `PackedGF2Entry` moved from `Hex.Conway` to `Hex.GFq`, where they are
  declared.
- #9299 `ff-gf2-instances`: `CommRing Hex.GF2Poly` and
  `Field (Hex.GF2nPoly f hirr)` under `Fact (0 < f.degree)`, built with
  Mathlib's minimal-axioms constructors so the operations stay the
  executable ones — `p * q = GF2Poly.mul p q` closes by `rfl` and `ring`
  applies to packed polynomials. Plus `Neg`/`Sub` on `GF2Poly`, and the
  `HexGF2` chapter's Mathlib-correspondence, performance, and
  field-wrapper sections.
- `ff-manual-conway` (this branch): decidable primality in `HexArith`,
  which collapses nine hand-written divisor case splits to `by decide`;
  a committed example field `GF(5⁴)` in `HexGFqField/Example.lean` so
  the manual cites an irreducibility proof instead of rebuilding a
  certificate with an 8M-heartbeat bump; `@[expose]` on
  `checkIrreducibilityCertificateLinear` and `checkPowChainLinear`,
  without which the checker's own docstring promise ("should be
  discharged by `decide`") is unreachable from a `module` file; and the
  Conway chapter's regeneration-command section and downstream links.

## Current frontier

Conway Tier 2 (primitivity plus divisor compatibility, W1c) and the
subfield embeddings it enables (W1d) are **not** done, and are not a
matter of finishing something started. Tier 2 needs the multiplicative
order of a root of each committed entry, hence a factorization of
`p ^ n - 1` carried as checkable data, an order predicate over the
executable field, and a kernel replay of `x ^ ((p^n - 1) / q) ≠ 1` for
each prime `q` of that factorization — for all 38 committed entries, at
the same proof budget that already sets the table's scope. That is its
own workstream with its own infrastructure, not a follow-on edit.

`Field (Hex.GF2n ...)` is also outstanding, for a smaller reason:
`HexGF2` proves `GF2n`'s field-operation laws but not the bare ring
laws (`add_assoc`, `mul_comm`, and so on) that the minimal-axioms
constructor consumes. `GF2nPoly` has them, which is why it got the
instance and `GF2n` did not.

`EuclideanDomain Hex.GF2Poly` is a design question rather than more of
the same: `HexGF2` already defines `Div` and `Mod` on `GF2Poly`, and
`EuclideanDomain` supplies its own, so the two have to be reconciled
rather than stacked.

## Next step

Prove `GF2n`'s ring laws in `HexGF2` and add the Mathlib `Field`
instance beside the `GF2nPoly` one; then take Conway Tier 2 as a
separate workstream, starting with the `p ^ n - 1` factorization
certificate.

## Blockers

None. All four branches build locally; CI on #9297, #9298, and #9299 is
queued behind the account's runner cap.
