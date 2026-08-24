# hex-sparse-poly-mathlib: activation and the complete Equiv surface

## Accomplished

- Authored the companion SPEC
  (`HexSparsePolyMathlib/SPEC/hex-sparse-poly-mathlib.md`) with the
  `## Headline correctness theorem` section naming `equiv` with
  `coeff_equiv` and `equiv_support` as its semantic clauses.
- Activated the library: `lean_lib HexSparsePolyMathlib`, umbrella,
  `libraries.yml` `status: active` with the sparse-mathlib-conversion
  input family, `done_through: 1`.
- `HexSparsePolyMathlib/Equiv.lean`, fully proven (zero sorries from
  the start): `denseEquiv` (packaging `toDense`/`ofDense`, the round
  trips, and `toDense_add`/`toDense_mul`), `equiv :=
  denseEquiv.trans HexPolyMathlib.equiv`, `coeff_equiv`,
  `equiv_toDense`, `equiv_support` (headline), `equiv_eval` (via a new
  `eval_toPolynomial` dense helper), `equiv_derivative`,
  `equiv_compose`, `equiv_substPow`.
- Both equivalences are stated at Mathlib `[CommRing R]`, following the
  parent SPEC's law-placement note (the core multiplicative transport
  sits at `Lean.Grind.CommRing`); the parent SPEC's Mathlib-layer block
  updated to match, with the weakening path recorded.
- Core supporting lemma `Hex.SparsePoly.mem_support_iff` added to
  `HexSparsePoly/Arith.lean` (representation facts belong in the core,
  per the companion SPEC's scope rule); `equiv_support` consumes it.
- Mathlib's `Semiring.toGrindSemiring` instances make the core's
  Grind-stated transport lemmas apply directly at Mathlib classes; only
  two `Zero.zero`-vs-`0` mismatches needed `show`/`congrArg` bridging
  in `eval_toPolynomial`.

## Current frontier

Companion at Phase 2 (scaffolding review). The stack below was also
rebased onto current main this session (the bottom PR had gone DIRTY
against main) and force-pushed; #9374 has auto-merge armed.

## Next step

Companion Phase 2 independent review, then the conformance module
(`conformance/HexSparsePolyMathlib/Conformance.lean` + HexConformance
glob) for Phase 3, then phases 4-6 per the proof-track rules.

## Blockers

None.
