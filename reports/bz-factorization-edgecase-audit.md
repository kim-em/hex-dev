# Berlekamp-Zassenhaus Factorization Edge-Case Audit

## Scope

Reviewed the public `Factorization` edge-case coverage for
`HexBerlekampZassenhaus.factor` against:

- `SPEC/Libraries/hex-berlekamp-zassenhaus.md` §"Output convention: the
  `Factorization` record" and §"Edge cases".
- `HexBerlekampZassenhaus/Conformance.lean`:
  `factorizationEdgeCases`, `factorizationCaseMatches`, and
  `factorPreservesProduct`.
- `HexBerlekampZassenhaus/EmitFixtures.lean` and the committed
  `conformance-fixtures/HexBerlekampZassenhaus/bz.jsonl` sample.
- Directive #2637's signed-scalar, signed-constant, signed-monomial,
  repeated-factor, and non-unit-content symptoms.

This is coverage audit only; it does not review the factoring implementation.

## Coverage Map

`factorizationCaseMatches` checks both exact `Factorization` equality and
product preservation for every row in `factorizationEdgeCases`:

```lean
let φ := factor c.input
φ == c.expected && Factorization.product φ == c.input
```

That means the Lean guard verifies the signed scalar and the
`(factor, multiplicity)` buckets directly, not just reconstruction.

| SPEC input | SPEC output shape | Lean guard coverage | JSONL/oracle coverage |
|---|---|---|---|
| `0` | `scalar = 0`, no factors | `factorizationEdgeCases`: `input := 0`, expected `0 #[]` | `edge/zero`, value `[0,[]]` |
| `1` | `scalar = 1`, no factors | `input := 1`, expected `1 #[]` | `edge/one`, value `[1,[]]` |
| `-1` | `scalar = -1`, no factors | `input := -1`, expected `-1 #[]` | `edge/neg_one`, value `[-1,[]]` |
| `2` | `scalar = 2`, no factors | `input := DensePoly.C 2`, expected `2 #[]` | `edge/two`, value `[2,[]]` |
| `-6` | `scalar = -6`, no factors | `input := DensePoly.C (-6)`, expected `-6 #[]` | `edge/neg_six`, value `[-6,[]]` |
| `X` | `scalar = 1`, `X` multiplicity `1` | `input := ZPoly.X`, expected `#[(ZPoly.X, 1)]` | `edge/x`, value `[1,[[[0,1],1]]]` |
| `-X` | `scalar = -1`, `X` multiplicity `1` | `input := -ZPoly.X`, expected `(-1) #[(ZPoly.X, 1)]` | `edge/neg_x`, value `[-1,[[[0,1],1]]]` |
| `X^2` | `scalar = 1`, `X` multiplicity `2` | `input := ZPoly.X * ZPoly.X`, expected `#[(ZPoly.X, 2)]` | `edge/x_squared`, value `[1,[[[0,1],2]]]` |
| `-X^2 + 1` | `scalar = -1`, `X - 1` and `X + 1` multiplicity `1` | `input := zpoly #[1, 0, -1]`, expected `#[(linear (-1), 1), (linear 1, 1)]` | `edge/neg_x_squared_plus_one`, value `[-1,[[[1,1],1],[[-1,1],1]]]` |
| `(X - 1)^2` | `scalar = 1`, `X - 1` multiplicity `2` | `input := repeatedRootPoly`, expected `#[(linear 1, 2)]` | `edge/x_minus_one_squared`, value `[1,[[[-1,1],2]]]` |
| `-(X - 1)^2` | `scalar = -1`, `X - 1` multiplicity `2` | `input := DensePoly.scale (-1) repeatedRootPoly`, expected `(-1) #[(linear 1, 2)]` | `edge/neg_x_minus_one_squared`, value `[-1,[[[-1,1],2]]]` |
| `2(X - 1)(X + 1)` | `scalar = 2`, both linear factors multiplicity `1` | `input := zpoly #[-2, 0, 2]`, expected `2 #[(linear (-1), 1), (linear 1, 1)]` | `edge/two_x_minus_one_x_plus_one`, value `[2,[[[1,1],1],[[-1,1],1]]]` |
| `-2(X - 1)^2` | `scalar = -2`, `X - 1` multiplicity `2` | `input := negativeRepeatedRootWithContent`, expected `(-2) #[(linear 1, 2)]` | `edge/neg_two_x_minus_one_squared`, value `[-2,[[[-1,1],2]]]` |

The Lean table also includes signed constant rows beyond the SPEC table
(`-2`, `6`) and the JSONL sample includes matching `edge/neg_two` and
`edge/six` oracle cases.

## Symptom Checks

- Negative-leading inputs are covered by `-X`, `-X^2 + 1`,
  `-(X - 1)^2`, and `-2(X - 1)^2`. The scalar field is expected to carry the
  sign in each case.
- Signed constants are covered by `-1`, `-2`, and `-6`, with no polynomial
  factors. Positive constants `1`, `2`, and `6` are also covered.
- Signed monomials are covered by `X`, `-X`, `X^2`, and the extra direct guard
  for `negativeMonomial`; multiplicities are checked as factor buckets.
- Repeated factors are covered by `X^2`, `(X - 1)^2`, `-(X - 1)^2`, and
  `-2(X - 1)^2`; each expected value uses multiplicity `2`, not duplicated
  factor entries.
- Non-unit content is covered in the SPEC table by `2(X - 1)(X + 1)` and
  `-2(X - 1)^2`. `EmitFixtures.lean` additionally emits
  `content2/cyclo5` and `content3/cyclo7`, whose committed JSONL expected
  values keep content in the scalar field and the primitive factor in a
  `(factor, multiplicity)` bucket.

## Oracle Coverage

The committed JSONL contains both `poly` and `result` records for every SPEC
edge case. The fixture format serializes `Factorization` as:

```text
[scalar, [[coeffs, multiplicity], ...]]
```

The `scripts/oracle/bz_flint.py` `factor` checker independently verifies:

- exact product reconstruction,
- signed scalar agreement with FLINT content,
- nonconstant primitive polynomial factors with positive leading coefficient,
- no duplicate polynomial factors,
- direct agreement with FLINT's irreducible-factor multiset and multiplicities.

This oracle path therefore covers scalar and factor-bucket structure
independently of the Lean `#guard` table.

## Conclusion

No coverage gap found. The current executable conformance coverage matches the
SPEC edge-case table and directly exercises directive #2637's sign,
signed-constant, signed-monomial, repeated-factor, and non-unit-content
symptoms. No follow-up issue is needed from this audit.
