# HexArith Extended-GCD API Phase 6 Review

## Scope

Reviewed `HexArith/ExtGcd.lean` against `SPEC/Libraries/hex-arith.md`,
`SPEC/design-principles.md`, and `PLAN/Phase6.md`.

The reviewed public surfaces are:

- `HexArith.extGcd`
- `Hex.pureIntExtGcd`
- `HexArith.Int.extGcd`
- `HexArith.UInt64.extGcd`
- their `_fst`, `_bezout`, `_spec`, and nonnegative/coercion-specialized
  wrapper theorems

This is a Phase 6 API-quality review. It does not edit Lean source.

## Findings

No follow-up findings.

- The natural-number API exposes the expected executable result plus named
  theorem surface: `HexArith.extGcd_fst`, `HexArith.extGcd_bezout`, and
  `HexArith.extGcd_spec`. Callers can recover both the gcd projection and the
  Bezout certificate after destructuring the triple without unfolding the
  recursive Euclidean implementation or the private `natDivMod` helper.
- The pure integer reference is correctly separated from the public GMP-backed
  integer API. `Hex.pureIntExtGcd` has matching `_fst`, `_bezout`, and `_spec`
  lemmas, while `HexArith.Int.extGcd` carries the extern contract and re-exports
  the same proof surface through public wrapper theorems.
- The integer API includes the coercion-specialized facts downstream users need:
  `HexArith.Int.extGcd_fst_ofNat`, `HexArith.Int.extGcd_spec_ofNat`, and
  `HexArith.Int.extGcd_zero_left_s_ofNat`. The zero-left coefficient lemma is
  used directly by `HexPolyFp/PrimeField.lean` for the `0^-1 = 0` convention.
- The `UInt64` API states the gcd theorem at the right representation boundary:
  `HexArith.UInt64.extGcd_fst` characterizes `g.toNat`, and
  `HexArith.UInt64.extGcd_bezout` states the certificate over
  `Int.ofNat a.toNat` and `Int.ofNat b.toNat`. The combined
  `HexArith.UInt64.extGcd_spec` gives callers both facts without exposing the
  bridge through `HexArith.Int.extGcd`.
- Existing downstream proof users in `HexModArith/Basic.lean` rely on
  `HexArith.Int.extGcd_bezout` and `HexArith.Int.extGcd_fst` by name after
  generalizing the returned triple. Runtime/cross-check users in
  `HexArith/CrossCheck.lean`, `HexArith/Bench.lean`, and
  `HexArith/Conformance.lean` consume the executable APIs directly. I did not
  find a caller forced to unfold the implementation loops.
- Automation is appropriate for the current theorem shapes. The projection
  facts are tagged `[simp]`, while the Bezout and combined-spec theorems remain
  explicit named facts rather than broad simplification rules over linear
  integer expressions.
- Public declarations and the non-obvious private invariant helpers have
  docstrings. Namespace placement is narrow, and `HexArith/ExtGcd.lean` does
  not add imports or Mathlib dependencies.

## Residual Risk Checked

This review is limited to API polish for the extended-GCD surface. It did not
review Barrett, Montgomery, `UInt64` wide arithmetic, modular exponentiation,
or performance behavior beyond checking that benchmark and conformance callers
use the public executable APIs rather than implementation details.
