# HexArith UInt64 Wide API Phase 6 Review

## Scope

Reviewed the low-level wide-word arithmetic surface against
`SPEC/Libraries/hex-arith.md`, `SPEC/design-principles.md`, and
`PLAN/Phase6.md`.

Files reviewed:

- `HexArith/UInt64/Wide.lean`
- `HexArith/ffi/wide_arith.c`
- `lakefile.lean`

Consumer files checked:

- `HexArith/Barrett/Reduce.lean`
- `HexArith/Montgomery/Redc.lean`
- `HexArith/Montgomery/Context.lean`
- `HexModArith/HotLoop.lean`
- `HexArith/Conformance.lean`

This is a Phase 6 API-quality review. It does not edit Lean or C source.

## Findings

No follow-up findings.

- The executable wide-word operations have the required shape: `UInt64.mulHi`,
  `UInt64.mulFull`, `UInt64.addCarry`, and `UInt64.subBorrow` all have logical
  Lean bodies and matching `@[extern]` declarations. The C implementations in
  `HexArith/ffi/wide_arith.c` implement the same contracts with `__uint128_t`
  for multiplication and overflow intrinsics for add/subtract with carry or
  borrow.
- The extern C source is wired through the `hexarithffi` `extern_lib` block in
  `lakefile.lean`, alongside `mpz_gcdext.c`. This matches the SPEC requirement
  that wide-word executable definitions land with native runtime externs rather
  than relying on the GMP-heavy logical Lean bodies.
- The theorem surface covers the promised Nat-level characterisations:
  `UInt64.toNat_mulHi`, `UInt64.toNat_mulFull`, `UInt64.mulHi_mulLo`,
  `UInt64.mulLo_add_mulHi`, and `UInt64.toNat_addCarry` are all public and
  directly state the reconstruction laws named in the SPEC. The module also
  exposes the useful component facts `toNat_mulFull_fst`,
  `toNat_mulFull_snd`, `toNat_addCarry_fst`, `addCarry_snd_eq_true`,
  `addCarry_snd_eq_false`, `toNat_subBorrow_fst`, `subBorrow_snd_eq_true`,
  `subBorrow_snd_eq_false`, and `UInt64.toNat_subBorrow`.
- The `mulFull` API has the performance-oriented bridge the SPEC asks for:
  `UInt64.mulFull_eq_mulHi_mul`, plus `[simp]` projection lemmas
  `mulFull_fst_eq_mulHi` and `mulFull_snd_eq_mul`. The executable REDC routine
  in `HexArith/Montgomery/Redc.lean` uses `UInt64.mulFull m p` to obtain both
  halves of `m * p` in one extern call, and the proof rewrites through
  `UInt64.mulFull_eq_mulHi_mul` instead of duplicating the product split.
- The Barrett bridge uses `UInt64.toNat_mulHi` directly in
  `HexArith/Barrett/Reduce.lean` to relate the executable quotient estimate to
  the Nat-level Barrett quotient. The Montgomery bridge uses
  `UInt64.toNat_addCarry`, `UInt64.mulHi_mulLo`, and
  `UInt64.mulLo_add_mulHi` directly in `HexArith/Montgomery/Redc.lean` and
  `HexArith/Montgomery/Context.lean`. I did not find consumer proofs unfolding
  `mulHi`, `mulFull`, `addCarry`, or `subBorrow` outside
  `HexArith/UInt64/Wide.lean`.
- Automation annotations are conservative and appropriate for the current
  surface. Projection and bit-characterisation lemmas used for normalization
  carry `[simp]` or `[grind =]` where useful, while larger reconstruction
  theorems remain named facts to avoid broad arithmetic rewrite churn.
- Public declarations and the non-obvious private quotient helper in
  `HexArith/UInt64/Wide.lean` have docstrings. The module imports only `Std`,
  remains Mathlib-free, and does not introduce namespace pollution beyond the
  intended `UInt64` extension namespace.

## Residual Risk Checked

This review checked API shape, native extern wiring, theorem discoverability,
and current downstream proof usage. It did not re-run performance benchmarks or
prove the C ABI contract independently; the existing conformance surface in
`HexArith/Conformance.lean` exercises representative runtime cases for
`mulHi`, `mulFull`, `addCarry`, and `subBorrow`, while the Lean theorem surface
continues to define the proof semantics.
