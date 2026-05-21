# HexModArith Hot-Loop API Phase 6 Review

## Scope

Reviewed the public modular-arithmetic API surface requested by #5713:

- `HexModArith/Basic.lean`
- `HexModArith/HotLoop.lean`
- `HexModArith/Ring.lean`
- `HexModArith/Prime.lean`

This is a Phase 6 API-quality review, not a source-change pass. No Lean source
edits are required by this report.

## Summary

The ordinary `ZMod64` arithmetic surface is in good shape for downstream use.
The executable definitions `mul`, `pow`, and `inv` have semantic docstrings,
and callers can reason through stable characterisation lemmas instead of
unfolding implementations:

- `ZMod64.toNat_mul`, `ZMod64.mul_eq_ofNat`, and `ZMod64.mul_op_eq_ofNat`
  characterise extern-backed multiplication.
- `ZMod64.toNat_pow`, `ZMod64.pow_eq_ofNat`, and `ZMod64.pow_op_eq_ofNat`
  characterise exponentiation.
- `ZMod64.inv_mul_eq_one_of_coprime`, plus the prime-modulus wrappers in
  `HexModArith/Prime.lean`, expose the inverse laws downstream code is likely
  to need.
- `HexModArith/Ring.lean` supplies the expected `Lean.Grind` ring instances
  and representative-level simp/grind lemmas for casts, negation, and scalar
  multiplication.

The hot-loop wrapper layer also has the important semantic facts:

- `BarrettCtx.mulMod_eq_mul` proves the Barrett wrapper agrees with ordinary
  `ZMod64` multiplication.
- `MontCtx.fromMont_toMont`, `MontCtx.toNat_mulMont`,
  `MontCtx.mulMont_repr`, and `MontCtx.fromMont_mulMont_toMont` give the
  required Montgomery entry, loop, and exit facts.

There are two follow-up-quality gaps before I would call the hot-loop API fully
Phase-6-polished.

## Findings

### 1. Add public smart constructors for `Hex.BarrettCtx` and `Hex.MontCtx`

`HexModArith/HotLoop.lean` exposes `Hex.BarrettCtx` and `Hex.MontCtx` as
structures whose fields include both a word modulus and an underlying
`_root_.BarrettCtx`/`_root_.MontCtx` (`HotLoop.lean` lines 22-42). Existing
callers in `HexModArith/Bench.lean` and `HexModArith/Conformance.lean` build
these records manually by filling `modulus`, `modulus_eq`, and `toUInt64Ctx`.

That is usable inside the library, but it leaks the representation boundary the
wrapper is supposed to hide. A downstream caller should not need to know the
root-level context field names just to opt into the `ZMod64` hot loop.

Recommended follow-up issue:

`HexModArith Phase 6: add smart constructors for ZMod64 Barrett/Montgomery contexts`

Target declaration cluster:

- `Hex.BarrettCtx`: add a constructor such as `ofModulus`/`mkOfNat` for
  `p < 2^32`, returning `Hex.BarrettCtx p` from the indexed modulus and proofs.
- `Hex.MontCtx`: add a constructor such as `ofOddModulus` for odd `p`, returning
  `Hex.MontCtx p`.
- Add small `[simp]` facts for the stored `modulus_eq` and, if useful,
  examples replacing the manual records in `HexModArith/Conformance.lean`.

### 2. Audit `[grind]` coverage for hot-loop wrapper characterisation lemmas

The core arithmetic characterisation lemmas in `Basic.lean` and `Ring.lean`
use `[simp, grind =]` consistently, for example `toNat_mul` and `toNat_pow`.
The corresponding hot-loop wrapper lemmas in `HotLoop.lean` are `[simp]` only:
`BarrettCtx.toNat_mulMod`, `BarrettCtx.mulMod_eq_mul`,
`MontCtx.toNat_toMont`, `MontCtx.fromMont_toMont`,
`MontCtx.toNat_mulMont`, `MontCtx.mulMont_repr`, and
`MontCtx.fromMont_mulMont_toMont`.

`simp` already normalizes most direct goals, so this is not a correctness gap.
It is a Phase 6 automation gap: callers using `grind` against mixed ordinary
and hot-loop multiplication may still need manual rewrites through the hot-loop
surface.

Recommended follow-up issue:

`HexModArith Phase 6: add grind coverage for hot-loop wrapper facts`

Target declaration cluster:

- Try `[simp, grind =]` on the representative-level equalities
  `BarrettCtx.toNat_mulMod`, `MontCtx.toNat_toMont`,
  `MontCtx.toNat_mulMont`, and `MontCtx.mulMont_repr`.
- Try `[grind =]` or a small set of dedicated wrapper lemmas for the equality
  bridges `BarrettCtx.mulMod_eq_mul` and
  `MontCtx.fromMont_mulMont_toMont`.
- Keep the final annotations conservative: if a lemma causes search loops,
  leave it `[simp]` and document the local reason in the follow-up PR.

## No Follow-Up Needed

No Phase 6 follow-up is needed for the default `ZMod64` multiplication,
exponentiation, casts, ring instances, or prime-modulus theorem surface within
this review scope. They already expose public theorem names, docstrings, and
statement shapes that let downstream code reason from representatives or from
ring/prime facts without unfolding executable definitions.
