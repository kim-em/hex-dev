# HexArith Barrett/Montgomery API Phase 6 Review

## Scope

Reviewed the public API and theorem surface for the lower-level word-arithmetic
context layers:

- `HexArith/Barrett/Context.lean`
- `HexArith/Montgomery/Context.lean`

Supporting context checked where it defines the exported structures and helper
theorems consumed by those files:

- `HexArith/Barrett/Reduce.lean`
- `HexArith/Barrett/ReduceNat.lean`
- `HexArith/Montgomery/Redc.lean`
- `HexArith/Montgomery/RedcNat.lean`
- `HexArith/Montgomery/InvNat.lean`
- `HexModArith/HotLoop.lean`

This is a Phase 6 API-quality review. It does not edit Lean source.

## Summary

The Barrett and Montgomery context APIs expose the right correctness facts for
downstream users. In particular:

- `BarrettCtx.mulMod_lt`, `BarrettCtx.toNat_mulMod`, and
  `BarrettCtx.mulMod_eq` let callers reason about word-level Barrett
  multiplication without unfolding `mulMod` or `barrettReduce`.
- `MontCtx.toMont_lt`, `MontCtx.fromMont_lt`, `MontCtx.fromMont_repr`,
  `MontCtx.toNat_toMont`, `MontCtx.mulMont_repr`,
  `MontCtx.fromMont_toMont`, `MontCtx.toNat_mulMont`, and
  `MontCtx.mulMont_eq` cover the standard Montgomery entry, loop, and exit
  reasoning pattern.
- The lower layers provide named bridges for the executable reducers:
  `toNat_barrettReduce_eq_mod`, `barrettReduce_eq`,
  `redc_mul_word_mod`, `toNat_redc`, and `redc_lt`.
- Public declarations and the non-obvious private helpers have docstrings.
  The files keep imports narrow and do not require Mathlib.

I found two Phase 6 polish follow-ups. Neither is a correctness issue.

## Follow-Up Recommendations

### 1. Add grind coverage for the lower-level Barrett/Montgomery context facts

The core semantic lemmas are currently mostly `[simp]` or unannotated. That is
enough for direct normalization, but it leaves `grind` users in downstream
proofs rewriting the hot-loop surface by hand. This mirrors the wrapper-layer
automation gap already reported for `HexModArith/HotLoop.lean`.

Recommended follow-up issue:

`HexArith Phase 6: add grind coverage for Barrett/Montgomery context facts`

Target declarations:

- Try `[simp, grind =]` on `BarrettCtx.toNat_mulMod`,
  `MontCtx.toNat_toMont`, and `MontCtx.toNat_mulMont`.
- Try `[grind =]` on equality bridges such as `BarrettCtx.mulMod_eq`,
  `MontCtx.fromMont_toMont`, `MontCtx.mulMont_repr`, and
  `MontCtx.mulMont_eq`.
- Consider `[grind]` on residue-bound facts such as `BarrettCtx.mulMod_lt`,
  `MontCtx.toMont_lt`, `MontCtx.fromMont_lt`, and `MontCtx.mulMont_lt` if
  they improve downstream boundedness goals without causing search loops.
- Keep annotations conservative: if a theorem loops or bloats search, leave it
  unannotated and document the local reason in the implementation PR.

### 2. Add named constructor characterisation lemmas for `BarrettCtx.mk` and `MontCtx.mk`

Both public constructors are usable today, and their fields reduce by
definition. For Phase 6 encapsulation, downstream proofs should have stable
named lemmas instead of relying on unfolding constructor bodies or raw field
reduction when they need the computed context constants.

Recommended follow-up issue:

`HexArith Phase 6: characterise Barrett and Montgomery context constructors`

Target declaration cluster:

- For `BarrettCtx.mk`, add small `[simp]` lemmas for the projections callers
  may inspect, especially `toNat_pinv` specialized to the constructor and the
  stored small-modulus hypotheses.
- For `MontCtx.mk`, add small `[simp]` lemmas for the constructor projections:
  the oddness witness, `p'_eq`, `r2_eq`, and possibly the already-public
  derived facts `p_odd_nat`, `p_pos`, and `p_lt_R` specialized to `mk`.
- Prefer theorem names that match Mathlib projection style, for example
  `BarrettCtx.mk_pinv_toNat`, `MontCtx.mk_p'_eq`, and `MontCtx.mk_r2_eq`, if
  those names fit local conventions.

## No Follow-Up Needed

No follow-up is needed for the basic theorem shapes of Barrett multiplication
or Montgomery conversion/multiplication. They already expose the downstream
contracts promised in `SPEC/Libraries/hex-arith.md`:

- Barrett multiplication has the residue-bound theorem, Nat-level modular
  theorem, and word-equality theorem.
- Montgomery arithmetic has separate entry (`toMont`), exit (`fromMont`), loop
  multiplication (`mulMont`), represented-residue, and standard-product
  theorem shapes.
- The REDC and Barrett reducer layers have direct public bridge lemmas, so
  users are not forced to unfold the executable reducer definitions.

The Nat helper surface in `HexArith/Nat/ModArith.lean` and
`HexArith/Nat/Pow.lean` remains out of scope for this review; it was covered by
`reports/hex-arith-nat-api-phase6-review.md`.
