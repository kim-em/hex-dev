## Current state

`HexModArith/HotLoop.lean` (the hot-loop wrapper surface that lifts the
`UInt64`-level Barrett/Montgomery contexts from `HexArith` to the
`ZMod64 p` / `MontResidue p` indexed-modulus surface, Mathlib-free —
imports only `HexArith.Barrett.Context`, `HexArith.Montgomery.Context`,
`HexModArith.Basic`, `HexModArith.Ring`) already exposes its **headline**
characterising lemmas to `grind`: `toNat_mulMod` (172), `mulMod_eq_mul`
(190), `toNat_toMont` (362), `fromMont_toMont` (381), `toNat_mulMont`
(405), `mulMont_repr` (429), `fromMont_mulMont_toMont` (447) are all
`@[simp, grind =]` (landed via the now-closed #6239).

But a second tier of clean equation-shaped public `@[simp]` lemmas — the
identity/absorbing `mulMod` and Montgomery round-trip companions, plus the
smart-constructor projection equations — is still `@[simp]`-only and lacks
`@[grind =]`, so downstream `grind` goals over these forms cannot close
without an explicit lemma list. This is the same asymmetry the ongoing
Phase 6 sweep removes file by file (cf. #8030 finishing the `repr_*`
cluster after `toQuotient_*` was done, and #8032 finishing the `mulMod`
identity cluster in `HexArith/Barrett/Context.lean` after the headline
pass). #6239 explicitly scoped only the headline lemmas, leaving this tier
unfiled.

The `@[simp]`-only candidates (re-read each before promoting):

Smart-constructor projection equations (all literal `lhs = rhs`):
- `BarrettCtx.ofModulus_modulus` (117) — `(ofModulus hp hlt).modulus = UInt64.ofNat p`
- `BarrettCtx.ofModulus_modulus_eq` (121) — `(ofModulus hp hlt).modulus.toNat = p`
- `BarrettCtx.ofModulus_toUInt64Ctx_pinv` (149) — `…toUInt64Ctx.pinv = UInt64.ofNat (barrettRadix / p)`
- `MontCtx.modulus_ofOddModulus` (284) — `(ofOddModulus hp hodd).modulus = ZMod64.modulusWord p hp`
- `MontCtx.modulus_toNat_ofOddModulus` (289) — `(ofOddModulus hp hodd).modulus.toNat = p`
- `MontCtx.toUInt64Ctx_ofOddModulus` (295) — `…toUInt64Ctx = _root_.MontCtx.mk (ZMod64.modulusWord p hp) hodd`

`MontResidue` projection equations:
- `MontResidue.toUInt64_eq_val` (76) — `a.toUInt64 = a.val`
- `MontResidue.toNat_eq_val` (79) — `a.toNat = a.val.toNat`

Barrett identity/absorbing `mulMod` lemmas:
- `BarrettCtx.mulMod_one_left` (201) — `ctx.mulMod 1 a = a`
- `BarrettCtx.mulMod_zero_left` (214) — `ctx.mulMod 0 a = 0`
- `BarrettCtx.mulMod_one_right` (228) — `ctx.mulMod a 1 = a`
- `BarrettCtx.mulMod_zero_right` (241) — `ctx.mulMod a 0 = 0`

Montgomery round-trip identity lemmas:
- `MontCtx.fromMont_mulMont_toMont_one_left` (459) — `ctx.fromMont (ctx.mulMont (ctx.toMont 1) (ctx.toMont a)) = a`
- `MontCtx.fromMont_mulMont_toMont_zero_left` (473) — `… (ctx.toMont 0) … = 0`
- `MontCtx.fromMont_mulMont_toMont_one_right` (487) — `… (ctx.toMont 1)) = a`
- `MontCtx.fromMont_mulMont_toMont_zero_right` (501) — `… (ctx.toMont 0)) = 0`

**Exclude** `MontResidue.toNat_lt` (82) — it is `a.toNat < p`, an
inequality, not an equation. Confirm and note the exclusion in the PR body.

## Deliverables

1. Promote the equation-shaped `@[simp]` lemmas listed above to
   `@[simp, grind =]`, matching the `@[simp, grind =]` convention already
   used for the headline lemmas in this same file. Only promote literal
   `lhs = rhs` forms; exclude `toNat_lt` and anything else that turns out
   to be an iff/inequality/proof-valued on re-reading, and say which and
   why in the PR body.
2. The Barrett `mulMod_one/zero` and Montgomery round-trip identity
   lemmas sit alongside the already-`grind` headline rewrites
   `mulMod_eq_mul` (`ctx.mulMod a b = a * b`) and
   `fromMont_mulMont_toMont` (`… = a * b`). Confirm the new oriented
   `grind =` rewrites are sound and do **not** loop against those
   (different LHS head patterns, so no cycle is expected; note that
   `mulMod_comm` at 252 and `mulMont_comm` are plain theorems, not
   `grind` rules, so commutativity introduces no cycle). If any lemma
   loops, leave it `@[simp]`-only and note why.
3. Confirm no `grind` loop or build-time regression in the module.

## Context

One file in the ongoing Phase 6 "grind automation coverage" sweep: one
`.lean` file per issue, promoting the equation-shaped public `@[simp]`
characterising lemmas to `@[simp, grind =]` so downstream `grind` goals
close without an explicit lemma list. Scope is confined to
`HexModArith/HotLoop.lean`; do not touch other files. `HexModArith` is a
Mathlib-free executable library — do not introduce any Mathlib dependency.
The headline-lemma half of this file was done by #6239 (closed); this
issue covers the remaining identity/absorbing and constructor-projection
tier only, so there is no overlap.

## Verification

- `lake build HexModArith` → `Build completed successfully`, and
  `HexModArith.HotLoop` builds without a grind-loop slowdown.
- `python3 scripts/check_dag.py` → exit 0.
- `git diff --check` clean; no added-line `sorry`/`axiom`/`native_decide`/
  `TODO`/`FIXME`.
