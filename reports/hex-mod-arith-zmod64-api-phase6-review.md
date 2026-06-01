# HexModArith ZMod64 API Phase 6 Review

## Scope

This review covers the public `ZMod64` residue API in:

- `HexModArith/Basic.lean`
- `HexModArith/Ring.lean`
- `HexModArith/Prime.lean`
- `HexModArith/HotLoop.lean`

The review criteria are the Phase 6 API-quality requirements in
`PLAN/Phase6.md` and the `ZMod64` contract in
`SPEC/Libraries/hex-mod-arith.md`: downstream code should reason through
canonical `toNat` representatives and stable wrapper theorems, without
unfolding executable word-arithmetic bodies or hot-loop context internals.

This is a review-only report. No Lean source was changed.

## Overall Assessment

The default `ZMod64` surface is close to Phase 6 quality. The core
constructor and operation APIs expose the expected representative lemmas:

- `toNat_ofNat`, `ofNat_toNat`, `eq_iff_toNat_eq`,
  `ofNat_eq_ofNat_iff_mod_eq`
- `toNat_zero`, `toNat_one`, `toNat_add`, `toNat_sub`, `toNat_mul`,
  `toNat_pow`
- `add_eq_ofNat`, `sub_eq_ofNat`, `mul_eq_ofNat`, `pow_eq_ofNat`, plus
  operator-level aliases for the ordinary operations
- `inv_mul_eq_one_of_coprime` and the prime-modulus wrappers in
  `HexModArith/Prime.lean`

The files also have good namespace hygiene. Imports are local to the intended
dependency boundary: the computational files import `HexArith` and
`Init.Grind`, not Mathlib.

The hot-loop wrappers are also mostly well-shaped. `BarrettCtx.mulMod_eq_mul`
and `MontCtx.fromMont_mulMont_toMont` let callers collapse optimized paths to
ordinary `ZMod64` multiplication, which is exactly the right abstraction
boundary for downstream polynomial code.

## Findings

### 1. `toNat_inv_def` is too heavy for `simp`

`HexModArith/Basic.lean` marks `ZMod64.toNat_inv_def` as
`@[simp, grind =]`. The theorem expands `(inv a).toNat` into the exact
`HexArith.Int.extGcd` representative. That is useful as a low-level
definition lemma, but it is not a good default simplification rule: callers
who simplify expressions containing inverses can be forced into the
implementation body instead of the intended algebraic facts
`inv_mul_eq_one_of_coprime`, `toNat_inv`, or the prime-modulus wrappers.

This is not a correctness issue, but it is a Phase 6 automation-hygiene gap.
The current attribute set weakens encapsulation of the executable inverse
implementation.

Recommended follow-up:

`HexModArith Phase 6: narrow the ZMod64 inverse simp surface`

Suggested deliverable: remove the default `simp` attribute from
`toNat_inv_def` or replace it with a more targeted simp/grind surface around
coprime and prime-modulus inverse use cases, while keeping the explicit
definition lemma available by name.

### 2. Operator neutral laws exist but are not simp-normal forms

`HexModArith/Ring.lean` exposes named operator laws:

- `add_zero`, `zero_add`
- `mul_zero`, `zero_mul`
- `mul_one`, `one_mul`
- `pow_zero`, `pow_succ`

Unlike `pow_one`, `zero_pow`, `one_pow`, and `natCast_self`, these are not
tagged for `simp`. Since this project uses `Lean.Grind.*` algebra classes
rather than Mathlib's standard algebraic hierarchy in the computational
library, downstream callers should not have to rely on unrelated global simp
lemmas to normalize these `ZMod64` operator forms.

Recommended follow-up:

`HexModArith Phase 6: add simp coverage for ZMod64 operator neutral laws`

Suggested deliverable: audit the listed laws and add the appropriate
`@[simp]` annotations, with a small build check that routine expressions such
as `a + 0`, `0 + a`, `a * 1`, `1 * a`, `a * 0`, `0 * a`, and `a ^ 0`
normalize without unfolding operation definitions.

### 3. `MontResidue` lacks Nat-representative extensionality wrappers

`HexModArith/HotLoop.lean` gives `MontResidue.ext` by backing `UInt64` word
and the basic `toNat` view, but unlike `ZMod64` it does not expose
`ext_toNat` or `eq_iff_toNat_eq`. Most Montgomery wrapper proofs already work
by moving through `toNat` and `fromMont`, so downstream hot-loop proofs have
to bridge back through `UInt64.toNat_inj` manually.

This is a small encapsulation gap, not a missing theorem about Montgomery
arithmetic.

Recommended follow-up:

`HexModArith Phase 6: add MontResidue toNat extensionality lemmas`

Suggested deliverable: add `MontResidue.ext_toNat` and
`MontResidue.eq_iff_toNat_eq`, with docstrings matching the `ZMod64`
extensionality surface.

## Checked Clusters With No Follow-Up Needed

- `Bounds`, `ZMod64`, `ofNat`, `normalize`, `values`, and equality by
  canonical representative have clear characterizing lemmas.
- Default `add`, `sub`, `mul`, and `pow` can be reasoned about through
  `toNat_*` lemmas without unfolding word-level branches.
- `inv` has the required extern-backed `HexArith.Int.extGcd` path and a
  checked coprime inverse law; the issue is only its default simp exposure.
- `Lean.Grind.Semiring`, `Lean.Grind.Ring`, `Lean.Grind.CommRing`, and
  `Lean.Grind.IsCharP` are present in `HexModArith/Ring.lean`.
- Prime-modulus facts cover no-zero-divisors, nonzero inverse laws, and
  Fermat's theorem with both explicit-prime and typeclass-driven entry points.
- Barrett and Montgomery optimized multiplication wrappers expose semantic
  agreement with ordinary `ZMod64` multiplication, so callers do not need to
  unfold `HexArith` context internals for product reasoning.

## Phase 6 Readiness

`HexModArith` should not be bumped to `done_through: 6` on this review alone.
The surface is broadly sound and well documented, but the three follow-ups
above are narrow enough that they should be completed before declaring the
`ZMod64` API polished.
