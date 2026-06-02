# HexArith UInt64 Wide-Word API Phase 6 Review

## Scope

Reviewed the shared wide-word substrate in:

- `HexArith/UInt64/Wide.lean`
- `HexArith/ffi/wide_arith.c`
- `HexArith/Barrett/Reduce.lean`
- `HexArith/Montgomery/Redc.lean`
- `HexArith/Montgomery/Context.lean`
- `HexArith/Conformance.lean`

The criteria are `PLAN/Phase6.md` and the Layer 1 requirements in
`SPEC/Libraries/hex-arith.md`: callers should reason through stable Nat-view
and reconstruction lemmas, each helper should have both a Lean logical body and
a C extern, and callers needing both halves of the same product should use
`UInt64.mulFull` rather than separate low/high computations.

This is a review-only Phase 6 slice. It does not edit Lean or C source.

## Overall Assessment

`HexArith/UInt64/Wide.lean` is close to Phase 6 quality. The public operations
have clear logical bodies and matching externs:

- `UInt64.mulHi`
- `UInt64.mulFull`
- `UInt64.addCarry`
- `UInt64.subBorrow`

The theorem surface is also broadly well-shaped. `toNat_mulHi`,
`toNat_mulFull`, `toNat_mulFull_fst`, `toNat_mulFull_snd`,
`mulFull_eq_mulHi_mul`, `mulFull_snd_add_fst`, `toNat_addCarry`, and
`toNat_subBorrow` let downstream proofs move to exact Nat arithmetic without
unfolding executable bodies. Component lemmas for carry and borrow bits are
tagged for automation, and `HexArith/Conformance.lean` covers the intended
overflow and underflow edge cases.

The C extern contract is present and direct: multiplication uses
`__uint128_t`, `mulFull` computes both halves from one wide product, and
carry/borrow use compiler overflow builtins. The extern names match the Lean
declarations, and the source is part of the existing `hexarithffi` extern
library.

## Findings

### 1. Montgomery context still computes two-word products through split calls

`HexArith/Montgomery/Context.lean` defines:

```lean
def toMont (ctx : MontCtx p) (a : UInt64) : UInt64 :=
  redc ctx (UInt64.mulHi a ctx.r2) (a * ctx.r2)

def mulMont (ctx : MontCtx p) (a b : UInt64) : UInt64 :=
  redc ctx (UInt64.mulHi a b) (a * b)
```

This is semantically correct, but it violates the SPEC guidance for callers
that need both halves of the same product. These definitions perform a wrapped
low multiplication plus a separate `mulHi` extern call instead of destructuring
`UInt64.mulFull`.

Filed as #6167:

`HexArith Phase 6: route Montgomery context two-word products through mulFull`

Suggested deliverable: refactor `toMont` and `mulMont` to destructure
`UInt64.mulFull`, and update the local bounds/projection proofs to use
`toNat_mulFull_fst`, `toNat_mulFull_snd`, or `mulFull_snd_add_fst`.

### 2. REDC proof lemmas expose a split-call view after the executable uses `mulFull`

`HexArith/Montgomery/Redc.lean` correctly implements `redc` with:

```lean
let (mhi, mlo) := UInt64.mulFull m p
```

However, `redc_u_spec` states the carry-chain theorem using
`UInt64.mulHi m p` and `m * p`, and `redc_sub_spec` immediately rewrites
`UInt64.mulFull m p = (UInt64.mulHi m p, m * p)`. This is a proof-quality
gap rather than a runtime bug: downstream proofs are still encouraged to reason
through the old split representation instead of the executable `mulFull`
components.

Filed as #6169:

`HexArith Phase 6: expose REDC carry-chain lemmas in mulFull form`

Suggested deliverable: add or refactor REDC helper lemmas so the main
carry-chain specification is stated over the `mhi`/`mlo` pair obtained from
`UInt64.mulFull m p`, while retaining any split-call bridge as a compatibility
lemma if existing proofs need it.

### 3. Reconstruction lemmas are useful but under-annotated for automation

The file has good reconstruction theorems:

- `mulHi_mulLo`
- `mulLo_add_mulHi`
- `mulFull_snd_add_fst`
- `toNat_addCarry`
- `toNat_subBorrow`

Only the component projections and bit characterizations are currently tagged
for `simp`/`grind`. Current consumers call the reconstruction lemmas manually,
especially in `HexArith/Montgomery/Redc.lean`. That is reasonable in long
proofs, but Phase 6 should audit whether conservative `@[grind =]`
annotations on the reconstruction equalities let Barrett/Montgomery proofs
avoid boilerplate without causing search blowups.

Filed as #6168:

`HexArith Phase 6: tune automation for UInt64 wide-word reconstruction lemmas`

Suggested deliverable: test `@[grind =]` on the reconstruction lemmas above,
keep only annotations that reduce current proof boilerplate without loops, and
add small local checks in the affected files or conformance layer.

## Checked Clusters With No Follow-Up Needed

- Public declarations in `HexArith/UInt64/Wide.lean` have docstrings. The
  private quotient-bound helper also has a docstring because its role is not
  obvious from the name.
- Namespace hygiene is clean: the file lives in namespace `UInt64` and imports
  only `Std`.
- `Barrett/Reduce.lean` uses `UInt64.mulHi` appropriately. Barrett reduction
  needs only the high word of `T * pinv`; it does not need both halves.
- The C externs match the Lean logical bodies and use a single `__uint128_t`
  multiply for `mulFull`.
- Conformance checks cover wide products crossing the `2^64` boundary,
  carry/no-carry addition, borrow/no-borrow subtraction, and optimized
  Barrett/Montgomery consumers.

## Phase 6 Readiness

The wide-word API surface itself is solid, but `HexArith` should not treat this
slice as fully polished until the Montgomery consumers are aligned with the
`mulFull` contract and the reconstruction automation audit is complete.
