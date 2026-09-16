# Proposal: kernel-efficient population count for Nat and BitVec

## Recommendation

Add a total `Nat.popcount : Nat → Nat`, with a transparent Lean definition and
proved bit-count equations, plus a native runtime implementation and a kernel
literal reduction rule. Keep `BitVec.cpop` as the public bitvector operation,
implemented through the same Nat operation. The API spelling is provisional.

This is a proposal, not an implemented primitive or a measured speedup.
The current Lean source has no Nat popcount primitive. Its `BitVec.cpop`
uses `cpopNatRec`, visiting every position up to the declared width.
The inspected source is the tree underlying
[lean4#15167](https://github.com/leanprover/lean4/pull/15167).

## Reuse the existing proof work

Bhavik Mehta's [PrimeCert #156](https://github.com/b-mehta/PrimeCert/pull/156)
already supplies `popc64K`: a fixed sequence of shifts, masks, additions and a
multiplication. Its proof establishes agreement with the sum of the low bits
for `v < 2^64`, with intermediate lemmas for arbitrary byte widths. Reuse and
credit that work. A Lean-core port must replace the Mathlib `Finset` and tactic
dependencies with core proofs; it cannot import that file verbatim into `Init`.

Expose useful equations independent of the implementation:

```text
popcount 0 = 0
popcount (2*n + b.toNat) = popcount n + b.toNat
popcount n ≤ n
popcount (n % 2^k) + popcount (n / 2^k) = popcount n
popcount n ≤ k, when n < 2^k
```

The binary equation uniquely describes the intended count. The split equation
connects word chunks to the arbitrary-precision operation. A portable Lean
fallback can process masked 64-bit chunks with `popc64K`, using direct recursors
and a proved finite fuel bound. Always mask before using the word theorem.
Do not generalize its final 8-bit sum to an unbounded integer: that would wrap
once the count exceeds 255.

## Runtime and kernel implementation

Add the operation to the existing Nat runtime interface and to the unary-literal
case in `src/kernel/type_checker.cpp`. Reduce only when the argument reduces
to a Nat numeral; symbolic inputs retain the Lean definition and theorem API.
A runtime `@[extern]` or compiler rewrite alone does not speed up kernel replay.

Use a portable word popcount for small Nats and an allocation-free scan of
big-integer limbs for large Nats. GMP's `mpz_popcount` is a candidate for its
backend; the non-GMP backend needs the equivalent limb loop. Do not narrow the
result through `unsigned`, especially on Windows. Use a Nat conversion that
preserves the backend count's full width, with an explicit bound or checked
accumulation. Inputs are nonnegative, so GMP's negative-number convention is
irrelevant. Return zero for zero.

The intended arithmetic cost is linear in the number of stored limbs. Merely
shifting a giant Nat right by 64 repeatedly copies successively shorter big
integers and can accumulate quadratic work. A recursive Lean chunk loop is a
useful portable fallback and comparison arm, not evidence of limb-linear cost.

This extends the trusted kernel reduction code, just as existing reductions
for Nat arithmetic do. Keep the extension small, retain the transparent
specification, and review the correspondence explicitly. No new axiom or
compiler-trusted proof rule is involved, but the C++ reduction is trusted.
If maintainers prefer no new kernel primitive, ship the proved word/chunk
implementation first and measure its remaining overhead.

## BitVec integration

Prove the bridge to the existing recurrence, then define `BitVec.cpop x` using
`Nat.popcount x.toNat` and `BitVec.ofNatLT`. The simple bound `popcount n ≤ n`
composes with `x.isLt` to supply the constructor proof for every width,
including zero. This avoids an unnecessary `% 2^w` through `BitVec.ofNat`.
In particular, a very wide vector containing only a small value should not
force a scan of its leading zeros or construction of a huge modulus merely
to package the count.

Retain `cpopNatRec` and its public equations as specification lemmas. Establish
`x.cpop.toNat = Nat.popcount x.toNat`, preserving current `cpop` result width
and zero-width behavior. Update proofs that currently unfold the old definition.
Preserve the existing `bv_decide` cpop reflection and circuit semantics, and
test the BitVec simplifiers and `grind` propagator as well as kernel reduction.
No second BitVec kernel primitive should be necessary.

## Evidence and acceptance

Compare the current BitVec recurrence, a proved 64-bit chunk fallback, and the
new primitive. Measure native execution and direct `Kernel.check` separately;
also measure complete `decide +kernel` proofs. Put imports, input construction,
and independent reference calculation outside the direct-check timer. Use
fresh checks, incorrect-result controls, adjacent AB/BA blocks, automatic CPU
affinity, and retain every completed sample. Plain `decide` is a compatibility
test, not the performance target.

Test zero; every input below `2^16`; single bits; dense, sparse, and mixed
inputs; and boundaries around 8, 32, 64, 128, 256, 4096, and 65536 bits.
Include counts above 255 and multiple machine limbs. Exercise tagged-Nat
boundaries and both GMP/non-GMP backends. Test BitVec widths 0 and 1, non-word
widths, all-ones vectors, and very wide vectors holding zero or one. Include
symbolic `bv_decide` examples, not just concrete numerals.

Use an independent bit-by-bit reference for differential tests so the primitive
does not serve as its own oracle. Require arbitrary-input Lean proofs for the
fallback and BitVec bridge. Small correctness cases belong in the existing CI
jobs; the larger performance sweep belongs in a standalone reproducible
artifact. Numerical performance targets should follow measurement.

## Suggested PR sequence

1. Core Nat API, proofs, and portable fallback, adapting PrimeCert #156.
2. Runtime and kernel literal reduction, with backend tests and direct timings.
3. BitVec integration and preservation of `bv_decide`, `simp`, and `grind`.

These can share one design discussion while keeping each code review focused.
