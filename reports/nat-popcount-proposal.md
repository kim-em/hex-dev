# Proposal: kernel-efficient population count for Nat and BitVec

## Recommendation

Add a total `Nat.popcount : Nat → Nat`, with a transparent Lean definition,
proved bit-count equations, and a native runtime implementation. Keep
`BitVec.cpop` as the public bitvector operation, implemented through the same
Nat operation.

[Draft lean4#15176](https://github.com/leanprover/lean4/pull/15176) implements
this design. Kernel reduction evaluates proved parallel counting using existing
Nat operations, following the approach of
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

The binary equation uniquely describes the intended count. The implementation
first replaces every byte of the whole integer by its bit count. Masked shifts
and additions combine adjacent lanes until the lane base minus one exceeds
the maximum total count. Taking the remainder modulo that value sums the
lanes exactly. The proof tracks the original bit width represented by each
lane, excludes carries between lanes, and preserves the total through pairing.

Inputs up to 248 bits use precomputed byte masks. Specialized paths cover
256 and 4096 bits with 16-bit lanes, and 65536 bits with 32-bit lanes. A
structurally recursive fallback doubles the input-width bound and combines
lanes as necessary. Its fuel bound and correctness theorem cover arbitrary
natural numbers.

## Native implementation and kernel reduction

Add the operation to the existing Nat runtime interface. Use a portable word
popcount for small Nats and a scan of big-integer limbs for large Nats, with
GMP and non-GMP implementations. Avoid narrowing the result through `unsigned`,
especially on Windows; checked accumulation must preserve its full width.
Return zero for zero.

The native arithmetic cost is linear in the number of stored limbs. Kernel
reduction applies shifts, masks, additions, division and remainder to the
whole integer. The `@[extern]` implementation accelerates compiled calls;
the transparent Lean body determines kernel replay performance. Its
correctness follows from the binary counting equations and the proved
bytewise algorithm. The kernel's trusted reduction rules remain unchanged.

[Standalone measurements and reproducers](https://gist.github.com/kim-em/c308db93be8966f18bc2b68c1daddecf)
compare a PrimeCert-style 64-bit word reference, the transparent whole-integer
implementation, and native execution. They include intermediate operand sizes
and inputs through one million bits. Larger performance experiments remain
outside CI.

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
The same transparent Nat implementation serves BitVec kernel reduction.

## Evidence and acceptance

Compare the BitVec recurrence, the 64-bit word reference, and the transparent
Nat implementation. Measure native execution and direct `Kernel.check` separately;
also measure complete `decide +kernel` proofs. Put imports, input construction,
and independent reference calculation outside the direct-check timer. Use
fresh checks, incorrect-result controls, adjacent AB/BA blocks, automatic CPU
affinity, and retain every completed sample. Plain `decide` is a compatibility
test, not the performance target.

Test zero; every native input below `2^16`; single bits; dense, sparse, and mixed
inputs; and boundaries around 8, 32, 64, 128, 248, 256, 496, 4096, and 65536 bits.
Include counts above 255 and multiple machine limbs. Exercise tagged-Nat
boundaries and both GMP/non-GMP backends. Test BitVec widths 0 and 1, non-word
widths, all-ones vectors, and very wide vectors holding zero or one. Include
symbolic `bv_decide` examples, not just concrete numerals.

Use an independent bit-by-bit reference for differential tests so the implementation
does not serve as its own oracle. Require arbitrary-input Lean proofs for the
parallel counting algorithm and BitVec bridge. Small correctness cases belong in the existing CI
jobs; the larger performance sweep belongs in a standalone reproducible
artifact. Numerical performance targets should follow measurement.

## Review scope

The draft PR includes the Nat API and proofs, native runtime implementation,
BitVec bridge, and literal evaluation through `simp`, `seval` and `sym`.
Correctness regressions belong in the existing test harness; performance
reproducers are attached separately.
