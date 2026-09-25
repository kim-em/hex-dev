# Determinant proof structure and wider comparisons

Wider testing exposes a substantial frontend cost unrelated to the determinant
recurrence: an optional definitional-equality shortcut can unfold concrete ring
arithmetic. On a 4×4 matrix over `ZMod 2`, the direct prototype hits its
10-second process ceiling while Mathlib's declaration completes in 0.570s.
Restricting that shortcut to reducible transparency gives 0.573s against an
adjacent Mathlib median of 0.749s. This is a general conversion change, without
recognition of a ring or matrix family.

The smaller 10×10 rank-one loss is not established as solved. A structural
control makes its Bird certificate exactly identical to Mathlib's, but the
direct before/after timing comparison does not demonstrate a speedup.

These are manual experimental proof probes, excluded from production dispatch,
computational benchmarks and CI timing gates. They neither call `norm_det` as a
fallback nor change the production implementation or normative SPECs.

## The 10×10 investigation

The [preceding comparison](determinant-normalized-comparison.md) found Mathlib
at 4.352s and the direct prototype at 4.549s on the rank-one matrix with entries
`xᵢ * yⱼ` and supplied determinant zero. Both adjacent pairs favored Mathlib.

The [structural diagnostic](bench-results/determinant-wider/inspection/rankone10-difference-corrected/inspection.json)
finds 141,760 unique nodes in each Bird certificate, with identical expression-head
histograms. The first mismatch is the dimension argument: Mathlib retains the
goal's `OfNat.ofNat` expression, while the prototype reifier uses a raw natural
literal. The full proofs contain 143,424 and 143,397 unique nodes respectively.
This is not evidence of a larger arithmetic certificate in the prototype.

`literal_bird` preserves the goal's dimension expression. On this input its
[certificate is structurally identical](bench-results/determinant-wider/inspection/rankone10-literal/inspection.json)
to Mathlib's, not merely equal in size or hash. The full proofs contain 143,424
and 143,394 unique nodes, with 143,372 shared structurally. This result concerns
this input only. Node-head counts include partial applications and are not
counts of arithmetic operations.

The literal control narrowly beats its adjacent Mathlib comparison, 2.369s
against 2.403s, in both pairs. However, the direct comparison of the two prototype
variants gives:

| Same 10×10 input | Direct | Preserved dimension |
|---|---:|---:|
| First adjacent pair | 1.363s | 1.367s |
| Second adjacent pair, reversed order | 1.350s | 1.656s |
| Median | 1.356s | 1.512s |

The first difference is only 4ms; the second is larger and variable. Preserving
the dimension has no established performance benefit, so it remains a control
instead of becoming the default. Absolute clocks vary substantially across
batches; only adjacent arms provide the intended comparison.

The structural diagnostics run Mathlib first and the prototype second in one
module. Their clocks change order across attempts and are not paired performance
evidence. Structural inspection runs after checking, outside declaration clocks,
and can itself be costly. Declaration time minus tactic time includes several
elaboration and declaration-processing stages; it is not a kernel-time attribution.
The cause of the small ordinary 10×10 gap remains uncertain.

## Wider coverage

All ordinary rows use two adjacent AB/BA pairs and complete declaration medians
in seconds, including statement elaboration, proof construction and all kernel
checks. Each stage retains its exact source. Variant labels matter: the literal
control and earlier direct frontend are not measurements of the final patched
frontend.

| Input | Prototype stage | Mathlib | Prototype | Pair evidence |
|---|---|---:|---:|---|
| 4×4 rational quadratic entries, two variables | Original direct | 1.237 | 1.180 | Pairs disagree; inconclusive |
| 10×10 rank one | Preserved dimension | 2.403 | 2.369 | Both narrowly favor prototype |
| 6×6 rational quadratic entries, two variables | Preserved dimension | 14.979 | 14.121 | Both favor prototype |
| 5×5 skew-symmetric, quadratic entries, zero diagonal | Original direct | 1.356 | 1.107 | Both favor prototype |
| 4×4 quadratic entries over `ZMod 2` | Original direct | 0.570, one sample | Process timeout at 10s | Batch stopped |
| Same `ZMod 2` input | Shortcut disabled | 0.713 | 0.520 | Both favor prototype |
| Same `ZMod 2` input | Restricted shortcut, final | 0.749 | 0.573 | Both favor prototype |
| 5×5 Vandermonde, factored target | Restricted shortcut, final | 1.498 | 0.656 | Both favor prototype |

The original direct shortcut used unrestricted `isDefEq left.norm right` before
ordinary target normalization. Disabling only that shortcut, with the same
prototype source hash and mathematical input, removes the characteristic-two
timeout. The retained fix uses `withReducible <| isDefEq left.norm right`:
successful cheap conversion still reuses the certificate, and otherwise the
existing target normalizer supplies the equality proof. This evidence isolates
the shortcut as a substantial cost; it does not attribute every millisecond
of the difference to a specific unfolding operation.

The final restricted variant is timed only on the characteristic-two and
Vandermonde rows. Its broader coverage cannot be inferred automatically from
earlier stages. In particular, 10×10 has not been retimed after that restriction.
There is no new 20×20 measurement or exhaustive search. The rational 4×4 result
is inconclusive, and the retained 10×10 loss still warrants investigation.
The two-pair protocol selects hypotheses; it does not satisfy the six-pair
shipping bar or justify changing default dispatch.

## Retained evidence and limits

Inventories contain every ordinary observation, ranges and exact inputs:
[original rational](bench-results/determinant-wider/direct/inventory.md),
[dimension control](bench-results/determinant-wider/literal/inventory.md),
[direct before/after](bench-results/determinant-wider/assembly/inventory.md),
[wider original frontend](bench-results/determinant-wider/coverage/inventory.md),
[disabled shortcut](bench-results/determinant-wider/no-conversion/inventory.md),
and [restricted shortcut](bench-results/determinant-wider/restricted/inventory.md).

The round retains eight complete paired batches, one partial batch ending in
the timeout, three successful structural diagnostic builds, and two failed
diagnostic builds. There are 33 accepted ordinary timing proofs and six proof
declarations in successful structural builds. The failed diagnostics exposed
two harness errors: reading theorem bodies through `ConstantInfo.value?`, and
using a reserved Lean identifier in the mismatch helper. Their observations
remain archived; failed modules are not successful timing samples.

All fourteen batches total **332.95 seconds (5m33s)**, including diagnostics,
timeouts and harness failures, within the six-minute round allowance. Together
with the earlier recorded experiments, retained measurement time is about
**59m21s**. The runner enforces the reduced allowance across sibling variant
roots, including when a later invocation omits or raises the requested cap.
Every process has a recorded ceiling no greater than 60 seconds; selected
ordinary ceilings range from 9 to 45 seconds. These include imports and build
overhead, so a timeout is not an exact tactic-runtime lower bound. The timeout
stopped its batch; no larger comparable characteristic-two input was attempted.
Retries used a changed shortcut or changed implementation, with separate sources.

Measurements are serial, use the existing automatic CPU lease, retain host
context, and discard no completed sample. There is no memory cap or background
monitoring service. Reproduction instructions and variant definitions are in
the [experiment README](../experiments/Determinant/README.md#normalized-determinant-comparison).

`lake build Determinant.NormalizedAudit Determinant.Inspect` checks the final
experimental implementation. The audit has sixteen accepted theorems and five
false-target rejection examples, including rational coefficients and positive
characteristic. Dependencies are limited to `propext`, `Classical.choice` and
`Quot.sound`; every successful measured result is audited by exact name as well.
The [validation archive](bench-results/determinant-wider/validation/checks.json)
records input equivalence, budget guards and repository checks. The
[replacement proposal](determinant-redesign-proposal.md) incorporates restricted
target conversion as a design constraint, while leaving production selection open.
