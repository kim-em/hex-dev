# Exact positive quotient bounds

For bounds with a nonnegative numerator and a positive denominator, the native
implementation computes the exact lower and upper quotient extrema using two
rational divisions. Other signs retain the original four corners and separation
guard. `Bounds.div_eq_impl` proves equality with the original `Bounds.div?` for
**arbitrary** bounds, including every refusal case. The kernel-facing reference
body is unchanged and marked noncomputable; a proved `@[csimp]` twin supplies
native execution. No containment or provider hypothesis is added to this equality.

## Declaration assessment

| Declaration | API/proof decision |
| --- | --- |
| `Bounds.div?` | Preserve the public type, original guard and four-corner kernel reference. Existing correspondence proofs apply unchanged. |
| `inv_le_of_pos` | Private Rat order support. Strict positivity and denominator order are explicit; multiplication by positive reciprocals proves reverse order. |
| `quotient_corners` | Private characterization of the four original corners. The bounds' stored order proofs and explicit sign hypotheses give all four needed inequalities. It supplies the result's order proof and the compiler equality. |
| `Bounds.divImpl` | Public implementation twin required by compiler registration. The fast branch has precisely the hypotheses used by the corner proof; fallback is the original computation. Both paths are native Lean. |
| `Bounds.div_eq_impl` | Public compiler registration, proving whole-operation equality rather than just successful examples or containment. Both data endpoints and `none` are preserved. |

Every added helper is used by the actual compiler replacement or its proof.
All declarations have source documentation; computational imports remain
Mathlib- and Tau-Ceti-free. The existing semantic library, tests and conformance
build in 3,275 jobs. The current native build, including the guarded axiom check,
passes; the theorem has exactly `propext`, `Classical.choice`, `Quot.sound`.
All 122 freshly emitted real fixtures are byte-identical and pass the pinned
FLINT/Z3/exact-Fraction oracle. No new axioms, runtime oracle or `native_decide`
are introduced. Generated C confirms two divisions in the selected branch and
four in the fallback.

## Bounded comparison

The predeclared question is whether this changed source improves the unresolved
approximation case at 12288 by more than 10% against an unmodified parent built
with the same compiler, without a greater-than-10% neighbor regression.
The frozen source is `a7a4930bab6618c3416bb4cc930e2e02a081870e`, retained by
`audit/issue-10575-positive-quotient-input-v1`. The parent is
`7244ae8f3c0c9f7eedc4112f2a2b79b45e2ff1fa` on Lean 4.35.0-rc3.
The earlier fresh parent build is reused unchanged, with all source, pin and
binary bindings rechecked. The unsuccessful constant-enclosure prototype is
not included in this candidate.

| Parameter | Parent median ns/call | Candidate median ns/call | Change |
| --- | ---: | ---: | ---: |
| 10240 | 2,813,846,509 | 1,860,605,648 | −33.876790% |
| 12288 | 4,355,692,698 | 2,871,639,983 | −34.071566% |
| 16384 | 8,620,011,969 | 5,644,654,418 | −34.516861% |

All eighteen arms complete with matching per-parameter hashes and unchanged
inputs. Three trial-major adjacent AB/BA/AB trials use one automatically leased
CPU on the shared host, with the original one-second batching target. No sample
is rejected and no quiet-core condition is imposed. All 36 raw streams and the
complete terminal context are retained. Per-arm medians have three observations;
these host-specific results meet the bounded expansion criterion.

Both builds bind 5,152 source/configuration inputs, 89 native import files and
sixteen identical clean dependency pins. Only `Oracle.lean` changes within the
native import paths; the broader snapshot also changes the test axiom guard.
The candidate executable hash is
`e8634bce8b34b35651fc5f73d249d7f2385370df0a53fa5d9b9b087d0b5d1662`;
the parent is
`0b260f7a83bab62a936c7cbb9a1334f55524ebe94bf366d715fb1378614fdeb5`.
Child Git metadata identifies the invocation checkout; producer commits are
bound separately by the source manifests.

The manifest binds compressed and original bytes. The retained script derives
its result from every completed raw observation. Native executables are not
committed. This is a bounded changed-source diagnostic, **not** the full
historical-baseline comparison and not a fresh Phase-4 scaling attestation.
The earlier four Phase-6 findings and captures remain retained. Final core
acceptance still needs the complete comparison to the required historical
baseline and reconciliation of every remaining finding; no phase or publication
counter changes here.

Verify the archive bindings, complete adjacent-arm schedule, raw observations,
result hashes, source-manifest bindings, medians and bounded criterion offline:

```sh
python3 reports/bench-results/ordered-fn-positive-quotient/replay.py
```

This command collects no timings. It checks the retained evidence; it does not
rebuild the executables or establish a current-source performance pass.
