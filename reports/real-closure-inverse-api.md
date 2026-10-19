# Supplied inverse proof and API review

This review covers the supplied-equation interface in
[InverseEquation](../HexRealClosure/InverseEquation.lean), its
[field semantics](../adapters/HexRealClosureMathlib/InverseEquation.lean) and
[finite-point semantics](../adapters/HexRealClosureMathlib/SuppliedInverse.lean).
The [native inverse record](../HexRealClosure/InversePacking.lean) is the
comparison boundary. This is a declaration review of this interface, not a
Phase-6 attestation for the whole library pair.

The existing `InverseFact` dictionaries, `Element.replayInverse`,
`Element.replayQuotient` and `Inverse.realize_many` consume native `Inverse`
records. An `Equation` proves a value equation at a selected point, not the
stored-element equality supplied by `Inverse.native`. It cannot replace the
stronger record in these interfaces.

## Computational declarations

| Declaration | Assessment |
| --- | --- |
| `Packing.Inverse.Equation` | The private constructor binds the actual operand and the joint signs of its polynomial and the residual `operand · output - 1`. A nonzero cached operand sign and the observed signs are explicit. The type intentionally carries no equality with the native inverse candidate. The output remains indexed by its original packing record and context. |
| `Equation.make?` | Checks precisely the cached nonzero sign and the supplied selected-sign values. Selected signs already carry their checked root/query bindings. No sign producer, gcd or candidate computation occurs here. This is a checker for supplied evidence, not the native inverse producer. |
| `Equation.make?_argument` | Successful construction retains the operand literally, rather than merely preserving its value. The successful-return premise is appropriate for a checker projection. |
| `Equation.make?_self` | Rechecking any retained record returns the same full record. This characterizes reconstruction without asking consumers to unfold the private constructor. It does not prove production of the signs for arbitrary inputs. |
| `Equation.readMemo?` | Reuses `SelectedSigns.readMemo?` on the exact retained root and two queries, then uses `make?`. Its memo index is checked by that reader; the stored operand and output are not replaced by equivalent representatives. |
| `Equation.readMemo?_argument` | Exposes literal operand retention through the memo reader, including its cached tag. The proof factors through the checker projection. |
| `Inverse.toEquation` | Forgets the stronger record's literal candidate equality while retaining its nonzero operand and checked equation. It does not change the packing output or construct a new inverse. |
| `Inverse.toEquation_argument` | A short normalization lemma makes operand retention available to `simp`. |
| `Inverse.toEquation_evidence` | A separate normalization lemma preserves the actual replay evidence, not merely its query values. It supports conversion of finite replay premises without unfolding either private constructor. |

## Semantic declarations

| Declaration | Assessment |
| --- | --- |
| `Equation.eval_inv` | Uses an arbitrary coefficient reader with zero/unit preservation, reached multiplication and subtraction relations, and the two observed signs at a supplied point. The nonzero operand follows from its retained sign. The product-minus-one equation gives the field inverse. No globally lawful coefficient embedding or real-closedness premise is imposed by this theorem. |
| `Equation.denote_inv` | Proves the law at the descriptor's selected root under the explicit predecessor interpretation laws, sign agreement and an ordered real-closed target. This is the whole-interpretation alternative to reached finite premises. It does not assert native candidate equality. |
| `Equation.Data` | Keeps original packing replay/subtraction separate from the inverse replay and its reached product/subtraction relations. Both concern the same indexed output and reader. This proposition supplies semantic premises; it is not an executable exporter. |
| `Inverse.Data.toEquation` | Converts the stronger native record's finite premises while preserving its original packing and replay evidence. The public conversion lemmas avoid dependence on private representation details. |
| `Equation.atPoint` | Requires an ordered real-closed target and uses the same `Context.finitePoint` as the other finite inventories. Descriptor data selects that point; packing data proves the original packing equation; inverse replay gives the observed signs. The inverse law additionally uses the reached product and subtraction relations. The conjunction retains the packing equation, inverse law and both cached signs. No separate existential root can replace this point. |

The names put the distinction in the `Inverse.Equation` namespace. The reader
and characterizing lemmas have source docstrings; the data fields are explained
beside their manual reference. Semantic declarations stay in the Mathlib layer.
`import HexRealClosure` exports the computational interface. The semantic
imports `HexRealClosureMathlib.InverseEquation` and
`HexRealClosureMathlib.SuppliedInverse` belong to the development
`HexQuerySemantics` target under `adapters/`; the base companion umbrella does
not export them, and this review does not change their publication boundary.

## Evidence and remaining acceptance

The source modules guard the ordinary-kernel axioms of the projection,
reconstruction and semantic laws. Their expected sets contain only `propext`,
`Classical.choice` and `Quot.sound`. Building the changed chapter also builds
these guards. The manual references the actual public declarations and
describes both the whole-interpretation and reached-data interfaces.

The existing [inverse packing controls](../HexRealClosure/InversePackingTests.lean)
exercise both readers on monic and scaled non-monic reducible defining polynomials.
They check native-candidate rejection alongside supplied-equation acceptance
of an alternate original polynomial. In the non-monic case the packed
representatives also differ. Supplied-reader controls reject an incorrect
inverse, changed operand, wrong root domain, out-of-range index and zero
operand. Independently accepted sign observations expose the nonzero residual
of the bad inverse and the zero operand's product-minus-one residual.
Most reader rejections occur in the selected-sign or memo checks, before
`Equation.make?`; the bad-inverse and zero-operand controls also call `make?`
directly. The zero operand's nonzero residual causes the observed-sign check to
fail, so these controls do not isolate its separate cached-nonzero guard. The
controls also reject a repeated-factor descriptor before inverse arithmetic
and check that neither private constructor is accessible. The Lake test target
includes this module; this review reuses it rather than creating a second test
owner.

The existing native `Inverse.atPoint` proof in
[FinitePoint](../adapters/HexRealClosureMathlib/FinitePoint.lean) derives the same
four-part conclusion as conversion followed by `Equation.atPoint`.
Consolidation is an API-polishing follow-up: `SuppliedInverse` currently imports
`FinitePoint`, so direct reuse in the reverse direction would introduce an
import cycle. Any consolidation must preserve the public imports and the
reached-data hypotheses. The native `Inverse.eval_inv` already delegates to
`Equation.eval_inv` through conversion.

The reached-data theorems require supplied descriptor, replay and arithmetic
premises. Automatic recursive construction of those premises through
interleaved algebraic/infinitesimal stages is a separate acceptance requirement.
The native inverse producer's totality is also a distinct contract, proved by
its native production laws under their interpretation and exact-key premises.
Neither a supplied equation nor `make?_self` discharges that producer contract.
Original expression-divisor guards remain with the expression consumer.

No computational implementation changes or new timing measurements accompany
this review. Full library phase acceptance, integrated conformance and the
[publication requirements](real-closure-publication.md) remain separate.
