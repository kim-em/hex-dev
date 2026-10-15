# Executable complete cells in an ordinary real model

The optional RCF adapter constructs complete typed cell evidence before
serializing it. The existing public `CellDiscover.run` now has an execution
progress theorem: with an actual ordinary-real parent model and nonzero
original divisor values, it returns a packet whose frozen cells are the
constructed rows. For both quantifiers, the typed checker returns a verdict
which is true exactly when the original shared sentence holds at the original
fixed coefficients. This is not yet a general literal-reader or frontend
acceptance theorem.

## One producer and one ordered collector

[CellRead.collectWith](../adapters/HexRCF/RealCoefficients/CellRead.lean)
collects every dependent entry in index order and checks its index before
transport. The existing `collect` reader retains its original binding error;
the native producer uses the same implementation with its own binding error.
No missing entry receives a default record.

[CellBuild](../adapters/HexRCF/RealCoefficients/CellBuild.lean) constructs
sections through the existing selected-sign producer. `bounds` checks the
negative and positive signs at every present adjacent root. `point` constructs
the linear ordinary-point descriptor, checks its actual head binding and
retains the entire source sign row at that point. `evidence` assembles those
sections, sectors and rows only after original guard preflight. `packet`
serializes that data in the established layout; the public `build` composes
those two functions. Serialization invokes no root or selected-sign search.

## Actual execution and original coefficient values

[CellAlignment.sector_vector](../adapters/HexRCF/RealCoefficients/CellAlignment.lean)
retains the exact `SectorRequest.points` return equation. Every coordinate,
cast by the same dimension equality used in `run`, lies in the corresponding
checked open cell. Both rays and an empty root table's whole line use the same
statement. Ordered-boundary agreement follows from the existing source
conversion and full radical/root coverage laws.

[CellExecution](../adapters/HexRCF/RealCoefficients/CellExecution.lean)
proves progress of the actual point, boundary, dependent-collection, typed
matrix and frozen-matrix functions. `CellDiscover.run_success` composes the
actual collection model, coefficient/guard conversion, radical/root
preparation, returned vector and typed production. It returns the public
packet together with its constructed data and exact equality of the frozen
cells. Both quantifier verdicts refer to the original coefficient valuation,
using that same compatible model and the actual typed checker.

No chosen carrier, root list, point function or successful child-sign premise
is added to the discovery theorem. The lawful ordinary-real parent and nonzero
original guards are its explicit domain hypotheses. A false verdict remains
diagnostic rather than a proof of the sentence.

## Kernel proofs and compatibility

The [fresh audit](../conformance/HexRCF/CellExecutionProofs.lean) rechecks all
nine actual executable proof bodies in the ordinary kernel. Its dependency
checks require the real radical, root, selected-sign and collection laws. It
allows only a subset of `propext`, `Classical.choice` and `Quot.sound`.

The [construction regression](../conformance/HexRCF/CellBuildConformance.lean)
checks agreement between the typed API and public JSON output, exact equality
with the existing frozen algebraic fixture, true existential and false
universal verdicts, constant/zero cases and original-guard/exterior refusals.
Fresh algebraic and Boolean source quotations additionally exclude the new
native cell-production functions from their actual proof dependencies.

## Remaining acceptance obligations

Freezing the correct typed data does not establish that a partial coefficient
codec can restore every serialized literal. General literal-reader progress
still needs finite coverage of all raw subjects, graph entries and contexts,
including unreachable entries, together with the actual descriptor and row
round-trip laws. The [existing owner API question](https://github.com/kim-em/hex-dev/issues/10575#issuecomment-6186780276)
identifies the checked descriptor composition without copying owner graph
validation proofs into the adapter.

Native collection history is not a frozen provider/context history. General
source authentication, predecessor inventories, all-live conversion, automatic
common-field certification, strict compiled replay on arbitrary missing
predecessors, frontend quotation/completeness and the remaining infinitesimal
path retain their own obligations. This result supplies no faithful formal
model for arbitrary named constants and infers no independence of separately
registered constants. #10358 remains open.
