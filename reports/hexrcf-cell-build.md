# Native construction of supplied complete cells

The optional RCF adapter can construct a complete derivative root table and
all section/ordinary-sector row packets using the existing family producers.
The caller still supplies an authenticated parent and proposed ordinary points.
Construction emits proposals; the independent readers and ordinary-kernel
acceptance remain the proof boundary.

## Root construction

[RootBuild](../adapters/HexRCF/RealCoefficients/RootBuild.lean) retains the actual checked full derivative tree and exact
owner extraction equation. Domain failures and internal `BuildError` values
remain distinct. `from_production` proves that its root list is precisely the
owner producer's list. `success` consumes the owner's actual total enumeration
theorem: for a lawful ordinary-real parent model and a squarefree interpreted
head, construction returns a complete `RootReplay.Result`. Squarefreeness is
an explicit mathematical domain requirement. The existing radical construction
establishes it for a carrier before root production; the wrapper does not infer
it from polynomial array length or erase repeated roots.

`RootBuild.prepare` composes actual radical progress with complete root
construction. `prepare_success` derives a returned packet and the original
input's literal radical check from its nonzero input and lawful model; neither
squarefreeness nor a chosen carrier/root list is an extra premise.

## Rows and ordinary points

[CellBuild](../adapters/HexRCF/RealCoefficients/CellBuild.lean) provides
`prepare`, which preflights original guards before source specialization,
radical reduction and complete root production. Its `prepare_success` derives
both construction and the radical check for every shared formula: the common
product omits zero factors, so zero and repeated atoms require no additional
nonzero-product premise. `build` preflights all original supplied divisors before specializing
or producing any row. It constructs each full section row, both applicable
strict adjacent-boundary rows for every ordinary sector point, the point's
linear count-one descriptor and its complete formula row. Infinite boundaries
retain null fields. An incorrect ordinary point fails with `.boundary`;
producer and descriptor failures retain their original structured causes.
Nothing short-circuits on a true matrix or removes false cells.

`RowEncode.packet` uses the owner's existing `SignEvidence.ofSigns` and codec.
`read_covered` proves that the shared operation-parametric reader recovers the
exact encoded checked row under finite predecessor coefficient/context codec
coverage. It does not assume a globally lawful predecessor codec or construct
a native algebraic context during proof checking. It also does not manufacture
the finite coverage evidence.

## Integration and limits

The [conformance driver](../conformance/HexRCF/CellBuildConformance.lean) specializes X²−sqrt2 over the selected positive Q(sqrt2)
parent, builds the radical carrier, complete roots and every cell row, freezes
their graphs, and independently reads and checks them. The newly produced
root graph, section array and sector array match the existing kernel-checked
algebraic fixture byte for byte. The points -2,0,2 are explicit proposals.
Controls retain the false universal verdict and refuse a zero original divisor,
an incorrect exterior point and an invalid zero carrier domain. Zero-atom true and false constant matrices exercise empty-root carriers and
both strict quantifiers while retaining original guards. The new construction
and row-round-trip theorem axioms are checked directly.

The existing fresh original-source quotations still consume independently
checked frozen data and exclude native producers. A compiled successful test
is not new proof evidence. No new root/sign algorithm, formula representation,
field instance, fixture, handler, CI job or owner-library proof is introduced.

This does not discover ordinary points in arbitrary parent fields, authenticate
general source/provider/context history, assemble arbitrary reached scalar
records, transport every live object after refinements, repair automatic
common-field certification or prove general frontend accepted completeness.
The supplied-operation interface's documented native fallback for arbitrary
missing predecessor records remains; this is not a strict arbitrary-packet
compiled checker. Native infinitesimal histories still require the actual
joint finite-realization obligations. #10358 remains open for that full scope.

## Validation

The [source-bound record](data/hexrcf-cell-build/context.json) retains the full
adapter/conformance/manual build at `beeee8b24b` (14,678 jobs), the focused
construction check, all seven structural checks, 623 admission cones covering
1,523 local modules and eleven scanner regressions. All five new construction
and row-encoding theorems have exactly the standard three axioms. No admission
is accepted.

A manual-only layout correction at `74b835299f` shortens qualified names through
namespace opens. The complete manual build (14,255 jobs), fresh rendering
(14,257 jobs) and final browser checks pass after that correction. All six
final desktop/narrow captures were opened and inspected; the earlier narrow
overflow and failed checks are retained separately. The [narrow API example](data/hexrcf-cell-build/construction-cell-narrow-source.png)
fits its code block. Target-level overflow checks make no claim about unrelated
content elsewhere in the full manual.

Every own build shares one 32GiB cgroup, no swap and two Lean workers. The full
build's recorded peak was12G. These are operational validation observations,
not performance, scaling or speedup evidence. The final record binds both
source versions rather than attributing the earlier full build to the later
manual source. No implementation changes follow the full build.
