# Frozen whole-matrix quotation at a selected real point

The optional adapter exports [`FiniteSigns.check`, `check_domains`, `check_sound`](../adapters/HexRCF/RealCoefficients/FiniteSigns.lean)
and `check_false`, and the source quotation entry
[`FiniteQuote.finish`](../adapters/HexRCF/RealCoefficients/FiniteQuote.lean).
The joint query list puts the original divisor constants before every atom
polynomial. Actual owner descriptor/replay laws interpret the complete list
at one ordinary point. Strict row evaluation rejects missing and extra signs.
A false row describes that point; it does not refute an existential goal.

Quotation freshly translates the source, checks its exact formula and fixed
coefficient valuation, authenticates every original divisor in order, derives
its nonvanishing with an ordinary-kernel proof, and checks the final proof
against the original goal. Exceptions restore environment/metavariable state.
The source equivalence is unconditional, so guard protocol proof terms need
not occur in the final theorem body. They remain required quotation checks.
The checker's leading types/operation instances are retained in semantic-law
applications. Constructor congruence avoids a stuck derived indexed formula
equality decision; dependent indices must be definitionally equal.

The fixed positive-√2 parent and the selected root of X²−√2 consume the owner's
actual `Element.denote` laws, `Descriptor.root_unique`, finite descriptor and
joint replay interfaces. Their semantic premises are proved, not assumed.
Canonical `RepresentationSpecialize.prepare_eval` binds all atom evaluations;
no hand-written matrix normalization theorem or earlier existential witness
is supplied. The source goals include the ordinary three-atom sentence and a
source retaining `x/(2-1)` before normalization.

The [frozen packet](../conformance-fixtures/HexRCF/finite-matrix.json) supplies 31 scalar facts, 43 packing records and 21 stored-sign
records. Constructor rendering shares literal subtrees. Every record's actual
reader conversion and rebuilt checker decision passes active kernel producer
diagnostics, including a required reader-unfold tripwire. Parent construction and earlier opaque
semantic theorems are outside these per-declaration reduction diagnostics. A pre-existing
`decide +kernel` auxiliary is not treated as evidence that its decision ran
under that guard. [Fresh source bodies](../conformance/HexRCF/FiniteMatrix/Ordinary.lean) receive separate ordinary checks,
exact three-axiom audits and all-project type/body dependency scans; upstream
packages are leaves. The dependency scans exclude the named earlier source theorems and cross-use
of the two quoted source theorems. They enforce that provenance, not
executed-work or producer-exclusion claims.

The owner replay dictionaries are an ordinary-kernel assembly interface.
Compiled execution can compute a missing record through the owner's native
implementation. Missing packing/sign controls therefore test that kernel
reduction does not reach a Boolean and the declaration is refused with
`declTypeMismatch`; resource errors propagate. Malformed packets, mismatched
guard modes and missing coefficient facts have literal `none` refusals.
This fixture reader is not a strict compiled checker for arbitrary packets.

The [emitter](../conformance/HexRCF/FiniteMatrix/Emit.lean) round-trips checked upper graphs and packing/sign records through
the owner codecs and regenerates only rational scalar graphs. It does not
independently regenerate the packing inventory or upper joint graphs.

No owner source, formula AST, raw field instance, base umbrella dependency,
AGENTS.md, PLAN.md or CI job is changed. The adapter remains an optional import.
General source/provider/context history, all-live transport, complete supplied
root/cell coverage, automatic common-field certification and accepted
algebraic completeness are outside this tranche and remain required by #10358.
The #10633/#10634 fixed-field improvements and their measurement limits remain
unchanged. No timing, scaling, whole-tactic or general speedup claim follows
from this fixed packet.

The source validation at `9406f0c2b4994ad593d3fe773bd52cc1c4a7cc13` passes
14,584 Lake jobs for the optional adapter, all conformance and the complete
manual. The fresh source audit originally took 136 seconds; a five-second
profile (496 samples, zero lost) attributed most sampled work to repeatedly
converting the environment module list. Retaining that list once preserves
the audit and the next affected build reports 6.6 seconds. These are
source-distinct shared-host observations, not a controlled speedup study.
The same correction is applied to the previous nested audit. All completed
build logs remain retained; no sample is discarded on host-activity grounds.

The regression is runnable with:

```sh
lake build HexRCF.FiniteMatrix.Ordinary HexRCF.FiniteSignsConformance
python3 scripts/rcf/selected_literals.py --check
HEX_RCF_FINITE_MATRIX_OUTPUT=/tmp/hex-rcf-finite-matrix.json \
  lake build HexRCF.FiniteMatrix.Emit
```

The optional emitter writes only when that target is elaborated, so use a
fresh build directory or remove that target's build output to reproduce the
file. Compare parsed JSON; whitespace is not part of packet identity. The
retained source packet is compact JSON. The ordinary target checks proof
acceptance independently of compiled emitter output.

The [validation manifest](data/hexrcf-finite-matrix/context.json) binds selected
source bytes, archived and decoded log hashes, and the render/browser drivers.
Its first full-integration record names the earlier source commit separately.
[Audit observations](data/hexrcf-finite-matrix/audit-observations.json) retain
the exploratory profile summary and both successful and failed surrounding
build records with their limits. These records are separate from proof evidence.

After merging current upstream main, source
`a6162bab8c27b138b528d9d646d443e2e8ec02f2` also passes the complete 14,584-job
integration. The current new-module quotation, refusal and fresh ordinary audit
finish successfully. The retained archive distinguishes this source from the
first full integration.

Full HTML rendering passes 14,192 Lake jobs. The retained desktop/narrow
captures and [inspection record](data/hexrcf-finite-matrix/inspection.json)
show the changed paragraphs within their 752-pixel and 343-pixel content
widths. The final narrow code example and desktop source captures were inspected.
The driver checks the code-block element and descendant overflow as well as
paragraph widths. This
checks the added section; it makes no whole-page overflow claim.

The quotation API checks divisor order by indexed identities. This fixed
packet exercises that interface with one unit divisor; it does not exercise
multiple-divisor permutations or a nontrivial algebraic guard sign.

The reviewed source `3c5c17ce18d98965ffafe4c7472e558c9dee25c4` passes
14,585 integration jobs. The final source
`0776d8e68f884fe5c0cf74f2a0630b38e1f3c0b8` additionally passes the 11,788-job
affected quotation/audit/manual build and the 14,192-job full HTML render.
It pins the comparison, polynomial-leaf and guard-count failure messages,
checks both diagnostic tripwires negatively, and excludes cross-use of the
quoted source theorems. The admission scan covers 528 cones and 1,425 modules;
all eleven scanner tests pass. The
[earlier manifest and captures](data/hexrcf-finite-matrix/before-review/context.json)
retain their own bytes and source bindings. The current manifest supplies
per-source hash maps for each integration record.
