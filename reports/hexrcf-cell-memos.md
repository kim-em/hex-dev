# Checked row graphs and algebraic source quotation

`RowQuote.withDecoder` shares checked graph validation within one quotation
attempt. It independently parses each packet, binds its exact ordered queries,
and uses the owner's `SelectedSigns.ofMemo?` and `Dag.selectedSigns_memo` to
recover each root's row. Keys retain the actual operations, sign function,
context, head, endpoints and complete graph. Each reused equation is checked
against the exact new reader. Descriptor projections preserve their supplied
operation indices, including operations only propositionally equal to canonical
arithmetic. The cache is local; all work uses the enclosing budget and transaction.

`CellQuote.replayWith` uses that decoder for its existing root, pointwise-cell
and strict-fold stages. No new solver handler, arithmetic producer, field
instance or owner proof is introduced.

The independent source example reconstructs the coefficient polynomial and
checks a complete frozen packet over the retained positive square root of 2.
It authenticates the coefficient and proves the exact original statement
`∃ x : ℝ, x²−√2 ≥ 0 ∧ x²−√2 ≤ 0 ∧ 0=0`. Its proof excludes older complete-packet
acceptance, source and canonical-certificate fixtures. The fixed selected
parent and checked coefficient seed facts remain supplied inputs.

| Fixed input | Charged proof nodes |
| --- | ---: |
| Constant true packet | 441,039 |
| Constant false packet | 441,041 |
| Rational quadratic: two sections, three sectors | 5,911,125 |
| Algebraic source reification and packet quotation | 8,644,422 |

The algebraic count precedes separate source finishing. Both nonconstant
packets record two graph-memo reuses and seven independent validations. Test
limits remain explicit: 16M nodes/24M heartbeats for the rational packet and
24M/60M for the algebraic source. Public defaults are unchanged. These are
charged quotation counts, not unique DAG-node, physical-sharing or matched
timing measurements.

The constant controls retain exact/below limits, wrong-goal proposals, false
verdict separation, malformed cells, original zero-divisor preflight, terminal
provider failures and full caller restoration. The row-entrypoint regression
retains the graph while changing ordered queries; it requires structured
rejection before graph validation and complete metavariable/declaration rollback.

| Fresh actual-body audit | Theorems | Definitions | Nonempty traces |
| --- | ---: | ---: | ---: |
| Constant/rational quotation | 1,246 | 101 | 1,297 |
| Complete original algebraic source | 1,056 | 72 | 1,094 |

Both audits check full transitive axiom closure against the standard three
axioms and retain the producer-reduction guard. The source audit requires
the original-source soundness, cell composition and row transport laws.
No admission or native decision proof is added.

The combined source/audit build passes in 19m37.628s, with an aggregate peak of
4.9 GiB and no swap. Lake reports 894s for the source module and 187s for its importing
audit. This remains expensive fixed-input proof construction. The subsequent
40-target selection, optional umbrella and complete manual pass in 7m42.475s,
peak 7.5 GiB, with cached dependencies reused. This selection is not the entire
default conformance set. The HTML render passes in 24.060s, peak 1.7 GiB; browser
capture passes in 10.916s, peak 2.8 GiB. All ten final 1440px/390px captures were
actually viewed; changed targets have zero local overflow. Pre-existing page
overflow is outside this change. Seven metadata checks pass.

All own Lean/Lake/browser invocations are serial under an aggregate 32 GiB cap,
with no swap and two Lean threads. The actual target invocation and active cgroup
properties are retained. Failed instance/universe and control-setup attempts,
task-only prototypes and available exact inputs are preserved separately.
No compiled replay timing, scaling, general tactic cost or speedup follows.

Generic source/provider/predecessor and frozen-history assembly, complete
tactic integration and accepted algebraic completeness, joint realization,
strict compiled missing-record coverage, practical costs and the remaining
issue conformance/manual/evidence scope remain required. Merged owner fixed
fixtures do not supply arbitrary live/interleaved export. Issue #10358 remains
open; #10331 owns downstream dispatch.

The [source-bound record](data/hexrcf-cell-memos/README.md) pins this implementation.
The earlier [cell quotation record](data/hexrcf-cell-quotation/README.md) remains
immutable and deliberately excludes this later algebraic source success.
