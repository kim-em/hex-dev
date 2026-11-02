# Quoting functions with proof inputs

Complete literal packet quotation reached an `Except.rec` continuation whose
type takes a `Nat.hasNotBit` proof and returns `Option Unit`. The previous
transport accepted proof arguments and independent data, but refused this
function because its argument proposition depended on the changed subject.

`RootQuote.proofFunction?` retains the original function and transports only
its proof input using `congrArg` and `Eq.mpr`. The generic equation is checked
with an abstract subject before the concrete subject and its checked equation
are supplied. It does not cast the returned data or evaluate the replay to
justify the transport. Both the generic and instantiated proofs pass the
ordinary kernel.

The supported function has one proof input and a result type that reduces to
a type independent of the changed subject and equality. A function returning
an indexed `Fin` remains unsupported, as does the existing direct dependent
data case. These refusals retain the caller's declaration and metavariable
state. No exception selects a different solver.

Two public readers exercise the function before and after a trailing equality
proof. Their retained results are 7 and 29, respectively. Their direct generated
proofs have no axioms and consume 1,079 and 1,099 proof nodes. The existing
control loop also checks exact and one-below budgets and caller expression/level
metavariable restoration. A fresh ordinary public module imports and uses both
equations. The actual-body audit checks 145 theorem bodies, 16 definitions and
88 nonempty traces with the unchanged native-producer guard; its complete
transitive axiom closure is `[propext]`.

This is an adapter quotation capability, not complete-cell tactic support.
The continuing full-packet experiment additionally needs a literal polynomial
and complete checked arithmetic data. No acceptance theorem from the older
fixture is counted as a new reduction proof. Frozen source/provider/predecessor
history, complete-cell frontend integration and the remaining #10358
requirements remain separate obligations.

All local Lean/Lake/browser processes run serially under aggregate 32 GiB,
no swap and two Lean threads. Validation counters and build observations do
not establish scaling, physical sharing or a speedup.

The affected compatibility and full manual build passes 14,371 jobs in
13m57.795s, peak 4.5 GiB/no swap, with reused dependencies. Existing primitive,
rational, public packet, actual-codec dependent reader, header and context
audits retain their checked inventories and budgets. This is a build
observation across several workloads, not an isolated proof timing or a
matched performance comparison.

The root-table conformance checks 94 theorem bodies and 14 definitions; the
assertion and manual match that observed inventory. Its targeted build passes
in 32.730s with peak 1.8 GiB. The full HTML render passes in 12.798s with peak
1.5 GiB. Six visually inspected desktop/narrow captures show the changed
paragraph and example without local overflow; existing whole-document
horizontal overflow is outside that claim.

The [source-bound record](data/hexrcf-proof-functions/README.md) retains the
validation, captures and development failures. Full-packet experiments quote
their literal polynomial in 1,893 proof nodes, but exhaust their enclosing
100,000- or 5,000,000-node budgets. Retaining polynomial/certificate data did
not resolve that cost. A smart-unfolding experiment was explicitly interrupted
and is not a passing sample. These failures do not trigger another solver.
