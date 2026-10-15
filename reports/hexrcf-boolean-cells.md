# Reusing complete cell evidence across formulas

The optional RCF adapter can reuse accepted section and sector rows when two
formulas have exactly the same ordered list of specialized polynomials. The
comparisons and Boolean structure may differ. Each new verdict is computed by
a fresh strict fold, and each original real goal still needs fresh source and
coefficient authentication. No equivalence between the old and new propositions
is assumed or proved by the data transfer.

## Transfer boundary

[CellReuse](../adapters/HexRCF/RealCoefficients/CellReuse.lean) defines
`CellReplay.Evidence.changeFormula`. Its equality premise covers the entire
`RepresentationSpecialize.prepare` list, retaining zero polynomials, repeated
occurrences and domain-guard atoms in order. It keeps the same full root table,
ordinary sector samples, point descriptors and checked sign evidence.
`changeFormula_row` proves that every section and sector keeps its complete
stored sign row. The implementation delegates query-index changes to the
existing value-preserving `RowOperations.retarget`.

The transfer does not run a reader, producer, approximation or root algorithm.
It consumes already checked typed data. It supplies neither a new radical
certificate nor a proof of a new sentence. `CellReplay.check` still checks all
original supplied divisors and the carrier identities before folding every
cell. `CellQuote.finish` still authenticates the freshly reified original
formula, fixed coefficient valuation and ordered original-divisor identities.
Changing polynomial order requires new row evidence unless the entire ordered
specialization lists are proved equal.

## Algebraic comparison and Boolean controls

[Boolean](../conformance/HexRCF/CellReplay/Algebraic/Boolean.lean) reuses the
[complete algebraic matrix](hexrcf-algebraic-cells.md) for
p(x) = x²−√2 over the selected positive ℚ(√2) parent. Its two root sections
and three ordinary sectors retain the same 21 independently checked scalar
packets. Each formula keeps two occurrences of p and the final zero atom.
The carrier and radical identities therefore retain their exact original
polynomial list.

| Matrix before the final zero atom | Quantifier | Checked result |
| --- | --- | --- |
| p < 0 ∨ p ≥ 0 | ∀ | true |
| p = 0 ∨ p ≠ 0 | ∀ | true |
| p < 0 ∧ p ≥ 0 | ∃ | false |
| p > 0 ∧ p ≠ 0 | ∃ | true |
| p ≤ 0 ∧ p ≠ 0 | ∃ | true |
| ¬(p > 0 ∧ p ≥ 0) | ∀ | false |

The positive existential uses the exterior sectors. The negative existential
uses the sector between the two roots; its non-equality condition excludes
both root sections. All six comparisons and the shared conjunction,
disjunction and negation traversal are exercised. False results remain
diagnostic and are not proofs of the original goal. Active kernel reduction
diagnostics prohibit native sign/root production while checking the folds.

[BooleanSources](../conformance/HexRCF/CellReplay/Algebraic/BooleanSources.lean)
quotes four original real goals from the true checker results, through fresh
`Reify.prepare`, the fixed coefficient identity and `CellQuote.finish`.
[BooleanQuoted](../conformance/HexRCF/CellReplay/Algebraic/BooleanQuoted.lean)
rechecks the actual proof bodies in a fresh import unit. Each source uses
exactly `propext`, `Classical.choice` and `Quot.sound`. The audit requires the
new transfer, actual complete-cell soundness, supplied root coverage and frozen
readers, and excludes the previous source witnesses and scalar packet
producers. It separately audits the generic row law, false folds and binding
refusal.

[BooleanBinding](../conformance/HexRCF/CellReplay/Algebraic/BooleanBinding.lean)
moves the zero atom before the two p atoms. The original literal section row
then fails with the exact `.binding` tag under the same checked coefficient
operations. Its proof passes the active native-producer reduction guard.
This is a query-order refusal, not a failure to obtain a root or coefficient
record.

## Scope

The new module belongs to the existing optional target and umbrella. The
existing conformance target builds its consumers, and the existing algebraic
manual chapter contains runnable universal and between-root examples. No new
formula representation, packet fixture, tactic handler, field instance,
family-owner algorithm, CI job or publication wiring is introduced.

The underlying supplied-operation interface retains its documented compiled
native fallback for arbitrary missing predecessor records. These ordinary
kernel acceptances do not establish a strict arbitrary-packet compiled
checker. General source/provider/context history, reached-data assembly,
all-live transport, automatic common-field certification, general accepted
algebraic completeness and full native/infinitesimal coverage remain separate
requirements of #10358. Reusing one fixed packet proves no search progress or
performance/scaling claim.

## Validation

The [source-bound record](data/hexrcf-boolean-cells/context.json) binds the
implementation at `f29be3a0e0` to successful default adapter/conformance/manual
validation (14,674 jobs), affected quotation/umbrella checks (11,153 jobs),
complete manual rendering (14,254 jobs), constructor regeneration, dependency
and umbrella checks, 620 admission cones/1,520 local modules, eleven scanner
regressions, copyright, manual split and conformance wiring. The earlier
misplaced-import failure is retained separately. No admission is accepted.

All six desktop/narrow captures were opened and inspected. The
[desktop examples](data/hexrcf-boolean-cells/boolean-cell-desktop-source.png)
and [narrow examples](data/hexrcf-boolean-cells/boolean-cell-narrow-source.png)
fit their code blocks. Target-level overflow checks do not assert that
unrelated content in the whole manual has no horizontal overflow. Builds use
one aggregate 32GiB cgroup, no swap and two Lean workers; these operational
records are not performance or scaling evidence.
