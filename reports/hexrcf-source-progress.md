# Selected-source proposal progress

`ScalarPacket.buildParts_sign` proves that a produced scalar proposal retains the actual total sign of its original polynomial at its selected root, under the supplied lawful ordinary-real parent model. It consumes the owner's checked selected-sign interpretation. It does not turn a proposed integer or serialized graph into proof evidence.

`SourceBuild.select_single` proves actual equation/window packet production for a selected root satisfying the original equation and a strictly positive original window. `SourceBuild.buildOn_success` derives an actual bounded proposal from a valid interpreted squarefree open domain, exactly one real root in that domain and strict window positivity at its roots. Positive stored degree follows from the real root and the owner's degree correspondence; it is not an extra premise. The proof uses the owner's `Descriptor.build_success_iff` and selected-root laws, then the packet progress and sign-retention laws. No successful producer equation, precomputed descriptor, table or accepted packet is assumed.

These are progress laws for valid mathematical inputs. Serialized replay acceptance, source alias selection, generic provider/history discovery and complete algebraic tactic progress remain separate obligations.

A fresh importing audit checks all three actual theorem bodies through `addDeclCore` with kernel checking enabled and checks their full axiom closure: `propext`, `Classical.choice`, `Quot.sound` only. It retains no copied declaration. The same native module still compares all 25,477 frozen bytes, validates six scalar graphs and checks endpoint/domain/uniqueness/wrong-conjugate refusals. Its final build passed in 11.662s, peak 1023.1 MiB/no swap. Earlier elaboration failures and successful core/control attempts are retained; exact snapshots of failed source versions are not claimed.

The source transition is proof-only. Removing exactly the three new theorem blocks and the new fresh-audit import/body recovers each of the three prior files byte-for-byte. Production, checking, quotation, budgets, data fixtures, Lake/CI configuration, tactic dispatch and manual sources are unchanged. The earlier 57-target/manual/render/quotation record retains its original source pin; it is not claimed as a new run. The new proof bodies and existing native frozen-byte controls have their own successful build and audit. Final-head CI and required fresh Opus review remain pending.

Eight metadata checks pass: copyright, line counts, dependency graph, named admissions, release manifest, figure freshness, literal freshness and diff checks. No build target or CI configuration changes.

Every own Lean/Lake call remains serial under aggregate 32 GiB, zero swap and two Lean threads. Full #10358 remains open; this supplements bounded proposal progress and does not establish generic frozen acceptance or complete tactic integration.
