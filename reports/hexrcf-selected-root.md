# Frozen ordinary selected-root row

The [fresh source proof](../conformance/HexRCF/SelectedRoot/Proofs.lean) concludes
`∃ x : ℝ, x² = Real.sqrt 2 ∧ 1 < x ∧ x < 2` through the original native
selected field. It retains the equation and both bound atoms at one ordinary
real root. The existing `TotalAlgebraicProofs.further_section` is an independent
polynomial-quotient tactic cross-check.

The fixture has one coefficient, three source atoms, degree-two parent and
child defining polynomials, and two selected-root levels. Its frozen JSON has
86,316 bytes. The lower and upper root graphs contain one vertex each, the
source row five, and the 37 scalar packets one each: 44 stored graph vertices
and 44 expanded tree occurrences. This fixture establishes no DAG-sharing gain
or degree/atom/width/precision/depth scaling verdict.

The upper root is `Descriptor.ofChecked` over independently parsed raw data
and a structurally expanded literal graph. Cached predecessor operations are
used for both specialization and replay. Kernel diagnostics require active,
nonempty counters and reject unfolds of the audited native root/sign producers
while checking root, row and exact refusal proofs. Zero unresolved requests is
checked separately. Scalar restoration retains literal key/sign fields using
the owner's `Context.readSignFact_fields`; subsequent field lookup needs the
rational key parser rather than the entire certificate reader.

## Ordinary build observations

These are operational Lake build captures on a shared host, with default build
parallelism. They are not fixed-schedule scientific comparisons and support no
speedup claim. No completed observation was discarded or retried for host
activity. [Context and exact source hashes](data/hexrcf-selected-root/build-context.json)
record the post-build host activity; this is not a pre-run quiet-host test.

| Build | Elapsed | Largest child RSS | Capture scope |
| --- | ---: | ---: | --- |
| [Frozen fixture](data/hexrcf-selected-root/fixture-build.log.gz) | 140.12 s | 9,271,492 KiB | All 21 fixture outputs removed once; owner/adapter dependencies warm. Includes data, scalar acceptance, root/row quotation, fresh original-goal proof, refusals and complete audits. |
| [Affected adapter/conformance/manual](data/hexrcf-selected-root/affected-build.log.gz) | 353.86 s | 14,809,424 KiB | Default optional adapter, all RCF conformance modules, handler/reifier regressions and manual. Some outputs, including the fixture, were already warm. The existing RCF chapter built in 205 s. |

RSS is the largest waited-for child, not an aggregate concurrent-memory
measurement. No compiled family-driver timing is included.

The public row API requires a faithful real parent model and authenticated
source inputs. Its divisor theorem concerns the supplied values; source
identity/guard collection remains a caller obligation. A false row is a
counterexample at that point, not a false existential decision. Complete root
coverage, generic frontend certificate production/progress and general finite
joint nested/successive-infinitesimal realization remain outside this fixture's
evidence. The full [adapter inventory](hexrcf-adapter-evidence.md) retains those
completion limits.
