# Fixed-field sign lookup comparison

This experiment answers #10633's finite-sign lookup question. Both arms use
matched imports and goals, monic carriers, `PolyQuot.reduce` quotation, interval
sign evidence, and split kernel replay. The reference retrieves keys linearly
from the checked sign entries. The candidate quotes a balanced tree of positions
in that same table, checks bounds and the exact key at each hit, and transports
accepted indexed replay to the existing checker and soundness theorem.
Sorting and index construction run during production; kernel replay receives
only the frozen tree. No independent cache signs or comparator assertions are
trusted. The option changes sign retrieval, not algebraic search or dispatch.

The first source, clean `dd2482e41d3054b670a9b3fe019cc9ea144ee08c`, checks
all requested indexed reads before quotation. Four trial-major rounds on
`chungus2` use automatically leased CPU 34 (SMT sibling 82), one Lean thread,
rotating pairs and adjacent alternating AB/BA arms. All 24 arms completed.

| Goal | Linear median (s) | Indexed median (s) | Median paired change (s) |
| --- | ---: | ---: | ---: |
| Further square root | 17.049 | 13.401 | −3.612 |
| Reciprocal coefficient | 16.853 | 13.150 | −3.643 |
| Cubic coefficient | 18.073 | 14.389 | −3.717 |

The shipped lookup also preserves every original recorded hit on a missing
index route, using the original checked-table lookup. The generic
`Table.lookupIndex_isSome` law needs no comparator or tree-shape assumption;
malformed routing cannot introduce a new missing-sign failure. A missing entry
in the original table still fails frontend preflight. Every returned sign is
authenticated against the original table and selected root.

This changed implementation has a separate comparison at clean
`50a37279c8ed6984b6466a6c37fa16ab45b50dd8`, CPU 43 (SMT sibling 91), one
Lean thread, with the same four-round schedule. All 24 arms are retained.
This is a changed-source comparison, not an unchanged rerun or pooled result.

| Goal | Linear median (s) | Indexed median (s) | Median paired change (s) |
| --- | ---: | ---: | ---: |
| Further square root | 17.259 | 13.784 | −3.774 |
| Reciprocal coefficient | 17.185 | 13.673 | −3.493 |
| Cubic coefficient | 18.007 | 14.449 | −3.527 |

All twelve paired changes favor indexing in each comparison. The second
further-root sequence is −3.713, −3.836, −3.238, −9.909 seconds. Its last
reference arm took 24.462 seconds and candidate 14.553 seconds; both remain
in the report. The largest recorded Lean/Lake count is 11 in the first study
and 24 in the second. Maximum SMT sibling busy ratios are 0.0163 and 0.1611;
measurement-CPU foreign ratios are 0.00130 and 0.00165. Host activity is
recorded context, not an exclusion criterion.

In the second study median peak RSS decreases from 4,636,260 to 4,041,298 KiB
(further root), 4,596,584 to 4,015,018 KiB (reciprocal), and 4,759,472 to
4,192,858 KiB (cubic). Private olean sizes increase from 611,024 to 641,576,
669,616 to 699,904, and 594,032 to 623,536 bytes. The first study has the
same private sizes. Lower build time and memory do not imply smaller proof
files or physical sharing.

Both collectors report `no-comparable-control`. These are whole fresh-module
Lake costs, including production, quotation, elaboration and ordinary kernel
checking; they do not isolate lookup cost or establish asymptotic scaling.
Every arm checks the actual indexed or linear proof route, interval entries,
coordinate constructor, and theorem axioms (`propext`, `Classical.choice`,
`Quot.sound`). No sample is filtered. No quiet-core wait or unchanged rerun
was used. Generator-interval refinement is a separate proposal.

`rcf.algebraic.indexSigns` defaults to true, supported by the retained
comparisons, checker equivalence, and preservation of recorded hits. The false
arm retains linear lookup. Earlier literal, interval, replay, and carrier
comparison probes now pin this false arm; those pins were added after their
archived measurements and preserve their original retrieval mode.

- [Collector](../scripts/bench/hexrcf_index_proofs.py)
- [Matched probes](../bench/HexRCF/ProofProbe/Index)
- [First full report](bench-results/hex-rcf-index-proofs-dd2482e41-chungus2.json)
- [First incremental records](bench-results/hex-rcf-index-proofs-dd2482e41-chungus2.json.samples.jsonl)
- [Preserved-hit full report](bench-results/hex-rcf-index-proofs-50a37279c-chungus2.json)
- [Preserved-hit incremental records](bench-results/hex-rcf-index-proofs-50a37279c-chungus2.json.samples.jsonl)

Reproduce with `python3 scripts/bench/hexrcf_index_proofs.py --output
<external-json-path>` from a clean checkout. Use a retained source commit for
its exact source/import hashes; later defaults and historical-control pins
have different hashes. The wrapper leases a CPU automatically and warms only
dependencies. Mathlib-importing proof probes remain build-only on-demand
modules; no runtime benchmark or CI job is added.
