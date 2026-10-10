# Supplied irreducibility proof construction cost

This fixed experiment answers the question of where to construct the supplied
irreducibility theorem for the degree-eight common field of the selected quartic
α and √2. Both arms prove `∀ x : ℝ, x² + α + √2 > 0` using the same `rcf`
frontend and literal polynomial `[-2,-24,169,70,-127,-70,6,8,1]`.

The reference reconstructs irreducibility using the owner's existing
`irreducibility!` tactic and installs that fresh checked instance. The candidate
reuses the imported, scoped instance. Both arms deliberately have identical
imports, including the factorizer's private executable closure and the imported
construction module. This measures the cost of repeating construction, not the
smaller ordinary-import consumer cone. The separate ordinary-import
[regression](../conformance/HexRCF/SuppliedIrreducibleProofs.lean) establishes
that the shipped frontend can reuse the proof without those private imports.
Native common-field construction during tactic search is unchanged.

The clean source is `9b6dbba8f515a1dd3db0dbe5633f6a11ca19eb70` on `chungus2`,
Lean `v4.35.0-rc3`, AMD EPYC 9455. The existing fresh-module collector runs four
fixed trial-major rounds, adjacent AB/BA/AB/BA arms, one Lean thread, on
automatically leased CPU 89 (SMT sibling 41). It removes only the measured
module's generated artifacts and builds through Lake. Import dependencies are
warm. Construction has 8,000,000 heartbeats; the tactic uses the default budget;
both arms have recursion limit 32,768.

| Round | Order | Reconstruct A (s) | Reuse B (s) | B − A (s) |
| --- | --- | ---: | ---: | ---: |
| 1 | AB | 20.268 | 11.958 | -8.310 |
| 2 | BA | 20.084 | 13.404 | -6.681 |
| 3 | AB | 21.643 | 13.495 | -8.148 |
| 4 | BA | 21.401 | 13.152 | -8.249 |

Median whole fresh-module cost is 20.834 seconds for reconstruction and
13.278 seconds for reuse. The median paired change is −8.199 seconds; every
pair favors reuse. These measurements include Lake startup, quotation,
elaboration and kernel checking. They do not isolate factorizer time or
establish a scaling law. The collector reports `no-comparable-control`; no
null control, host activity filter or unchanged-source rerun was used.

Median peak RSS is 4,471,748 KiB (4.26 GiB) and 3,866,274 KiB (3.69 GiB).
Private olean files are 692,976 and 690,456 bytes; public olean files are
50,752 and 50,152 bytes. Lower fresh-build cost does not establish physical
proof sharing or a general tactic speedup. All eight arms retain complete
inventories with exactly `propext`, `Classical.choice`, `Quot.sound` and verify
that the emitted proof uses the intended fresh or imported checked instance.

The largest recorded Lean/Lake process count is seven. Maximum recorded
SMT-sibling busy ratio is 0.01171 and measurement-CPU foreign ratio is 0.00123.
Host observations are retained as context; every completed arm remains evidence.
The first collection retained two successful builds but failed inventory
validation because `#guard_msgs` suppressed successful output. Adding explicit
inventory output changed the source; the completed four-round collection has
its own source binding. The two earlier arms and all exploratory failure logs
remain separately recorded and are not pooled with these results.

The result supports constructing this proof once in a separate module and
reusing it for this goal. It does not repair the automatic certificate-language
gap or establish accepted progress for all algebraic sources. General frozen
tower/context assembly and recursive whole-joint finite replay remain separate
requirements; #10358 stays open.

The manual separately exercises the existing native finite-sign realization
API on both operands, their sum and their product with one reader. Its exact
proof, renamed in a fresh module, passes a complete standard-three-axiom
inventory. The actual provider history and closed partial domain remain
explicit; this verifies use of the native law and constructs no frozen
context/root/arithmetic package. The manual passes 14,149 Lake jobs and full
rendering passes 14,151 at the recorded documentation sources.

- [Protocol](../scripts/bench/rcf_irreducibility_proofs.py)
- [Reconstruction probe](../bench/HexRCF/ProofProbe/Supplied/Reconstruct.lean)
- [Reuse probe](../bench/HexRCF/ProofProbe/Supplied/Reuse.lean)
- [Full source-bound report](data/hexrcf-irreducibility-cost/paired.json.gz)
- [All completed arms](data/hexrcf-irreducibility-cost/paired.samples.jsonl.gz)
- [Original collection and diagnostic records](data/hexrcf-irreducibility-cost/context.json)
