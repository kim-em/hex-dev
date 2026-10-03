# Fixed-field literal quotation

The question is whether quoting already-reduced field coordinates directly
improves ordinary-kernel tactic proof cost. Each pair has identical imports,
the same quantified formula, solver, finite certificate checker and soundness
theorem. The reference quotes `PolyQuot.reduce`; the candidate quotes
`PolyQuot.mk` with a separate ordinary-kernel degree proof for every literal.
The `rcf.algebraic.reducedLiterals` comparison control selects the quotation.

The retained source is `427d008a7` on shared host `chungus2`, Lean
`v4.35.0-rc3`, automatically leased CPU 69 with sibling 21 and one Lean thread.
Four trial-major rounds rotate the three pairs and alternate adjacent AB/BA
order. All 24 completed arms are retained, without filtering or reruns.
The checkout and dependency checkouts were clean and the collector records
complete, release-quality provenance with no validity exceptions.

| Goal | Reference median, s | Candidate median, s | Median paired candidate minus reference, s |
| --- | ---: | ---: | ---: |
| `∃ x, x² = √2 ∧ 1 < x ∧ x < 2` | 21.506 | 22.413 | +0.773 |
| `∃ x, x² = 1/(√2+1) ∧ 0 < x ∧ x < 1` | 21.082 | 21.301 | +0.186 |
| `∃ x, x² = 2^(1/3) ∧ 1 < x ∧ x < 2^(1/3)` | 27.039 | 26.157 | −0.891 |

The further-root paired margins are all positive: +0.787, +1.039, +0.760 and
+0.285 seconds. The reciprocal margins are −0.670, −0.121, +0.559 and +0.493;
the cubic margins are −2.462, +0.698, −5.759 and +0.679. These observations do
not establish a speedup. The collector reports `no-comparable-control`; there
is no separate noise-control arm. Direct quotation with independently decided
degree bounds is therefore a comparison implementation, not the production
default. A different degree-proof construction requires its own comparison.

These are fresh-module `lake build` times, including Lake startup, elaboration,
source authentication, production, quotation and kernel replay. They do not
isolate kernel reduction or measure numerical solver throughput. Every arm
audits its actual theorem dependencies and uses only `propext`,
`Classical.choice` and `Quot.sound`.

Median peak RSS spans 4,752,160–5,120,804 KiB. Candidate private olean sizes
are 915,024, 956,120 and 1,009,072 bytes, respectively; reference sizes are
835,408, 880,088 and 934,256 bytes. The candidate does not reduce serialized
proof size. Raw data includes other artifact sizes, process accounting,
compiler output, host activity and SMT activity. The largest recorded host
Lean/Lake count is 38. Completed samples remain evidence under that load.

This experiment tests one proposal from #10634. It does not measure direct
normalized rational constructors, shared replay declarations, polynomial
normalization, interval signs or indexed sign lookup from #10633. The signed
Sturm chain already uses positive absolute-leading-coefficient scaling;
arbitrary monic scaling would not preserve its signs.

- [Collector](../scripts/bench/hexrcf_literal_proofs.py)
- [Reference and candidate modules](../bench/HexRCF/ProofProbe/Literals)
- [Complete results](bench-results/hex-rcf-literal-proofs-427d008a7-chungus2.json)
- [Incremental retained samples](bench-results/hex-rcf-literal-proofs-427d008a7-chungus2.json.samples.jsonl)
