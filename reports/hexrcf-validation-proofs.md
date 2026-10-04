# Fresh tactic input validation costs

The implementation question is whether revalidating freshly constructed tactic
input adds useful protection or substantial fresh-module cost. Editable public
`Coefficients.Environment` inputs retain full binding and required-type checks.
The private tactic assembly accepts only data returned by its own field factory,
screens unresolved/unsafe/axiom dependencies, checks every original divisor and
submits the complete original-target proof to the dispatcher’s ordinary kernel.
`rcf.algebraic.validateFresh` repeats the public boundary as a comparison control;
its default is false. It never disables public API validation or proof checking.

The [raw results](bench-results/hex-rcf-validation-proofs-f034e83b1-chungus2.json)
and [incremental arm records](bench-results/hex-rcf-validation-proofs-f034e83b1-chungus2.json.samples.jsonl)
retain all sixteen completed ordinary-kernel builds at source
`f034e83b199362fccc523bc27cc4ccdf10ea0961`. The two pairs have matching imports,
goals and solver/replay options. The scalar goal is `∀ x : ℝ, x² + √2 > 0`;
the several-coefficient goal conjoins `x² + 3√2 > 0`, `√2 > 0`, `2√2 > 0` and
`3√2 > 0`. The reference sets fresh-input validation to true and the candidate
to false. Both emit proofs of the same original sentence with only `propext`,
`Classical.choice` and `Quot.sound`.

Four fixed trial-major rounds rotate the two pairs and alternate adjacent
AB/BA arms. Dependency warming precedes timing; each arm removes only its
probe’s generated artifacts. Whole Lake time includes dependency replay,
elaboration, production, quotation, checking and compiler output. The source
and imported-source hashes, toolchain and dependency checkout identities are
retained. Source was clean and unchanged throughout. Host `chungus2` used
Lean 4.35.0-rc3, automatically leased CPU 53, sibling 5 and one Lean thread.
Recorded host activity filters no completed sample. There was no rerun.

| Goal | Median checked / fresh seconds | Median paired fresh minus checked seconds | Median peak RSS checked / fresh KiB | Public / private olean bytes, both arms |
| --- | --- | ---: | --- | --- |
| Scalar | 8.614 / 8.599 | −0.0359 | 3,468,442 / 3,469,204 | 58,280 / 483,480 |
| Several | 8.867 / 8.886 | −0.0004 | 3,474,736 / 3,473,634 | 60,248 / 515,040 |

The scalar paired differences are `[-0.1124, 0.0365, 0.0092, -0.0810]` seconds;
the several-coefficient differences are `[0.0399, -0.0018, 0.0011, -0.0266]`.
The full paired data, compiler outputs and byte/memory observations are retained.
The mechanical record reports `complete`, `release_quality: true` and
`no-comparable-control`. These small mixed margins establish no useful speedup
or slowdown on these inputs. Private assembly avoids redundant validation by
construction; the observations do not establish general coefficient scaling,
separate compilation/kernel costs or physical heap-sharing behavior.

Public validation batches coefficient and divisor coordinates into two native
list evaluations. The coefficient function has one let binding rather than
being duplicated at every coordinate. These are input-binding checks;
ordinary-kernel proof acceptance remains mandatory. This comparison includes
the batching implementation in the reference, so it does not measure the older
per-coordinate evaluator or assert how much batching saved.

The timing source is retained separately from later documentation and delivery
commits. These fixed-goal proof costs are not compiled numerical complexity
attestation, general frontend/tower completion or extension evidence borrowed
from rational benchmarks. Imported dependency warming and module names are
part of the stated measurement boundary.
