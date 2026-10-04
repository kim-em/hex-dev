# Fresh tactic input validation costs

Editable public `Coefficients.Environment` inputs retain full binding and
required-type checks. The private tactic assembly accepts factory-produced data,
checks original divisors and submits the complete original-target proof to the
dispatcher’s ordinary kernel. The `rcf.algebraic.validateFresh` comparison control
repeats public validation for this fresh data and defaults to false.

The retained [f034e83b1 raw run](bench-results/hex-rcf-validation-proofs-f034e83b1-chungus2.json)
and [arm records](bench-results/hex-rcf-validation-proofs-f034e83b1-chungus2.json.samples.jsonl)
contain sixteen completed builds, but do **not** measure validation cost.
Both original goals used only the special positive square root of 2. They
selected the existing named-root handler, which does not read `validateFresh`.
The original raw metadata labels the dimension incorrectly; it is retained
unchanged. This run is an A/A observation of that handler, not evidence for
fresh-input validation. Its small mixed margins and equal proof sizes support
no validation speed claim. There was no sample filtering or rerun of that
unchanged comparison.

The corrected probes use the positive square root of 3 and independent square
roots of 2 and 3. Each actual quoted proof asserts the presence of
`CommonPresentation.checkPolynomials_sound`, so the controlled common-field
path must be exercised. Both arms still require ordinary-kernel acceptance and
the complete standard axiom inventory. Public validation batches coefficient
and divisor coordinates into two native list evaluations and gives the
coefficient function one let binding. These checks are input validation, not
proof evidence. Separate retained results are required for this corrected
comparison; the earlier run must never be pooled with it.

## Common-field comparison

The corrected [raw results](bench-results/hex-rcf-validation-proofs-99f23b940-chungus2.json)
and [arm records](bench-results/hex-rcf-validation-proofs-99f23b940-chungus2.json.samples.jsonl)
retain all sixteen completed builds at clean source
`99f23b940485c8a803b159174e9889c3fe42e7df`. The scalar goal is
`∀ x : ℝ, x² + √3 > 0`. The several-source goal conjoins
`x² + √2 + √3 > 0`, `√2 > 0` and `√3 > 0`. Every arm checks the
common-field proof marker and its complete standard axiom inventory.

Four trial-major rounds rotate the two pairs and alternate adjacent AB/BA
arms. The same imports and solver/replay controls are used. In this v2 source,
the checked arm forces synchronous elaboration while the fresh arm uses ambient
options; both were timed with one Lean thread. This is a stated arm difference,
so the result is not an isolated validation-cost attribution. Imported dependencies are warmed before timing, and only each
probe’s artifacts are removed per arm. Whole Lake time includes dependency
replay, elaboration, production, quotation, kernel checking, route inspection
and compiler output. Imported source hashes and exact dependency checkouts are
retained. Host `chungus2` uses Lean 4.35.0-rc3, automatically leased CPU 67,
sibling 19 and one Lean thread. Host activity is context and filters no sample.
There was no unchanged rerun or pooling with the earlier A/A inputs.

| Goal | Median checked / fresh seconds | Median paired fresh minus checked seconds | Median peak RSS checked / fresh KiB | Private olean checked / fresh bytes |
| --- | --- | ---: | --- | --- |
| Scalar | 8.797 / 8.621 | −0.1466 | 3,465,282 / 3,472,046 | 545,384 / 545,152 |
| Several sources | 9.590 / 9.448 | −0.1495 | 3,517,076 / 3,512,582 | 645,488 / 645,256 |

All eight adjacent pairs favor private assembly. Scalar differences are
`[-0.0697, -0.1996, -0.0935, -1.4458]` seconds; the slower checked arm in the
last pair is retained. Several-source differences are
`[-0.1529, -0.1884, -0.1313, -0.1461]`. Public olean bytes are equal within
pairs (58,448 / 59,504), and server olean bytes are 616 for all arms.
Namespace and source-module names differ between arms; the small private-size
difference is an observation, not an isolated proof-sharing attribution.

The mechanical record reports `complete`, `release_quality: true` and
`no-comparable-control`. These divisor-free fixed-goal observations favor the fresh arm, with the
synchronous-option difference stated above. They do not isolate validation cost. They establish no
asymptotic coefficient law, numerical-kernel complexity attestation, separate
validation/kernel attribution or general frontend/tower completion. The
reference already includes batched coordinate validation, so this does not
measure the older per-coordinate evaluator. The measured source is retained
separately from later documentation and delivery commits.
