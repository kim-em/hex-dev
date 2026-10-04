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
