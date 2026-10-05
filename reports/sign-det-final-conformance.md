# Direct sign-determination conformance

The [retained execution](data/sign-det-final-conformance/c377f14544/metadata.json)
checks the compiled BKR/Thom interfaces independently of the tactic and tower
clients. All commands succeeded. Their outputs, errors, source reconstruction
and original metadata are retained in the [archive](data/sign-det-final-conformance/c377f14544/archive.json),
with hashes of both compressed and original bytes. Applying the source patch
to its recorded base reproduces the entire captured source tree exactly.

The compiled number-field checks exercise 33 actual API cases over ℚ(∛2)
and the real quartic common field of √2 and √3. They cover tables, selected
signs, completion, root enumeration, comparison, re-encoding, conversion,
noninjective storage and rejection of stale or mismatched evidence.

FLINT independently checks rational roots/signs, signs of close algebraic
values, and original selected embeddings in independently constructed common
fields. The three common-field cases use √2 and √3 in both orders and ∛2 with
∛4. Z3 independently checks the nested infinitesimal inputs and complete tables
at all four depths, including actual rejection decisions. These oracles read
computed coefficients and outputs; matching saved fixture hashes is not their
correctness criterion.

| Check | Result | Whole-command elapsed seconds |
| --- | --- | ---: |
| Compiled number-field API checks | 33/33 passed | 8.525 |
| Rational fixture emission | 102 cases, subsequently checked by FLINT | 2.787 |
| Close-value scalar emission | 20 signs, subsequently checked by FLINT | 0.046 |
| Common-field emission | 3 cases, subsequently checked by FLINT | 0.619 |
| Nested infinitesimal emission | depths 1–4, subsequently checked by Z3 | 454.828 |
| Rational FLINT oracle | 102 cases, 0 failures | 0.108 |
| Close-value FLINT oracle | 20 signs, 0 failures | 0.088 |
| Common-field FLINT oracle | 3 cases, 0 failures | 0.054 |
| Nested Z3 oracle | 4 cases, 0 failures | 0.160 |
| Independent JSON byte oracle | 324 cases, 0 failures | 0.190 |
| Adversarial oracle regression tests | 51 tests passed | 0.901 |

The mutation tests cover omitted support, wrong counts or signs, substituted
inputs, changed selected embeddings and malformed byte records. The native
field checks separately exercise the actual certificate checker; oracle
mutation tests alone do not establish its rejection behavior.

The execution binds source `c377f1454431abc75d4d11e0d6fe98dfbb316a4d` and all
six compiled binary hashes. It used automatically leased CPU 57 on `chungus2`
and retained host load before execution and after every command. The oracle
environment used python-flint 0.9.0 / FLINT 3.6.0 and z3-solver 4.15.4.0.
Source revision, clean working-tree state and binary hashes were checked again
at the end. Every completed command is retained.

These are descriptive single-run times, including construction and output,
not isolated operation timings, medians, proof-checking costs or scientific
scaling verdicts. The capture does not measure allocated bytes or live memory.
The ordinary-kernel replay examples, shared coefficient-evidence interfaces
and remaining Phase-4 obligations have their own evidence; this collection
alone does not complete #10377.

To repeat the direct checks, build `hexsigndet_field_checks`,
`hexsigndet_emit_fixtures`, `hexsigndet_emit_field_signs`,
`hexsigndet_emit_common_fields`, `hexsigndet_emit_nested_fields` and
`hexsigndet_json_bytes` with `lake build`. The retained metadata lists every
exact emitter, oracle and regression-test command. Use the nested emitter's
`--profile local` and the corresponding oracle's `--profile local` for all
four depths. The oracle package versions are part of the input contract.
