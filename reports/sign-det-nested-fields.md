# Sign determination over nested infinitesimal fields

The executable `hexsigndet_emit_nested_fields` checks an ordered-field family
at extension depths one through four. Its fields iterate the existing canonical
rational-function field over the rationals. Each new indeterminate is positive
and smaller than every positive element of the preceding field. The sign
function uses the existing lowest-coefficient sign at each level; arithmetic
and field laws are the existing `HexRationalFn` instances.

At depth d let g = ε₁ − ε₁² − ε₂ − ⋯ − ε_d. Let a = ε₁ at depth one,
and let a be the preceding depth's generator at higher depths. Then g > 0,
and g − a is −ε₁² at depth one and −ε_d at every higher depth. The inputs are

```
P = X² − g²,       Q = [X − g, X − a],       interval = (−∞, +∞).
```

The two roots −g and g have sign patterns (−,−) and (0,−), each with count
one; all other patterns have count zero. The second query at g forces the
newest level's sign past its zero constant coefficient. The emitted value of
`sign (g − a)` checks the same cancellation directly. Thus treating the newest
infinitesimal as zero or negative cannot pass. The independent tests also
reverse the field order or make the first generator infinitely large; each
changes the computed table. Depth zero exercises actual rejection of the
nonsquarefree head X² by the prepared-domain operation.

For every positive depth the emitter returns the actual reduced, unreduced and
full-reference tables and replay decisions. It checks graph leaf layout,
foreign contexts and stale child contexts. It splices a valid same-context
child built for X² − (2g)², and also changes that child's top-level head binding
back to P while retaining its foreign moment evidence. Both copies must fail.
Presenting the root without its children must also fail the leaf-arity check;
that case alone does not prove general support completeness. The emitted
coefficient arrays recursively encode actual numerators and denominators, using
the same input constructor as execution.

The pinned Z3 RCF oracle independently reads those coefficients, verifies P
and Q, computes exact roots and signs, and checks every returned table. Its
JSON mutation tests reject omitted patterns with preserved total counts, wrong
signs, substituted inputs, malformed counts and foreign contexts. Those
mutations test the oracle; the native replay decisions test the certificate
checker. The existing two-level oracle keeps its original default depth limit.

Routine CI runs depths one and two; the local profile retains all four depths.
The existing classifier runs these checks for HexSignDet changes and on main,
not automatically for every change in its dependencies. Run both profiles with:

```sh
lake build hexsigndet_emit_nested_fields
.lake/build/bin/hexsigndet_emit_nested_fields > nested-fields.jsonl
python3 scripts/oracle/sign_det_nested_z3.py nested-fields.jsonl
.lake/build/bin/hexsigndet_emit_nested_fields --profile local > nested-fields-local.jsonl
python3 scripts/oracle/sign_det_nested_z3.py nested-fields-local.jsonl --profile local
```

A single native local run took 441.941 seconds on shared host `chungus2`.
The per-depth observations include construction, replay, coefficient encoding
and output; they are not fixed-schedule complexity measurements:

| Depth | Elapsed seconds |
| --- | ---: |
| 1 | 0.034893 |
| 2 | 0.814919 |
| 3 | 18.912842 |
| 4 | 422.155960 |

The [execution record](data/sign-det-nested-fields/anchor-fields/execution.json)
retains source/executable hashes and host load, and the stderr record retains
the per-depth timings. These observations are host-specific, not CI runner
measurements or a complexity law.

These are executable conformance cases, not ordinary-kernel semantic proofs or
cross-level coefficient-proof certificates. Same-level BKR graph sharing does
not discharge sharing and validation of lower-level sign proofs. Nested kernel
probes, dependency counts, allocation scaling and full Phase-4 evidence remain
requirements. This test imports no tower implementation and changes no field
arithmetic.
