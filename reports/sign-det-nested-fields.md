# Sign determination over nested infinitesimal fields

The executable `hexsigndet_emit_nested_fields` checks one family at extension
depths one through four. Its fields are obtained by iterating the existing
canonical rational-function field over the rationals. Each new indeterminate is
positive and smaller than every positive element of the preceding field. The
sign function uses the existing lowest-coefficient sign at each level; the field
operations and field laws are the existing `HexRationalFn` instances.

Let g = ε₁ − ε₁² − ε₂ − ⋯ − ε_d at depth d. This is positive under
the specified order. Reversing the order at depth at least two, or interpreting
the first generator as infinitely large, makes g negative and changes the sign
table. The head and queries are

```
P = X² − g²,       Q = [X, X − g],       interval = (−∞, +∞).
```

The two roots are −g and g. Their sign patterns are (−,−) and (+,0), each with
count one. All other patterns have count zero. Depth zero is excluded because
g is zero there and the head is not squarefree. The executable checks this
using the actual prepared-domain operation.

For each positive depth the native executable emits the actual results of reduced and unreduced BKR construction, the full
ternary reference, and
replay of the shared same-level graph. It also checks rejection with a foreign
context and with a stale child context. It checks the graph leaf layout before
splicing a valid same-context child built for the different head X² − (2g)²,
and checks rejection when the root is presented without its support children. The emitted inputs retain the actual
stored coefficient arrays, recursively encoding each numerator and denominator.
The same input constructor is used for execution and emission.

The independent pinned Z3 RCF oracle introduces the same sequence of
infinitesimals, reads those coefficients, verifies the defining polynomials,
computes their exact roots and evaluates the queries. It checks the complete
sign table. Its adversarial tests reject omitted support even when the total
count is preserved, wrong signs, substituted inputs, malformed counts and
foreign or reordered coefficient contexts. Those JSON-table mutations test the
oracle, while the emitted replay decisions test the native checker. Additional
tests actually reverse the independent field order and substitute an infinitely
large first generator; each changes the independently computed table. This uses the existing oracle
pipeline and its existing Z3 dependency.

Run the native cases and independent oracle with:

```sh
lake build hexsigndet_emit_nested_fields
.lake/build/bin/hexsigndet_emit_nested_fields > nested-fields.jsonl
python3 scripts/oracle/sign_det_nested_z3.py nested-fields.jsonl
```

The four-level native conformance run took 336.587 seconds on the shared
host `chungus2` (source SHA-256
`cddfb03eec41f057eec31313190d1550cbdbbf7027d852f22865ba9dbe35f4e8`,
executable SHA-256
`cf6c75e85bb88dcaea7de43ebeb5748a931e8100a4cc1a21742f049e8a49af43`). That observation includes all three construction modes and
replay checks. It is not a fixed-schedule complexity measurement, nor a timing
of coefficient signs alone. Depth-dependent measurements need to account for the actual nested arithmetic
and witnesses. This single execution does not establish a complexity law.

These are executable conformance cases, not ordinary-kernel semantic proofs or
cross-level coefficient-proof certificates. Same-level BKR graph sharing does
not discharge the separate requirement to share and validate lower-level sign
proofs. Nested proof probes, dependency counts, allocation scaling and the full
Phase-4 evidence remain separate obligations. This test imports no real-closure
tower implementation and changes no field arithmetic.
