# Sign determination over nested infinitesimal fields

The executable `hexsigndet_nested_conformance` checks one family at extension
depths one through four. Its fields are obtained by iterating the existing
canonical rational-function field over the rationals. Each new indeterminate is
positive and smaller than every positive element of the preceding field. The
sign function uses the existing lowest-coefficient sign at each level; the field
operations and field laws are the existing `HexRationalFn` instances.

Let g be the sum of the infinitesimals introduced so far. The head and queries
are

```
P = X² − g²,       Q = [X, X − g],       interval = (−∞, +∞).
```

The two roots are −g and g. Their sign patterns are (−,−) and (+,0), each with
count one. All other patterns have count zero. Depth zero is excluded because
g is zero there and the head is not squarefree.

For each positive depth the native executable checks direct evaluation at both
roots, reduced and unreduced BKR construction, the full ternary reference, and
replay of the shared same-level graph. It also checks rejection with a foreign
context and with a stale child context. The emitted inputs retain the actual
stored coefficient arrays, recursively encoding each numerator and denominator.
The same input constructor is used for execution and emission.

The independent pinned Z3 RCF oracle introduces the same sequence of
infinitesimals, reads those coefficients, verifies the defining polynomials,
computes their exact roots and evaluates the queries. It checks the complete
sign table. Its adversarial tests reject omitted support even when the total
count is preserved, wrong signs, substituted inputs, malformed counts and
foreign or reordered coefficient contexts. This uses the existing oracle
pipeline and its existing Z3 dependency.

Run the native cases and independent oracle with:

```sh
lake build hexsigndet_nested_conformance
.lake/build/bin/hexsigndet_nested_conformance > nested-fields.jsonl
python3 scripts/oracle/sign_det_nested_z3.py nested-fields.jsonl
```

The four-level native conformance run took roughly four minutes on the shared
host `chungus2`. That observation includes all three construction modes and
replay checks. It is not a fixed-schedule complexity measurement, nor a timing
of coefficient signs alone. It exposes substantial cost even with a quadratic
head and two queries; depth-dependent measurements need to account for the
actual nested arithmetic and witnesses.

These are executable conformance cases, not ordinary-kernel semantic proofs or
cross-level coefficient-proof certificates. Same-level BKR graph sharing does
not discharge the separate requirement to share and validate lower-level sign
proofs. Nested proof probes, dependency counts, allocation scaling and the full
Phase-4 evidence remain separate obligations. This test imports no real-closure
tower implementation and changes no field arithmetic.
