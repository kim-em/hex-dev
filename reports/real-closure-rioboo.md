# Original Rioboo conformance cases

The native [Lean driver](../conformance/HexRealClosure/RiobooConformance.lean)
reproduces the mathematical actions of `rioboo1.py` and `rioboo2.py` from the
original CADE-24 example package. [PR #10899](https://github.com/kim-em/hex-dev/pull/10899)
records that package's source provenance. The script SHA-256 identities are
`51dee2d698ebe39a267d642b35d2197936739517234cd0be7039fe2ee2c5eba7` and
`2c13ac14e1c8783d1aaf88e56ee6ee5d40ebc730f19759b2b17321a722a70936`.

The first case computes every root of `X⁴ − 10X² + 1`, checks their strict
order, equations and unit multiplicities, and selects returned indices 2 and
3. It gathers their separate immutable owners through `Shared.gather?` and
uses the returned owner maps before computing `((a + b) / 2)² = 3`.
Both selected values are positive, as in the source script.

The second case executes the five positive-square-root selections from the
source: 28, 82, 33, 74, then 28 again. All requested owners enter the same
checked target before computing
`√28 + √82 < √33 + √74` and squaring the repeated √28 to obtain 28.
The repeated call is retained; its original owner remains available even when
the shared target reuses a selected generator.

The [retained fixture](../conformance-fixtures/HexRealClosure/rioboo.jsonl)
contains both complete original root lists, source selection labels,
multiplicities, target context signatures, 15 computed values and their cached
signs. The driver checks each original descriptor's native replay. The
[independent Z3 checker](../scripts/oracle/real_closure_rioboo.py) reconstructs
every selected root and target generator, verifies the literal original
polynomials, and interprets the stored values in one exact RCF context. It
checks equality of the actual transported operands with the original selected
values, both identities and the strict comparison. It does not replay the
embedded Lean evidence graphs; that boundary is exercised by the native driver.
The index fields label the source operations. Equality of the actual transported
values with the original selected roots checks the selected embeddings separately.
The checker also binds its script identities to the
[verified source inventory](bench-results/real-closure-cade24-inputs/source.json).

Run the native examples and compare their deterministic output with the fixture:

```bash
lake build hexrealclosure_rioboo_conformance
LEAN_ABORT_ON_PANIC=1 .lake/build/bin/hexrealclosure_rioboo_conformance > /tmp/rioboo.jsonl
diff -u conformance-fixtures/HexRealClosure/rioboo.jsonl /tmp/rioboo.jsonl
python3 scripts/oracle/real_closure_rioboo.py /tmp/rioboo.jsonl
python3 -m unittest scripts.oracle.test_real_closure_rioboo
```

The checker requires `z3-solver` 4.15.4.0, as does the existing RCF oracle
suite. The existing single CI job builds and runs the driver, compares its
output with the committed fixture, and checks both the fixture and fresh
output independently. The rejection tests alter original inputs, root order,
selected indices, multiplicities, source identities, transported values and
cached signs, including a changed target generator and the opposite conjugate.

These are compiled functional and independent semantic checks. They add no
scientific timing comparison, operation-count study or ordinary-kernel theorem
specific to these two scripts. The general operation and transport
correspondence theorems remain the formal foundation. The original
[Strzeboński cases](real-closure-strz.md) have their own conformance driver.
The required Phase 4 measurements remain separate work. π/e-dependent cases remain explicitly
unsupported while their approximation infrastructure is deferred.
