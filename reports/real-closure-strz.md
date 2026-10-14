# Original Strzeboński conformance cases

The [native driver](../conformance/HexRealClosure/StrzConformance.lean)
reproduces the four real polynomial inputs in the original CADE-24 `strz.py`.
The [source archive](bench-results/real-closure-cade24-inputs/README.md) records
the script SHA-256
`4d26847955ecacaff4cadd0dce4550f125a726ea3f4e768d7aedd48ebcdaa7c4`.
The source itself omits examples 1, 5 and 7 because they use complex numbers.

| Original case | Coefficient inputs | Degree | Real roots |
| --- | --- | --- | --- |
| 2 | Positive √2 and √3 | 5 | 3 |
| 3 | Positive √7 | 10 | 2 |
| 4 | Second and third ordered roots of X³ − 7X − 5 | 3 | 1 |
| 6 | Positive √2, √3 and √6 | 5 | 1 |

Every returned real root has multiplicity one. In case 6 the executed cubic
coefficient is `23 + 8√6`; the source's print label says `23 + 8√5` instead.
The driver follows the executed coefficient list. Case 4 computes all three
source cubic roots and retains indices 1 and 2, exactly as the original does.

Each radical or cubic root comes from the actual complete-root producer,
with native equation, order, multiplicity and selected-descriptor replay
checks. When coefficients have separate immutable owners, `Shared.gather?`
builds their common target and the driver uses its returned value maps before
constructing the original polynomial. The complete-root API then isolates
every real root over that target. The
[retained fixture](../conformance-fixtures/HexRealClosure/strz.jsonl) contains
the original source selections, complete target signatures, actual polynomial
coefficients, ordered output descriptors and multiplicities.
The index fields label the source selections; the checker verifies the actual
selected embeddings through the interpreted coefficients and root values.

The [independent Z3 checker](../scripts/oracle/real_closure_strz.py)
reconstructs the original radicals and cubic roots in one exact RCF context,
rebuilds each original coefficient formula, and checks the native target
coefficients against it. It independently computes the complete ordered root
list and obtains exact multiplicities by successive derivatives. It checks
the mathematical selected roots; native replay of the stored evidence graphs
is checked by the Lean driver. Mutation tests reject altered source identities,
inputs, selections, output roots, multiplicities and the case-6 print-label
substitution. They change actual coefficient values and target embeddings,
including interpretation of the cubic coefficient using √5 instead of √6.
The checker binds its script identity to the
[verified source inventory](bench-results/real-closure-cade24-inputs/source.json).

```bash
lake build hexrealclosure_strz_conformance
LEAN_ABORT_ON_PANIC=1 .lake/build/bin/hexrealclosure_strz_conformance > /tmp/strz.jsonl
diff -u conformance-fixtures/HexRealClosure/strz.jsonl /tmp/strz.jsonl
python3 scripts/oracle/real_closure_strz.py /tmp/strz.jsonl
python3 -m unittest scripts.oracle.test_real_closure_strz
```

The driver also accepts one case number, `2`, `3`, `4` or `6`. The checker
accepts either one such record or all four in their original order and requires
`z3-solver` 4.15.4.0. The existing single CI job builds the driver, compares
fresh output with the retained fixture and checks both outputs independently.

These checks reproduce each mathematical input and its selected embeddings.
They construct the coefficient owners needed by each case, rather than
reproducing the original Python process's global allocation history. They
make no original-runtime comparison, scientific timing claim, operation-count
claim or ordinary-kernel theorem specific to these scripts. The required
Phase 4 measurements and the general interleaved realization theorem remain
separate obligations of #10378.
