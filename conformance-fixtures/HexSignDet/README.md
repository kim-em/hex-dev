# Exact sign-table and descriptor fixtures

`sign_det.jsonl` contains 102 cases emitted by `hexsigndet_emit_fixtures`.
The 59 table records include ascending rational polynomial coefficients as exact
`[numerator, denominator]` pairs, open finite/infinite endpoints, and the
complete sparse tables from reduced and unreduced BKR. Lists of at most four
queries also include the full-ternary reference result. Constructor diagnostics
are emitted as errors, never converted into mathematical domain rejection.

The independent Lean consumer clears rational denominators, enumerates roots
with `ZPoly.realAlgebraicRoots`, and uses exact Horner evaluation and signs.
It does not consume BKR moments, counts or candidate supports. This import is
confined to conformance; the computational library has no reverse dependency.

`scripts/oracle/sign_det_flint.py` independently checks the domain with FLINT
rational polynomial arithmetic, enumerates real `qqbar` roots, filters by the
exact open interval, and evaluates every query at each selected root. It compares
complete positive-count tables, so matching totals do not excuse omitted support.
The existing adapter pins **python-flint 0.9.0 / FLINT 3.6.0** and uses no decimal
root approximations. Missing capabilities fail the oracle. Its tests include
identity-preserving total-count forgeries, malformed sparse tables, wrong
Thom order, omitted roots, incorrect selected signs, false validity diagnostics,
and Boolean values substituted for integer sign/index literals.

The 35 fixed cases cover rational and irrational roots, shared factors, zero,
duplicate and constant queries, empty queries, negative leading coefficients,
formal derivative lists, high-degree queries, rational scaling, constant/root-free
heads, zero/repeated heads and invalid endpoint combinations. Another 24 cases
use seed `10377` and the emitter's fixed recurrence
`state = (1664525 * state + 1013904223) mod 2^32` to select query coefficients.
The 27 descriptor records add partial/full validation, permuted slots, empty
constraints in singleton intervals, completion, selected-query signs and full
root lists. They include the cubic example where lexicographic derivative-word
order is wrong, negative heads, irrational roots, absent/ambiguous/unrealized
encodings, malformed slots, invalid domains and stale contexts. FLINT evaluates
formal derivatives and queries at roots sorted by exact numerical comparison;
it never uses the producer's Thom rule to establish expected root order.
Eleven comparison and five re-encoding records cover equal derivative vectors
from different linear heads, common irrational roots, negative/scaled heads,
overlapping/disjoint intervals, foreign root endpoints, invalid targets and
absent selected roots. The oracle checks the common head's squarefreeness and
three polynomial divisibilities with FLINT, then compares selected roots by
their exact numerical positions. It also verifies both common-head encodings and the total comparison in both
argument orders. Every comparison case has adversarial missing, malformed and
wrong-order total-result tests.
It does not assume that the producer's Thom comparison is correct.
The oracle requires every case name; a truncated nonempty stream does not pass.
The repository's `lean-toolchain` and `lake-manifest.json` pin Lean-side inputs.

```sh
lake build hexsigndet_emit_fixtures
.lake/build/bin/hexsigndet_emit_fixtures > conformance-fixtures/HexSignDet/sign_det.jsonl
python3 scripts/oracle/sign_det_flint.py --check
python3 -m unittest scripts.oracle.test_sign_det_flint
```

`infinitesimal.jsonl` contains 31 cases emitted by `hexsigndet_emit_infinitesimal`
using the existing rational-function fields over one and two positive
infinitesimals. The independent Z3 RCF oracle requires `z3-solver==4.15.4.0`
and numeric runtime version `(4, 15, 4, 0)`. Its comparison checks include the
total operation in both argument orders, with adversarial missing, malformed
and wrong-order result tests. Each record creates a fresh context
and reconstructs the serialized coefficients with exact arithmetic. The oracle
enforces the coefficient depth of each case and the corrected Passmore
polynomial `(εx²−1)(εx³−1)`, then computes roots, signs and order independently.
The cases cover sign tables, invalid domains, all five descriptor-error reasons,
completion, selected signs, comparisons and re-encoding. Negative replay checks
change context, head and derivative-query bindings or present a multi-query
table as a leaf; the latter checks leaf arity, not identity-preserving incomplete
support. The 16 adversarial Python tests also reject substituted case inputs,
omitted support with preserved totals, wrong root order and version drift.

```sh
lake build hexsigndet_emit_infinitesimal
.lake/build/bin/hexsigndet_emit_infinitesimal > conformance-fixtures/HexSignDet/infinitesimal.jsonl
python3 scripts/oracle/sign_det_z3.py --check
python3 -m unittest scripts.oracle.test_sign_det_z3
```

These fixtures validate rational and nested-infinitesimal sign tables and the
implemented descriptor operations, including comparison and re-encoding.
The infinitesimal sign callbacks are test providers. General coefficient
interpretation, nested semantic replay and root-sum/Thom correspondence proofs
remain required. None of these fixtures supplies Phase-4 performance evidence.

`common-fields.jsonl` contains two actual common-number-field cases: independent
√2/√3 inputs producing a degree-four generator and independently constructed
∛2/∛4 inputs represented in a degree-three field. Each record includes the
selected generator interval, both independently selected input intervals,
QAdjoin coordinates, the checked table, complete root list, selected signs,
comparison in both directions, re-encoding and rejected stale evidence.
`scripts/oracle/sign_det_common_fields.py` reconstructs all selected algebraic
values and checks the coordinates, roots, signs and orders with FLINT `qqbar`
using exact algebraic arithmetic. It checks the coefficient and context
bindings and rejects incomplete fixture streams. The oracle never consumes
Lean's BKR moments, support choices or Thom ordering rule.

```sh
lake build hexsigndet_emit_common_fields
.lake/build/bin/hexsigndet_emit_common_fields > conformance-fixtures/HexSignDet/common-fields.jsonl
python3 scripts/oracle/sign_det_common_fields.py --check
python3 -m unittest scripts.oracle.test_sign_det_common_fields
```
