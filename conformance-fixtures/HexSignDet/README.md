# Rational sign-table and descriptor fixtures

`sign_det.jsonl` contains 86 cases emitted by `hexsigndet_emit_fixtures`.
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
The oracle requires every case name; a truncated nonempty stream does not pass.
The repository's `lean-toolchain` and `lake-manifest.json` pin Lean-side inputs.

```sh
lake build hexsigndet_emit_fixtures
.lake/build/bin/hexsigndet_emit_fixtures > conformance-fixtures/HexSignDet/sign_det.jsonl
python3 scripts/oracle/sign_det_flint.py --check
python3 -m unittest scripts.oracle.test_sign_det_flint
```

These fixtures validate rational sign tables and the implemented descriptor
operations. Cross-polynomial comparison/re-encoding, extension-field and nested
context conformance remain required. None of these fixtures proves general
root-sum/Thom semantics or supplies Phase-4 performance evidence.
