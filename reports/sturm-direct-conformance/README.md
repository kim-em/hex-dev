# Direct Sturm oracle coverage

The Mathlib-free native emitter exercises `Hex.Sturm.query`, `rootCount`,
reduced queries, preparation, prepared queries/counts, endpoint retargeting
and produced query/count-certificate replay. The
192-case corpus serializes original rational coefficients and finite/infinite
endpoints. Eleven fixed heads run over twelve interval choices. Another 24
rational cubic inputs each run on whole-line and finite intervals and use the POSIX LCG with seed 10575, coefficients from
−5 through 5 and denominators from 1 through 5. Twelve cases use the existing
noncanonical storage carrier with distinct representatives of the value one.
Their two original rational coordinates, including noncanonical finite
endpoints, are serialized and independently interpreted by the oracle. The
Python checker regenerates all heads, queries, intervals and seeded inputs
from the fixed corpus contract, preventing degenerate regenerated fixtures
from silently replacing the required cases.

The pinned python-flint 0.9.0 / FLINT 3.6.0 oracle enumerates exact qqbar roots
and evaluates every query there. It reuses the independent rational root/sign
helper shared with the SignDet oracle in `scripts/oracle/exact_roots.py`.
Changes to that neutral helper or the shared qqbar wrapper select the full CI verification suite. Domain validation uses FLINT
polynomial gcd and exact endpoint evaluation. No Lean answer, remainder chain,
certificate or count enters the expected-value computation.

Cases include zero and constant heads, root-free heads, squarefree and repeated
heads, positive and negative leading coefficients, rational denominator
clearing, non-monic definitions, zero/constant/common-factor/high-degree queries,
finite and infinite endpoints, endpoint roots, equal/reversed intervals and
invalid infinity pairs. Guarded finite integer endpoints additionally compare
positive clearing followed by every integer Tarski query and the existing
half-open integer Sturm count.
Those comparisons have root-free endpoints, exactly as the public agreement
theorem requires; they do not claim equality when an endpoint is a root.
A separate Lean guard covers the upper-endpoint distinction: the integer API
counts the root at 1 in (0, 1], while the field frontend refuses that domain.

Produced certificates replay on their original literal inputs as Lean controls
and reject an altered value for ordinary, prepared and count certificates. Their actual certificate values are serialized
and independently compared to the exact oracle answers. The oracle checks
those numerical values and domain refusal, not
arbitrary-certificate soundness or coefficient-evidence transport. Existing
kernel proofs, stale/corrupted-evidence controls, non-Archimedean downstream
fixtures and axiom inventories remain separately required. This corpus does
not add tower algorithms or provide computational performance evidence.

## Reproduction

From the repository root, with the pinned python-flint available:

```sh
lake build hexsturm_emit_fixtures +HexSturm.Conformance
.lake/build/bin/hexsturm_emit_fixtures > /tmp/sturm.jsonl
cmp /tmp/sturm.jsonl conformance-fixtures/HexSturm/sturm.jsonl
python3 scripts/oracle/sturm_flint.py --check
python3 scripts/oracle/test_sturm_flint.py
```

For an isolated local Python environment, replace the last two commands with
`uv run --with python-flint==0.9.0 python …` using the same script arguments.
The existing single-job oracle runner contains one `HexSturm` tuple; there is
no new workflow or runner. Its Sturm tuple runs the nine refusal-control tests
before the exact oracle. Required CI treats unavailable oracle dependencies
as a failure. The corpus is deterministic, including rejected seeded inputs;
no sampling retry excludes unfavorable cases.

[Oracle output](oracle.log) records all 192 cases with zero failures.
[Refusal controls](negative-controls.log) exercise wrong sign sums, counts,
domain acceptance, prepared results, Boolean replay fields, integer agreement
raw-storage interpretation, missing/duplicate stream cases, altered fixed
inputs and malformed schema/library/type tags. The accompanying source/corpus bindings identify
exactly the checked inputs; full family acceptance and Phases 6–7 remain separate.
