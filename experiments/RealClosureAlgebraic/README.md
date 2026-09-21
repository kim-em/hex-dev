# Selected algebraic-root representation experiment

An isolated, Mathlib-free test of canonical-zero storage with noncanonical
nonzero representatives. The main example selects positive sqrt(2) from
`(X²−2)(X²−3)` using `(1,3/2]`. This is a genuine algebraic extension, and
its zero test calls existing rational polynomial gcd and integer Sturm code.

- [Algebraic.lean](Algebraic.lean): checked descriptors, zero test, arithmetic,
  inversion with local factor splitting, explicit transport, two multiplication arms.
- [Tests.lean](Tests.lean): kernel-reduced regression checks and the storage invariant.
- [Transfer.lean](Transfer.lean): proved noninjective transfer of the existing
  `DensePoly.divMod` and `gcd`, conditional on operation preservation and zero reflection.
- [Nested.lean](Nested.lean): a second genuine algebraic level, the fourth root of 2,
  using the irreducible quadratic `Y²−sqrt(2)` over the first representation.
- [Check.lean](Check.lean), [verify.py](verify.py): runtime checks and an independent
  python-flint/exact-quadratic-arithmetic oracle, comparing complete outputs.
- [Bench.lean](Bench.lean), [PROTOCOL.md](PROTOCOL.md), [measure.py](measure.py):
  prepared fixed comparisons using lean-bench and a predeclared AB/BA schedule.
- [Independent review and disposition](REVIEW.md).
- [Results and proposed next steps](../../reports/real-closure-algebraic-experiment.md).

From the repository root, with its pinned lean-bench dependency available:

```sh
lake -d experiments/RealClosureAlgebraic build Tests Transfer algebraicCheck algebraicBench
experiments/RealClosureAlgebraic/.lake/build/bin/algebraicCheck > /tmp/algebraic-checks.jsonl
python3 experiments/RealClosureAlgebraic/verify.py < /tmp/algebraic-checks.jsonl
python3 experiments/RealClosureAlgebraic/summarize.py
python3 experiments/RealClosureAlgebraic/audit.py
```

The verifier needs `python-flint` (the retained run used 0.9.0).
`measure.py` refuses to overwrite the retained `results/timing` directory.
To intentionally reproduce the experiment, preserve/move that directory first;
the script records every sample and does not retry.

This is not a production context API. `valid` is checked for the fixtures, not
carried in every descriptor. `transport` is exercised only for a root-preserving
split and is not safe for arbitrary unrelated descriptors. `canonical` and
`signSqrt2` know the selected positive quadratic root and are test utilities;
they are not a general algebraic sign algorithm. `Nested.zero` relies on the
particular quadratic's irreducibility and does not implement general second-level
root isolation. The semantic correspondence of these routines is checked on
examples, not proved universally. The transfer theorems themselves have no
proof holes and use only `propext` and `Quot.sound`.

No Mathlib, hex-interval, transcendental provider, universal tower construction,
BKR, infinite-endpoint root isolation, or production caching is introduced
by this experiment. The existing CI job builds the experiments and runs the
independent finite checks; scientific timing remains a local shared-host run. Dyadic isolating intervals here belong to the
existing real-root code; they do not require hex-interval.

## Storage policy and context refinement

[Policy protocol](POLICY-PROTOCOL.md) fixes E1/E2 and their acceptance checks.
`Policy.lean` compares unreduced storage, monic remainder retention, smaller
definitions, and a fixture-specific irreducibility fast path. `PolicyCheck.lean`
and `verify_policy.py` cross-check complete results in FLINT's Q[X]/(X⁴−2).
`Refinement.lean` transports a genuinely changed upper defining coefficient,
live values and context bindings after a lower-level split.

`PolicyBench.lean` measures division/gcd at both levels with prepared inputs.
`PolicyTrace.lean` enables untimed callbacks to count actual zero tests at each
level; their hashes are checked against the timed outputs. `measure_policy.py`
controls only the fixed AB/BA schedule and retains all harness results;
`summarize_policy.py` checks every sample and trace hash. Results live in
[results/policy](results/policy), with interpretation in the
[storage/refinement report](../../reports/real-closure-storage-experiments.md).

```sh
lake -d experiments/RealClosureAlgebraic build policyCheck policyBench policyTrace refinementCheck
python3 experiments/RealClosureAlgebraic/verify_policy.py
python3 experiments/RealClosureAlgebraic/summarize_policy.py
```

The verifier defaults to retained results; `--results DIR` checks newly emitted
`checks.jsonl` and `refinement.jsonl`, as CI does. Policy elements enforce
literal nonzero storage, while semantic zero correctness remains a tested
fixture property, not a new universal Lean theorem. Their experimental
constructors are not the production opaque validated API. Refinement tickets
test full context/operand binding, not a general certificate checker.

Both experiment workspaces require the root Hex package by path, reusing its
compiled library artifacts. CI runs `audit.py --live` for current import,
proof-hole and link checks. Run `audit.py` without that flag to additionally
check the retained timing source identities; historical measurements stay
bound to their measured sources and do not prevent later API maintenance.
