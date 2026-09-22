# Determinant redesign prototypes

These experiments are excluded from production dispatch, default builds and
CI. The fixture producer is Mathlib-free; proof probes are module builds.

From the repository root:

```sh
lake build Determinant.Fixture > /tmp/determinant-fixture.log 2>&1
lake build Determinant.Arithmetic
python3 experiments/Determinant/arithmetic.py /tmp/determinant-fixture.log /tmp/determinant-arithmetic
python3 experiments/Determinant/full.py /tmp/determinant-arithmetic/fixture.json experiments/Determinant/Full.lean
lake build Determinant.Audit
python3 experiments/Determinant/full_measure.py /tmp/determinant-arithmetic/fixture.json /tmp/determinant-full
```

Use new output directories and run serially. Runners refuse to overwrite
results and stop the batch on failure/timeout. Every measured invocation has
a 60-second ceiling; each batch has a four-minute ceiling. All observations
are retained. The generator is limited to the fixed 4×4 quadratic witness;
it is not a general determinant implementation.

`arithmetic.py` compares list replay, independent ring proofs and cached ring
proofs for equivalent identities in different statement formats.
`full_measure.py` includes every prototype lemma and compares production
Hex and explicit Mathlib proofs of the same generated statement. Witness
production and source generation are outside the proof clocks.

`Arithmetic.lean` uses scalar arithmetic helpers from Mathlib's Bird
certificate module. It never calls the Bird determinant evaluator or
`norm_det`. `Audit.lean` checks axioms, counts proof nodes, and tests generic
arithmetic and rejection of unequal normal forms.

The recorded integer microbenchmark's exact support source is in its archive.
The working support is generalized to arbitrary commutative rings; a rerun
is not byte-for-byte reproduction of that integer-only implementation.

See [results](../../reports/determinant-redesign-results.md) for measurements,
limitations, negative results and the next hypotheses.
