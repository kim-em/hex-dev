# Determinant redesign prototypes

These experiments are excluded from production dispatch, default builds and
CI. The fixture producer is Mathlib-free; proof probes are module builds.

From the repository root:

```sh
# Force the fixture-producing declaration to run even with a warm Lake cache.
rm -f .lake/build/lib/lean/Determinant/Fixture.olean
lake build Determinant.Fixture > /tmp/determinant-fixture.log 2>&1
lake build Determinant.Arithmetic
python3 experiments/Determinant/arithmetic.py /tmp/determinant-fixture.log /tmp/determinant-arithmetic
python3 experiments/Determinant/full.py /tmp/determinant-arithmetic/fixture.json experiments/Determinant/Full.lean
lake build Determinant.Audit
python3 experiments/Determinant/full_measure.py /tmp/determinant-arithmetic/fixture.json /tmp/determinant-full
python3 experiments/Determinant/full_measure.py /tmp/determinant-arithmetic/fixture.json /tmp/determinant-transport --mode transport
python3 experiments/Determinant/full_measure.py /tmp/determinant-arithmetic/fixture.json /tmp/determinant-controls --mode controls
python3 experiments/Determinant/full_measure.py /tmp/determinant-arithmetic/fixture.json /tmp/determinant-shared --mode shared
```

Use new output directories and run serially. Runners refuse to overwrite
results and stop the batch on failure/timeout. Every measured invocation has
a 60-second ceiling; each batch has at most a four-minute ceiling. All observations
are retained. The generator is limited to the fixed 4×4 quadratic witness;
it is not a general determinant implementation.

`arithmetic.py` compares list replay, independent ring proofs and cached ring
proofs for equivalent identities in different statement formats.
`full_measure.py` includes every prototype lemma and compares production
Hex and explicit Mathlib proofs of the same generated statement. Witness
production and source generation are outside the proof clocks.

The default full-proof clock is synchronous complete declaration elaboration,
including statement and all kernel checks. `--clock profile` selects the older
tactic/kernel component diagnostic. Do not compare those metrics directly.
`--mode arithmetic --clock profile` compares ordinary and opaque-certificate
arithmetic; `--mode transport` holds the witness fixed while changing transport;
`--mode controls` compares improved transport against production tactics.
`--mode deferred` compares delayed ordinary normalization with cached traversal
of the same shared Bird expression. `--mode shared` compares the latter with
explicit Mathlib and production Hex. Cases are `quadratic4` (default),
`independent4`, `common-factor4`, and `linear6`; the last requires python-flint
to generate an independent target. These are forward literal equality probes,
not a general production frontend. All candidate construction and checking,
including the supplied-target comparison, is inside the declaration clock.

For compiled value experiments, use a Python environment with `python-flint`
(the retained runs use 0.9.0). Build before measuring, then select one case:

```sh
lake build determinant_experiment
python experiments/Determinant/runtime.py /tmp/determinant-int --ring int --dimension 16
python experiments/Determinant/runtime.py /tmp/determinant-poly --ring poly --dimension 4
python experiments/Determinant/runtime.py /tmp/determinant-rat --ring rat --dimension 8
python experiments/Determinant/runtime.py /tmp/determinant-dyadic --ring dyadic --dimension 8 --spread 64
python experiments/Determinant/runtime.py /tmp/determinant-modular --ring int --dimension 32 --modular
python experiments/Determinant/runtime.py /tmp/determinant-flat --ring int --dimension 128 --flat
python experiments/Determinant/runtime.py /tmp/determinant-owned --ring int --dimension 32 --owned
python experiments/Determinant/runtime.py /tmp/determinant-word --ring int --dimension 128 --word
python experiments/Determinant/runtime.py /tmp/determinant-univariate --ring univariate --dimension 4
python experiments/Determinant/word_loop.py /tmp/determinant-flat /tmp/determinant-c
python experiments/Determinant/verify.py /tmp/determinant-value-verification
python experiments/Determinant/word_verify.py /tmp/determinant-c-verification
```

These are independent commands, not instructions to run a grid. Choose the
next case from the preceding result. The runtime runner stops its whole batch
on a timeout/failure, and never launches a larger case automatically. After a
timeout, do not manually advance a comparable dimension/coefficient ladder.
The polynomial cases use fixed fixtures: only dimension 4, dense shape, and
the default bits/spread arguments are accepted.
`--modular` compares existing ordinary CRT and divisor routes without fallback
and attributes ordinary CRT stages. `--flat` changes just its elimination route.
`--owned` and `--word` compare the experimental owned Lean buffer and hoisted
raw-word arithmetic. The univariate case compares sparse/dense Bareiss and cold
nine-point interpolation, returning the same dense coefficient array. It is
limited to the fixed 4×4 quadratic fixture.

`word_loop.py` requires a C compiler and consumes a retained `--flat`, `--owned`
or `--word` batch containing the exact matrix and prime list. It compiles a
value-only C diagnostic, compares all prime images with FLINT in two AB/BA pairs,
and removes the generated shared object. Its hard batch limit is 60 seconds.
It is never linked into Lean proofs or production Hex. `word_verify.py` checks
its small/boundary/singular/pivot cases with the undefined-behavior sanitizer;
the retained host uses Clang and its standalone UBSan runtime.

Native clocks include input-reference reading, arithmetic and storing the result
before the stop clock; generated C was inspected to verify that ordering.
Inputs, JSON serialization and external validation are outside the native
clocks. The runner retains executable/source hashes, inputs, process resource
metrics, FLINT answers and all samples. `verify.py` checks boundary dimensions,
singularity, initial row pivoting, and the executable's Mathlib-free import
closure; it is not a timing experiment. Bird and scaling remain experimental
value routines with differential checks, not new universal correctness proofs.

`Arithmetic.lean` uses scalar arithmetic helpers from Mathlib's Bird
certificate module. It never calls the Bird determinant evaluator or
`norm_det`. `Audit.lean` checks axioms, counts proof nodes, and tests generic
arithmetic and rejection of unequal normal forms.
`DeferredAudit.lean` checks generic-ring shared/deferred determinant proofs,
rejection of a wrong supplied target, and their axiom dependencies. The
`Deferred.lean` recurrence is an attributed experimental adaptation of Mathlib's
Bird certificate evaluator; the scalar normalizer itself is reused.

The recorded integer microbenchmark's exact support source is in its archive.
The working support is generalized to arbitrary commutative rings; a rerun
is not byte-for-byte reproduction of that integer-only implementation.

See [results](../../reports/determinant-redesign-results.md) for measurements,
limitations, negative results and the next hypotheses.
