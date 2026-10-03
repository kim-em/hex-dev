# Nested sign replay experiment

This native Lean experiment tests automatic collection and reuse of coefficient
signs at two predecessor levels, including signs inside serialized inputs. It
uses the existing root descriptors, arithmetic reduction, BKR sign producer,
strict coefficient codecs and shared graph checker.

The selected positive roots satisfy `a² = 2`, `b² = a + 2` and `c² = b + 2`.
The coefficient domains are ℚ, ℚ(a) and ℚ(a)(b). Two identical queries at c
are `X - b`, both positive: `1 < a < 2` implies `1 < b < 2`, so
`b² - b - 2 = (b - 2)(b + 1) < 0` and therefore `c > b`. The existing
encoder shares the identical leaf, leaving two graph entries.

Local wrappers record each exact reduced polynomial and computed sign during
construction and production. Inverse candidates use the existing inverse
algorithm and are packed through the same collector. During replay, packing
uses exact lookup and preserves canonical zero; a missing key exits with
status 17 before replacement sign evaluation. Inversion is outside the
replay vocabulary and rejects with status 18. Rational bottom-level arithmetic
remains ordinary.

Before checking, the graph is serialized and decoded recursively with the
existing `Element.signCodec`. Every nonzero input coefficient, including
stored scale factors, must match a fact for its exact polynomial and claimed
sign. The context's immutable predecessor coefficients and prebuilt One
values are checked too. Re-encoding must give identical graph bytes.
These facts remain trusted in-memory producer outputs; independently checked
child certificates and kernel proofs are outside this prototype.

The default run uses only construction/production facts. `--collect-replay`
also checks in collection mode; the driver verifies that this discovers no
extra keys. `--omit` and `--omit-level-one` remove actually used nonconstant
arithmetic facts at either level. `--omit-literal` removes a nonconstant
input fact before a fresh decode. Each rejects without replacement sign work.
A separate `--keys-only` probe uses a nonmonic head, different stored
representatives of the same value, and conjugate ±√2 contexts. An absent
representative and a copied opposite-sign literal both reject.

Build and check with:

```sh
lake -d experiments/NestedReplay build
python3 experiments/NestedReplay/run.py /tmp/nested-replay-check
```

The output directory must not exist. The driver sets `LEAN_ABORT_ON_PANIC=1`,
retains stdout/stderr and exits, and records source/binary hashes, CPU placement,
counts and timings. Six blocks use one automatically leased CPU and reverse
the order of three adjacent arms on alternating blocks:

```sh
python3 experiments/NestedReplay/run.py /tmp/nested-replay-pairs --pairs 6
```

Each arm checks its graph 200 times. The fact and ordinary arms record call
counters but disable used-key collection during timing. The plain arm builds
a separate equivalent tower with unmodified library instances and no wrapper
instrumentation. Changing positive nonces prevent whole-result sharing; both
instrumented arms must execute exactly 200 times their preliminary check's
packing calls. Input decoding, construction and production are outside the
replay timer. The plain arm also uses prebuilt input data.

Counts describe executed wrappers, including constants and inverse-result
packing, rather than Tarski queries or formal complexity bounds. Nonconstant
sign evaluation may use the existing interval shortcut. Facts for constants
are deliberately required in this experiment. The public `Element.pack`
native fallback still recomputes missing signs; a production strict mode
would require changing that behavior.

The IO instrumentation is local `unsafe` diagnostic code, with no public API,
field instance, query kernel or SPEC change. Process exits are not a proved
total rejection interface. Production work still needs safe automatic
evidence collection, checked child certificates with literal context bindings,
ordinary-kernel correspondence and assembly, and broader cost evidence.
The linear fact-list scan here does not prescribe a production data structure.

The arithmetic-only observations in [results](results/summary.json) refer to
the source revision recorded there. Their timers include used-key collection,
and their inputs retain producer-computed signs. They are not measurements of
the current full-input experiment or evidence for a production speedup.
All completed observations remain retained. This experiment does not complete
Phase-4 performance requirements.
