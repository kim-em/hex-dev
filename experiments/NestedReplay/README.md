# Nested sign replay experiment

This native Lean experiment tests whether the existing BKR certificate checker
can reuse intermediate coefficient signs at two predecessor levels, rejecting
a missing fact before computing its replacement. It uses the existing root
descriptors, arithmetic reduction, sign producer and shared graph checker.

The selected positive roots are

```
a² = 2,       b² = a + 2,       c² = b + 2.
```

The coefficient domains are ℚ, ℚ(a) and ℚ(a)(b). The two identical queries at
c are `X - b`. Their signs are both positive: `1 < a < 2` implies `1 < b < 2`,
so `b² - b - 2 = (b - 2)(b + 1) < 0` and hence `c > b`. The existing encoder
shares the identical leaf, leaving two graph entries.

`Main.lean` installs local diagnostic wrappers around packing into each
coefficient extension. During construction and certificate production they
record the exact reduced polynomial and its computed sign. During replay they
look up those exact keys, preserve canonical zero, and exit with status 17 on
a miss. No missing key falls back to `Context.signPoly`. Inversion is outside
the replay vocabulary and exits with status 18 if attempted during replay.
Ordinary arithmetic at the rational bottom level remains available.

The default run uses only facts collected during construction and production.
`--collect-replay` additionally runs the checker in collection mode, allowing
a comparison of the fact sets. `--omit` removes an actually used nonconstant
fact at the second coefficient level; `--omit-level-one` does so at the first.
Both must reject. No list of intermediate signs is supplied by hand.

Build and check with:

```sh
lake -d experiments/NestedReplay build
python3 experiments/NestedReplay/run.py /tmp/nested-replay-check
```

The output directory must not exist. The driver retains native stdout/stderr,
exit codes, source and binary hashes, CPU placement, counts and timings. A
six-pair comparison uses one automatically leased CPU and adjacent arms in
alternating order:

```sh
python3 experiments/NestedReplay/run.py /tmp/nested-replay-pairs --pairs 6
```

Each timed arm checks the same graph 200 times. Both record used keys and
wrapper counters. Changing positive nonces prevent sharing the complete
Boolean result between runs; the checker ignores the nonce's value. Cached
call counts must equal 200 times the preliminary check's counts. Counts
describe executed diagnostic wrappers, including constant sign evaluations;
they are not counts of Tarski queries or formal complexity bounds.

This is a runtime experiment using local `unsafe` IO instrumentation. Its
in-memory facts are trusted outputs of the same producer, not independently
verified serialized child certificates. Exiting a diagnostic process is not
a proved total rejection interface. No kernel proof is assembled here, and
the prototype adds no public arithmetic API, field instance or query kernel.
It does not establish the full nested replay contract or Phase-4 performance.

Production work still needs automatic evidence collection without unsafe
instrumentation, checked child certificates and literal context bindings,
ordinary-kernel proofs connecting cached operations to native arithmetic,
and broader examples and cost evidence. The fact lookup here is a linear
list scan; this experiment does not prescribe the production data structure.
