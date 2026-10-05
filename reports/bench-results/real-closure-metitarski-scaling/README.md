# MetiTarski second-stage degree ladder

The input is `Yⁿ + α³ + 1` for `n = 3,5,7,9`. Here α is the least real
root of the exact degree-15 polynomial from de Moura and Passmore,
CADE 2013, section 4. Degree three is the original second-stage problem;
the higher odd degrees form a derived scaling family. The original
transcription and the unsupported printed `tower8` premise are recorded in
[the input report](../../real-closure-phase4.md).

The computational operation is the native complete-root producer in
`Hex.RealClosure.Bench.measureMetiSecond`. The same coefficient field and
selected embedding are used at each degree. Construction of the degree-15
predecessor, least-root checks and second polynomial takes place in the
measured runner's setup, outside its inner timer. The timer includes complete
second-stage root production, the root-count check, an input-function
reference read, full coefficient-prefix extraction and normalization, and
the ordinary harness hash/consumer. Functional root equations,
coefficient/evidence serialization and independent oracle checks are outside
timing. Preparation is forced before timing, followed by one explicit untimed
second-stage warm-up in every child. This makes the reported operation follow
a previous call at every degree; ordinary harness autotuning may make further
probe calls. The child timeout includes preparation and this warm-up. A runtime function read inside
every iteration takes the full coefficient count; this argument controls
actual input data and keeps the pure root producer inside the timed loop.
The prefix is proved to be literally the original polynomial at its full size.

## Protocol

The source is committed and clean before capture. The driver checks the
lean-bench pin, builds and snapshots both executables, binds their hashes and
records dependency pins, compiler, host, CPU model and initial activity.
It leases one automatically selected CPU and pins the parent and all children
to it. Activity is context; every completed point is retained.

Before timing, the snapshot emits each original polynomial, predecessor
selection and second-stage descriptor. Both native replays, the root equation
and multiplicity are checked. The FLINT oracle independently reconstructs
the selected predecessor and exact coefficients, constructs the unique
negative odd radical, and checks the descriptor interval and Thom word.
For positive `c = α³ + 1`, odd `Yⁿ+c` has exactly one real root, and
`n*β^(n−1)` is nonzero. This avoids repeating expensive global canonical
power arithmetic for an already constructed exact radical. The oracle checks
semantic root selection; it does not reimplement the native replay checker.
Functional snapshot emission must match the committed fixtures byte for byte.
The benchmark snapshot also emits the exact polynomial from its measured input
constructor; its degree, actual predecessor descriptor, first polynomial and coefficient serialization must
match that independently checked fixture.

The ordinary lean-bench custom schedule runs six fixed trial-major rounds,
visiting degrees `3,5,7,9` in each. Its 0.5-second target guides ordinary
autotuning toward a final batch just past half that duration; a slower call
is reported alone. Actual batch durations and repeat counts are retained.
The operational child timeout is 120 seconds. There is one
capture and no automatic rerun or dropped attempt. Caps and errors remain
in the export and report, including when the harness returns exit status 2
with a complete failed-point export; incomplete rungs cannot establish the full-family
model. Raw total nanoseconds and
inner-repeat counts are retained in the harness export. The capture process
has a 3600-second operational safeguard. A process timeout retains command
logs and failure metadata, but lean-bench only writes its export at the end,
so an interrupted parent may not retain individual point records.

The declared model is `n³` for this fixed coefficient context. The report
includes every per-degree median and range, `time/n³`, compact polynomial
bytes and complete selected-descriptor bytes. The ordinary harness's verdict,
slope and dropped-leading count are retained separately. These finite
shared-host observations do not prove asymptotic or total bit complexity.
They do not establish whole-library Phase 4 readiness or cover other tower
families, normalization policies or the unsupported `tower8` input.

## Commands

```sh
python3 scripts/bench/real_closure_metitarski_scaling.py \
  --output /absolute/external/capture-directory \
  --oracle-python /absolute/path/to/pinned-python
python3 scripts/bench/analyze_real_closure_metitarski_scaling.py \
  /absolute/external/capture-directory
```

The pinned oracle is python-flint 0.9.0 / FLINT 3.6.0. Existing CI builds the
functional emitter, compares its four rows with the committed fixtures and
runs the independent semantic and mutation checks. Scientific timing is
collected separately on the shared host.

<!-- metitarski-results -->
## Retained results

Measured source: `14b03f863df9341f411a1f3df7461f41b82d4ab7`.

Completed samples: 24 of 24 attempts.

| Degree | Completed trials | Median ms | Range ms | Median ms / n³ | Head bytes | Descriptor bytes |
| --- | --- | --- | --- | --- | --- | --- |
| 3 | 6 | 213.826 | 147.106–259.516 | 7.919 | 59 | 21688 |
| 5 | 6 | 469.475 | 314.137–533.768 | 3.756 | 65 | 60790 |
| 7 | 6 | 731.902 | 611.720–984.343 | 2.134 | 71 | 121854 |
| 9 | 6 | 1299.439 | 1051.705–1600.144 | 1.782 | 77 | 204318 |

Harness verdict: `inconclusive`; slope: `-1.404948`; leading points dropped: `0`.

The ranges and medians use every completed trial. The raw export retains each
batch duration, repeat count, signal-floor flag and failure status; the derived
analysis retains them by degree. The harness verdict is reported separately
from these descriptive observations. This finite ladder does not establish
asymptotic complexity or acceptance of the other Phase 4 families.
<!-- /metitarski-results -->

[Raw capture and source snapshots](../real-closure-metitarski-scaling-14b03f/README.md).
