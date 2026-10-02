# Allocation in complete sign matrices

The complete finite moment system contains every ternary sign word of length
`s`, once each, in the library's fixed order. Its dimension is `r = 3^s`.
`MaximalMatrix.runSolve` executes the rational solver, converts counts to
integers and checks the literal identities. `runCheck` checks the supplied
integer inverse and moment identities. Both include the dense inverse identity
check. Preparation constructs and validates the input before either callback;
no polynomial, root enumeration or Tarski query runs in these callbacks.
These are finite matrix inputs, not a claim that one polynomial realizes every
sign word at the larger sizes. The [ordinary matrix report](sign-det-maximal-matrices.md)
describes the inputs, coefficient-operation model and separate running times.

The [capture method](sign-det-allocation-method.md) measures successful
allocation requests during the actual callback. It intercepts specified Lean,
direct mimalloc and GMP entry points, suppressing nested interception. GMP
reallocation contributes the newly requested size. The three buckets describe
entry points, not every object or every possible allocator path. Their sum is
cumulative requested bytes, not peak live memory. Instrumented elapsed times
and RSS include Valgrind and preparation overhead and are not used as timing
or live-memory evidence.

The [retained records](data/sign-det-allocations/matrix-25b179f5c/metadata.json)
identify clean source `25b179f5c8f2143cd77753cd8c802d364aefd958`, its executable,
compiler, Valgrind 3.27.1, generated callback ABI, allocator inventory,
direct-call audit and exact collector sources. On `chungus2`, the driver leased
CPU 90 and ran three fixed trial-major rounds. Each round visits query counts
1 through 5, corresponding to dimensions 3, 9, 27, 81 and 243, and runs solve
then check. Host load is recorded without filtering or an idleness test.

All 30 scheduled captures completed. Each contains exactly one callback,
passes event-origin and per-bucket attribution checks, and gives the same
answer as its ordinary native invocation. Every answer also matches the
[ordinary dimension-parameter benchmark](data/sign-det-maximal-matrices/ff35bd9da-dimensions/runSolveDimension.json)
for the same matrix. Checks must return `true` (hash `0xb`); matching a
consistently false result would not count as success. All three repetitions of
each operation and size have identical request counts and byte totals.

Requested bytes per callback:

| Dimension | Operation | `lean_alloc_*` | Direct mimalloc | GMP | Sum |
| --- | --- | ---: | ---: | ---: | ---: |
| 3 | Solve | 9,440 | 296 | 13,152 | 22,888 |
| 3 | Check | 3,568 | 0 | 312 | 3,880 |
| 9 | Solve | 91,880 | 2,160 | 256,632 | 350,672 |
| 9 | Check | 22,816 | 0 | 5,616 | 28,432 |
| 27 | Solve | 1,218,464 | 16,664 | 4,728,632 | 5,963,760 |
| 27 | Check | 217,216 | 0 | 75,816 | 293,032 |
| 81 | Solve | 18,156,968 | 131,808 | 85,416,768 | 103,705,544 |
| 81 | Check | 2,248,048 | 0 | 909,792 | 3,157,840 |
| 243 | Solve | 289,632,032 | 1,050,632 | 1,533,691,240 | 1,824,373,904 |
| 243 | Check | 23,328,784 | 0 | 10,235,160 | 33,563,944 |

At dimension 243, GMP accounts for approximately 84.1% of solve's intercepted
bytes and 30.5% of check's. These observations characterize the current complete
callbacks; they do not establish an asymptotic allocation law or resolve the
ordinary report's inconclusive running-time verdicts.

The [retained dimension-callback attempt](data/sign-det-allocations/matrix-dimension-failed-25b179f5c/metadata.json)
has state `failed`. Its first native and instrumented answers agree, but the
wrapper records no callback or allocation events, so the collector rejects the
capture through its one-callback counter check. A separate adversarial test
checks rejection when a callback is recorded but all request counts are zero;
truly zero-allocation callbacks are outside this capture method. The generated C contains those
forwarding definitions. A
[post-capture inspection](data/sign-det-allocations/matrix-dimension-failed-25b179f5c/post-capture-inspection.json)
of the executable with the same recorded hash retains its callback symbol
inventory, its full unfiltered output, exact command and tool version: the dimension forwarding functions are absent, while `runSolve`
and `runCheck` are present. This later observation does not replace the
original capture metadata. The successful schedule selects the actual `runSolve` and `runCheck`
callbacks and expresses the same dimensions using their query-count parameter.
The failed attempt remains retained, including its logs and raw empty event
file; it supplies no allocation observation. No unchanged measurement is
rerun or completed observation discarded.

Both collections retain the three controlled ABI checks and collector sources.
Raw DHAT files and generated matrix C are stored losslessly with deterministic
gzip compression. The regression suite verifies the fixed successful schedule,
raw hashes and attribution, allocator inventories, native and ordinary answers, repeat agreement,
report totals, generated callback ABI and failed-capture rejection. The source
and executable hashes equal the
[joint collection](data/sign-det-allocations/joint-25b179f5c/metadata.json);
its retained source reconstruction applies to these same measured sources.
The before/after hashes remain equal for both matrix schedules. The later
inspection also records hashes of the retained failed native log and raw event
file; those two hashes were not recorded at capture.

Reproduce the successful schedule on the measured source with installed
Valgrind and its headers:

```sh
python3 scripts/bench/sign_det_allocations.py \
  --functions Hex.SignDetBench.MaximalMatrix.runSolve Hex.SignDetBench.MaximalMatrix.runCheck \
  --parameters 1 2 3 4 5 --trials 3 \
  --valgrind /path/to/valgrind --include /path/to/valgrind/include \
  --output /path/to/new-capture-directory
python3 -m unittest scripts.bench.test_sign_det_allocations
```

The collector checks instrumented/native answer agreement. A newly collected
dataset also needs an independent answer check before it can be interpreted as
a successful computation. The original directories remain under
`/home/kim/.local/state/hex/issue-10377-profiles/` as
`allocation-matrix-queries-25b179f5c` and `allocation-matrices-25b179f5c`.

This collection supplies allocation observations for the complete finite sign
matrix solve and checker. Independent coefficient-height and nested-field
families, live memory and the remaining Phase-4 requirements still need their
own evidence. Dimension 729 from the ordinary timing family is outside this
allocation schedule. It does not complete #10377 or the separate rank obligation #10352.
