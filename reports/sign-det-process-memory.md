# Whole-process memory for sign determination

The collector runs existing compiled callbacks once per child, using the shared
lean-bench profiler with cold inputs. It retains native peak resident memory and
Valgrind Massif page profiles as separate observations. These cover the entire
child, including runtime startup, input preparation and result consumption.
They complement the [operation allocation counts](sign-det-allocation-method.md);
they do not measure the bytes occupied by live Lean objects or isolate callback
memory from preparation.

Native peak resident memory comes from the Linux kernel’s `VmHWM` counter, read
by the pinned harness. Massif uses `--pages-as-heap=yes`: it counts mapped pages,
including code, data, stacks and allocator reserves. Mapped address space need
not be resident. The [Massif manual](https://valgrind.org/docs/manual/ms-manual.html#ms-manual.using-massif)
explains this distinction. Massif’s default peak-recording tolerance is 1%;
the page summaries take the maximum of every retained snapshot. On a Massif record, `process_peak_rss_kib` is the instrumented child’s RSS; on a
native record, it is native RSS. Only native records enter the resident table.
Instrumented resident memory and elapsed time include Valgrind overhead and are not native
memory values or scientific timing samples.

## Captures and validation

The [joint captures](data/sign-det-process-memory/4c790b883d/joint/metadata.json)
and [remaining captures](data/sign-det-process-memory/4c790b883d/other/metadata.json)
retain all 162 successful profiles: 81 native and 81 Massif. Both collections
bind source `4c790b883dc708ab1a479bdd3d52897309a8ce69`, the same compiled binary
and clean pinned harness. They used automatically leased CPU 70 on `chungus2`.
Host load is retained at collection entry and after every capture; no completed
point was removed and no quiet-core test was used.

Three trial-major rounds cover each selected parameter. Adjacent native/Massif
pairs alternate AB/BA order. Each child must report one successful cold
invocation, its exact operation and parameter, and its clean source revision.
Before collection, existing input and callback validators check the exact
known-root answers, full ternary matrix dimensions and height-sensitive output
fingerprints. Every observed answer must match the validated callback digest and its paired
native/profile answer. A Boolean checker digest is `hash true`: it records
acceptance, while the function/parameter, registration and binary bindings
identify the input; that digest alone does not identify a certificate.

Each archive keeps the original metadata, all stdout/stderr and page snapshots,
and the verified source reconstruction patch. Compressed files retain hashes
of both stored and original bytes; collection metadata is copied unchanged.
CI re-runs the retained input checks, reconstructs the expected callback digests,
and validates every retained file, capture order, answer and memory summary.
The stderr captures also retain mimalloc’s process-exit statistics through
`MIMALLOC_SHOW_STATS=1`. These describe allocator page/chunk commitments and
reserves, and are diagnostic output rather than validated live-object counts.

The measurement driver uses no custom native wrapper and changes no compiled
algorithm or scientific timing settings.

## Native observations

Values are medians of all three native captures in MiB. Startup and preparation
are included. The sparse table/graph cases prepare their existing full fixtures;
the joint cases use the original combined input constructor. These values
therefore cannot compare isolated production and replay working sets.

| Family / callback | Parameters | Native peak resident medians (MiB) |
| --- | --- | --- |
| joint / Joint.runComparison | 3, 7, 15 | 72.270, 72.273, 73.434 |
| joint / Joint.runCheckReduced | 3, 7, 15 | 72.574, 72.082, 74.695 |
| sparse / runProduce | 64, 256, 1024 | 72.781, 74.594, 87.949 |
| sparse / runTree | 64, 256, 1024 | 72.188, 73.703, 86.082 |
| sparse / runGraph | 64, 256, 1024 | 72.820, 74.699, 86.375 |
| matrix / MaximalMatrix.runSolveDimension | 9, 27, 81 | 72.316, 72.758, 72.277 |
| matrix / MaximalMatrix.runCheckDimension | 9, 27, 81 | 72.832, 72.809, 72.078 |
| height / Height.runReduce | 8192, 65536, 524288 | 72.301, 72.820, 72.621 |
| height / Height.runCheck | 8192, 65536, 524288 | 72.770, 72.453, 73.082 |

At 1024 sparse queries, production reaches about 88 MiB resident memory,
compared with about 73 MiB at 64 queries. The small matrix, joint and height
ranges mostly remain near the roughly 70–75 MiB whole-process baseline. These
observations do not identify asymptotic live-memory growth. The existing
[matrix timing records](sign-det-maximal-matrices.md) include native resident
memory at the larger dimension 729; this capture does not replace that range.

## Page-profile attribution and limits

Most page peaks are 4,587,094,016 bytes; the largest is 4,587,253,760 bytes.
Under Valgrind, the retained degree-three joint-comparison peak tree attributes 3,221,237,760
bytes to runtime thread-stack mappings. The allocator also reserves address
space in large chunks. These reservations dominate the page totals while the
native resident totals are much smaller. The page profiles explain why their
nearly flat peaks are not evidence of constant algorithmic storage. For example,
the sparse 1024-query resident peak grows by about 15 MiB from its 64-query
value while its mapped-page peak remains unchanged.

The captures supply process-memory observations and startup attribution over
four existing families. They do not supply live-object accounting, operation
boundaries for memory, nested coefficient/evidence allocation, or new scaling
verdicts. The previously inconclusive joint and matrix timing results remain
inconclusive. Full Phase-4 attestation still requires the outstanding evidence.

## Reproduce

After committing sources and building `hexsigndet_bench`, run:

```sh
python3 scripts/bench/sign_det_memory.py --groups joint \
  --valgrind /path/to/valgrind --output /path/to/new-joint-captures
python3 scripts/bench/sign_det_memory.py --groups sparse matrix height \
  --valgrind /path/to/valgrind --output /path/to/new-other-captures
```

Output directories must be new and outside the worktree. The driver checks
build freshness and source, executable and harness identity before and after
collection. Failed output remains available. Ctrl-C, SIGTERM and SIGHUP stop the owned
profile process group and leave the collection marked failed with retained output.
