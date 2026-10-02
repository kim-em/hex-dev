# Operation-scoped sign-determination allocation

`scripts/bench/sign_det_allocations.py` profiles the existing Mathlib-free
`hexsigndet_bench` callbacks. The companion C wrapper counts successful
allocation requests while the selected callback executes. It checks that the
callback has one object argument and an explicitly supported result ABI in the
actual generated C. A typed return preserves pointer, Boolean and integer
results. Each instrumented result must match an uninstrumented invocation on
the same input.

The three groups classify the entry point at which a request is intercepted:

- `lean_alloc_*` entry points: `lean_alloc_small_object_core` and `lean_alloc_object`;
- direct mimalloc entry points: `mi_malloc`, `mi_malloc_small` and `mi_new_n`;
- GMP default allocator entry points: `__gmp_default_allocate` and `__gmp_default_reallocate`.

A thread-local nesting counter charges only the outermost wrapped request.
For example, a Lean object request that calls `mi_malloc` is charged once to
the `lean_alloc_*` group. Runtime-internal Lean array growth and the inline
large-constructor path can call `mi_malloc` directly, so their requests appear
in the direct mimalloc group. The first group is not a total count of all Lean
objects. GMP reallocation charges the newly requested size, including
in-place reallocation. Small Lean object sizes include alignment already
performed before calling the wrapped allocation entry point. These are
cumulative requested bytes, not live heap or memory retained after a call.
The groups are separate from the benchmark's reserved `alloc_bytes` field.

Valgrind DHAT ad-hoc events record the same requested bytes and request
counts as the wrapper. The driver classifies each event by its emitting wrapper
frame and checks
per-group totals against the counters. This verifies event provenance and bucket
assignment; it does not independently detect missing allocators or incorrect
size arguments. The driver rejects disagreement, overflow,
missing callback instrumentation and repeated callbacks. Activation at callback
entry and deactivation at exit exclude preparation and process initialization;
stack truncation does not change the counters. The operation must be pure and
single-threaded. The wrapper does not propagate activation to spawned threads.

The controlled `SIGN_DET_CHECK` fixture requests 64 bytes at `lean_alloc_*` entry points,
56 bytes at direct mimalloc entry points and 160 bytes at GMP entry points in six requests. Its nested allocator calls
and a separate 256-byte request outside the callback must not add events.
Pointer, Boolean and 64-bit integer variants preserve their expected return
values and report 280 DHAT units in six events. Run all three with the driver
`--self-check`; every capture also runs these fixtures before measurement.

The driver requires every wrapped allocator symbol to be defined in the actual
executable and retains the allocator symbol inventory. A disassembly audit
rejects unwrapped direct `mi_*` calls from callers outside `mi_`/`_mi_`
routines. It does not inspect `_mi_*`, libc allocation or `operator new`
targets, and is not a complete indirect-call or foreign-allocation detector. Before interpreting a
capture as complete coverage, also audit the measured binary's
allocation entry points and generated/inlined paths. The wrappers count the
listed client requests; allocator backing pages, arbitrary foreign malloc
calls and alternative allocators are outside these counters. They do not
establish a portable total-process allocation API. Instrumented elapsed times
and peak RSS include Valgrind overhead and are not scientific timing samples.

The driver automatically leases a CPU, uses a fixed trial-major schedule, keeps
all completed samples and failed output, and records source/binary identities,
callback ABI and wrapper hashes. Scientific running-time measurements continue
through the existing lean-bench registrations and their required schedules.
Allocation captures do not resolve inconclusive running-time verdicts.

Example after `lake build hexsigndet_bench`:

```sh
python3 scripts/bench/sign_det_allocations.py \
  --functions Hex.SignDetBench.Joint.runComparison Hex.SignDetBench.Joint.runCheckReduced \
  --parameters 3 5 9 --trials 3 \
  --valgrind /path/to/valgrind --include /path/to/valgrind/include \
  --output /path/to/new-capture-directory
```

Pilot records are retained under
`/home/kim/.local/state/hex/issue-10377-profiles/allocation-final-validated-8e34be08d`.
A portable copy of the metadata, counters, output and compressed raw events is
in [the validation data](data/sign-det-allocations/validation/metadata.json).
The regression suite checks hashes, allocator-frame attribution and native
result agreement against these retained records.
The degree-three comparison recorded 6,283,680 bytes at `lean_alloc_*` entry
points, 624,384 bytes at direct mimalloc entry points and 10,490,208 bytes at
GMP entry points. Reduced graph checking recorded
1,672,112, 130,416 and 2,584,336 bytes respectively. These two validation
observations used clean collector revision
`8e34be08d9bce5636fc5478ce08ab4ed7915a6ec` and retained uninstrumented result
comparisons, source hashes and raw output. Earlier pilot captures remain retained separately. The Lake build checked the
benchmark through its ordinary incremental dependency rules; it did not force
recompilation of every unchanged module. They demonstrate working instrumentation;
they are not a scaling result or full Phase-4 evidence. Wider matrices,
coefficient sizes, nested fields and all remaining performance requirements still
require their specified evidence.
