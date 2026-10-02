# Operation-scoped sign-determination allocation

`scripts/bench/sign_det_allocations.py` profiles the existing Mathlib-free
`hexsigndet_bench` callbacks. The companion C wrapper counts successful
allocation requests while the selected callback executes. It checks that the
callback has one object argument and an explicitly supported result ABI in the
actual generated C. A typed return preserves pointer, Boolean and integer
results. Each instrumented result must match an uninstrumented invocation on
the same input.

The three counter groups are:

- Lean object requests: `lean_alloc_small_object_core` and `lean_alloc_object`;
- other direct mimalloc requests: `mi_malloc`, `mi_malloc_small` and `mi_new_n`;
- GMP requests: `__gmp_default_allocate` and `__gmp_default_reallocate`.

A thread-local nesting counter charges only the outermost wrapped request.
For example, a Lean object request that calls `mi_malloc` is charged once to
the Lean group. GMP reallocation charges the newly requested size, including
in-place reallocation. Small Lean object sizes include alignment already
performed before calling the wrapped allocation entry point. These are
cumulative requested bytes, not live heap or memory retained after a call.
The groups are separate from the benchmark's reserved `alloc_bytes` field.

Valgrind DHAT ad-hoc events independently sum the requested bytes and request
counts. The driver rejects disagreement with the wrapper's counters, overflow,
missing callback instrumentation and repeated callbacks. Activation at callback
entry and deactivation at exit exclude preparation and process initialization;
stack truncation does not change the counters. The operation must be pure and
single-threaded. The wrapper does not propagate activation to spawned threads.

The controlled `SIGN_DET_CHECK` fixture requests 64 Lean bytes, 56 other
mimalloc bytes and 160 GMP bytes in six requests. Its nested allocator calls
and a separate 256-byte request outside the callback must not add events.
Pointer and Boolean result variants both return the expected value and report
280 DHAT units in six events.

Before interpreting a capture as complete coverage, audit the measured binary's
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
`/home/kim/.local/state/hex/issue-10377-profiles/allocation-method-check`.
The degree-three comparison recorded 6,283,680 Lean bytes, 624,384 other
mimalloc bytes and 10,490,208 GMP bytes. Reduced graph checking recorded
1,672,112, 130,416 and 2,584,336 bytes respectively. These two preliminary
observations used a dirty collector checkout with exact source hashes and
retained collector snapshots. They demonstrate working instrumentation;
they are not a scaling result or full Phase-4 evidence. Wider matrices,
coefficient sizes, nested fields and all remaining performance gates still
require their specified evidence.
