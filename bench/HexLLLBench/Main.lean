/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

import HexLLLBench

public section

/-!
Benchmark registrations for `hex-lll`.

This first Phase 4 slice covers the executable `LLLState` operations and the
top-level `lll.firstShortVector` entry point. Fixture construction builds the
integer Gram-Schmidt state once in `prep`; the timed targets measure the state
update or projection surfaces and return compact checksums of the affected
cells. The `lll.firstShortVector` registrations use the three non-degenerate
HexLLL Phase-4 input families named in `libraries.yml`.

Scientific registrations:

* `runOfBasisBzRecombinationChecksum`: build the initial integer state for a
  square BZ-style triangular recombination basis.
* `runOfBasisRandomBoundedChecksum`: build the initial integer state for a
  bounded-coefficient square basis.
* `runOfBasisHarshCubicChecksum`: build the initial integer state for a
  square basis whose entry bit-length grows linearly in the dimension.
* `runSizeReduceColumnChecksum`: one targeted column reduction against the
  previous row of a prepared `(n + 3) x (n + 3)` state.
* `runSizeReduceChecksum`: full reduction of the final prepared row.
* `runSwapStepChecksum`: one adjacent swap at the final prepared row.
* `runGramSchmidtCoeffChecksum`: rational coefficient recovery from stored
  integer `ν` and `d`.
* `runPotential`: prefix product of the stored Gram determinants.
* `runFirstShortVectorBZRecombinationChecksum`: fixed BZ-shaped triangular
  recombination basis with three lifted local factors.
* `runFirstShortVectorRandomBoundedChecksum`: random-bounded integer bases
  with `|entry| <= 30` at `n in {30, 45, 60, 75, 90, 120, 150, 180}`.
* `runFirstShortVectorHarshCubicChecksum`: harsh-cubic bases with entry
  bit-length approximately `3.3 * n` at
  `n in {15, 20, 25, 30, 35, 40, 45, 50, 55}`.

Informational external comparator:

* `fpLLL via fplll-ffi`: in-process FFI registrations call `libfplll`
  through the `fplll-ffi` shim — one C++ call per request, no
  subprocess. The shim's `lean_fplll_lll_reduce` symbol is resolved
  by `HexLLL/ffi/lean_hexlll_provider.c` via `dlsym(RTLD_DEFAULT, ...)`
  after an opportunistic `dlopen` of `HEX_FPLLL_FFI_LIB`, mirroring
  the Isabelle binary-path override. The shim is built by
  `scripts/oracle/setup_fplll_ffi.sh` (clone+lake build of
  `leanprover/fplll`), keeping hex free of any Lake dependency on
  it. The comparator is classified informational in
  `SPEC/Libraries/hex-lll.md` because fpLLL's floating-point
  Gram-Schmidt implementation (Nguyen-Stehle) bypasses the
  exact-integer operand-size drift this verified implementation
  pays. Ratios are recorded for orientation but do not block
  Phase 4. The conformance oracle keeps its independent fpylll
  cross-check at `scripts/oracle/lll_fpylll.py --check`; only the
  speed comparator switched to the FFI shim.
* `fpLLL certified path`: the same in-process `fplll-ffi` call returns
  the flat `(B', U, V)` candidate payload directly; the Lean target
  runs `LLLProvider.certifyFlat`, so the measured path is fpLLL
  candidate production plus the executable checker. Companion
  checker-only targets cache one candidate after warmup and re-run
  only `certCheck`, giving the checker's cost share. Public-dispatch
  verify targets check that, when an `fplll-ffi` provider is
  intentionally loaded via `HEX_FPLLL_FFI_LIB`, the dispatch tally
  records at least one accepted candidate.

External comparator:

* `verified Isabelle LLL (AFP LLL_Basis_Reduction; Haskell extraction from
  Zenodo record 2636367, https://zenodo.org/records/2636367, archive SHA-256
  `5c975aeb2033540b8f9a05d2ffac87dca0f258e887a5807edefbe60178a547e0`)` is
  registered as the Phase-4 gating comparator for the bottom/shared
  `phase4.input_families` rungs. `scripts/oracle/setup_lll_isabelle.sh`
  downloads, verifies, caches, and patches the archive, then builds
  `svp_verified`. The patch
  `scripts/oracle/patches/lll-isabelle/01-persistent-stdin.patch`
  rewrites the Haskell entry point so the binary loops on stdin instead
  of accepting a single matrix file path on argv. Set
  `HEX_LLL_ISABELLE_SVP` to an already-built binary to avoid setup in
  the first measured call.
* `verified Isabelle certified-LLL` uses the same Zenodo archive's
  `svp_certified` target (`haskell_sources/Main_Certified.hs`), not the
  later AFP modular-HNF certifier. It verifies the external fpLLL
  two-transform certificate, re-runs verified LLL to confirm reducedness,
  and reports the same first-vector squared norm. Set
  `HEX_LLL_ISABELLE_CERTIFIED_SVP` to an already-built persistent driver
  to avoid setup in the first measured call.

## Comparator-call protocol

The `fpLLL via fplll-ffi` comparator is an in-process FFI call: each
request marshals the matrix into the `Array String` payload the
provider hook expects, calls `LLLProvider.providerReduce`, and reads
the flat `(status, rows, cols, has_inverse, reduced, U, V?)` reply.
No subprocess, no IPC, no interpreter startup; the per-call overhead
is the FFI marshalling cost alone.

The `verified Isabelle LLL` comparator uses a persistent subprocess
per `SPEC/benchmarking.md` (post-#3657) "External comparators /
Process call": one `svp_verified` driver is spawned per
`lake exe hexlll_bench run` invocation, and each measured call sends
one framed request to its stdin and reads one framed reply from its
stdout.

The `verified Isabelle certified-LLL` comparator uses the same
persistent protocol with the archive's `svp_certified` driver. Each
request still shells out to the `fplll` binary from inside the generated
certifier, unlike Hex's in-process `fplll-ffi` certified path.

**Isabelle framing.** Each request is one line containing the input
matrix in Haskell's `[[Integer]]` read syntax — exactly the string
produced by `matrixHaskell` — terminated by `\n`. Isabelle returns
the squared norm of its first reduced row.

**Isabelle lifetime.** The Isabelle driver is spawned lazily on first
use into the module-level `isabelleChildRef`
(`IO.Ref (Option PersistentComparator)`) and reused for every
subsequent call in the same `hexlll_bench` process. The child's
stdin is held by the bench process via `Child.takeStdin`; on process
exit, the OS reaps the driver via EOF on stdin.

**Isabelle error handling.** If `requestLine` raises any `IO` error,
the bench wiring drops the cached child handle, re-spawns the
Isabelle driver from `scripts/oracle/setup_lll_isabelle.sh`, and
retries the request once. Persistent failure (e.g. setup script
failure or repeated driver crash) surfaces as an `IO.userError`.

**Per-call overhead.** Piping 10000 trivial inputs (`[[1,0],[0,1]]`)
through the patched Isabelle binary on the audit host takes ~110 ms
wall total (median of 5 trials), of which ~22 ms is the one-time
GHC startup; per-call Isabelle protocol overhead is ~9 µs in steady
state. The `fplll-ffi` FFI call carries no interpreter startup; its
per-call cost is one `dlsym`-resolved C++ call plus the
`matrixToEntries` marshalling.

**Interaction with `setup_fixed_benchmark`.** `lean-bench` spawns one
fresh `hexlll_bench` child process per measured repeat of a fixed
benchmark, so each repeat starts with a cold `isabelleChildRef`; the
process-call comparator registrations set `minTotalSeconds := 1.0`,
forcing the fixed child to run enough inner iterations to amortize
the one-time GHC start inside the child. For `fplll-ffi`, the
per-process cost is the one-time `dlopen` performed lazily on the
first probe via `HEX_FPLLL_FFI_LIB`.

**Driver path overrides.** `HEX_FPLLL_FFI_LIB` selects the
`fplll-ffi` shared library that the bench `dlopen`s at start-up
(see `HexLLL/ffi/lean_hexlll_provider.c`). The Isabelle binary path
is controlled by `HEX_LLL_ISABELLE_SVP`; the Isabelle certified binary
path is controlled by `HEX_LLL_ISABELLE_CERTIFIED_SVP`.

**Signal-floor setting.** HexLLL scientific parametric registrations set
`signalFloorMultiplier := 1.0`. The timed rows come from child-side
inner-repeat batches, not parent-side process spawn wall time, and recent
scheduled hosts have shown multi-second executable startup while the
algorithmic batches remain well within their per-call caps. Disabling the
spawn-floor filter here keeps those child-side measurements usable; the JSON
export still records `spawn_floor_nanos` for auditability.
-/


def main (args : List String) : IO UInt32 :=
  LeanBench.Cli.dispatch args
