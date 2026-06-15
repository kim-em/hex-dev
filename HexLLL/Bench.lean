import HexLLL
import Batteries.Lean.IO.Process
import LeanBench

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
  `kim-em/fplll-ffi`), keeping hex free of any Lake dependency on
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
  smoke targets guard that, when an `fplll-ffi` provider is
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

namespace Hex.LLLBench

/-- Row-major deterministic fixture for one integer basis. -/
structure IntBasisInput where
  rows : Nat
  cols : Nat
  entries : Array Int
  deriving Repr, BEq, Hashable

/-- Prepared `LLLState` plus stable indices used by the benchmark targets. -/
structure StateInput where
  rows : Nat
  cols : Nat
  state : LLLState rows cols
  j : Fin rows
  k : Fin rows
  hjk : j.val < k.val

instance : Hashable StateInput where
  hash input :=
    hash (input.rows, input.cols, input.j.val, input.k.val)

/-- Matrix input for benchmarking `LLLState.ofBasisUnchecked` itself. -/
structure OfBasisInput where
  rows : Nat
  cols : Nat
  basis : Matrix Int rows cols
  j : Fin rows
  k : Fin rows
  hjk : j.val < k.val

instance : Hashable OfBasisInput where
  hash input :=
    hash (input.rows, input.cols, input.j.val, input.k.val)

/-- Prepared basis for `lll.firstShortVectorUnchecked` benchmarks. -/
structure FirstShortVectorInput where
  rows : Nat
  cols : Nat
  basis : Matrix Int rows cols
  hn : 1 ≤ rows

instance : Hashable FirstShortVectorInput where
  hash input := hash (input.rows, input.cols)

/-- Deterministic small integer entry generator keyed by shape and position.
The diagonal offset keeps the prepared bases independent in the benchmark
range while still giving size-reduction and swap updates nontrivial data. -/
def entryValue (rows cols row col salt : Nat) : Int :=
  let raw :=
    ((row + 1) * 37 +
      (col + 3) * 29 +
      (rows + 5) * 17 +
      (cols + 7) * 13 +
      salt) % 5
  let centered := Int.ofNat raw - 2
  if col < row then
    0
  else if row = col then
    Int.ofNat (rows + 3)
  else
    centered

/-- Deterministic row-major matrix fixture of shape `rows x cols`. -/
def flatBasis (rows cols salt : Nat) : Array Int :=
  if rows = 0 || cols = 0 then
    #[]
  else
    (Array.range (rows * cols)).map fun idx =>
      let row := idx / cols
      let col := idx % cols
      entryValue rows cols row col salt

/-- Reconstruct a typed dense matrix from row-major entries. -/
def matrixOfFlat (input : IntBasisInput) : Matrix Int input.rows input.cols :=
  Matrix.ofFn fun i j => input.entries.getD (i.val * input.cols + j.val) 0

/-- Deterministic square matrix fixture. -/
def generatedBasis (rows salt : Nat) : Matrix Int rows rows :=
  Matrix.ofFn fun i j => entryValue rows rows i.val j.val salt

/-- Build the executable LLL state for a deterministic matrix. -/
def stateOf (b : Matrix Int n m) : LLLState n m :=
  LLLState.ofBasisUnchecked b

/-- Per-parameter fixture: a prepared `(n + 3) x (n + 3)` LLL state. -/
def prepStateInput (n : Nat) : StateInput :=
  let rows := n + 3
  let cols := rows
  let basis := generatedBasis rows 197
  let j : Fin rows := ⟨n + 1, by simp [rows]⟩
  let k : Fin rows := ⟨n + 2, by simp [rows]⟩
  { rows := rows
    cols := cols
    state := stateOf basis
    j := j
    k := k
    hjk := by
      change n + 1 < n + 2
      omega }

/-! ## Phase-4 `lll.firstShortVector` input families. -/

/-- BZ-shaped triangular coefficient block from `HexLLL/EmitFixtures.lean`. -/
def bzRecombinationCoeff (factor col : Nat) : Int :=
  match factor, col with
  | 0, 0 => 1
  | 0, 1 => 1
  | 1, 1 => 1
  | 1, 2 => 1
  | 2, 2 => 1
  | _, _ => 0

/-- BZ-shaped triangular recombination basis. -/
def bzRecombinationBasis : Matrix Int 3 3 :=
  Matrix.ofFn fun i j =>
    bzRecombinationCoeff i.val j.val

/-- Fixed BZ recombination input. -/
def bzRecombinationInput : FirstShortVectorInput :=
  { rows := 3
    cols := 3
    basis := bzRecombinationBasis
    hn := by decide }

instance : Nonempty FirstShortVectorInput :=
  ⟨bzRecombinationInput⟩

initialize bzRecombinationInputRef : IO.Ref FirstShortVectorInput ←
  IO.mkRef bzRecombinationInput

/-- Trivial 2×2 identity input. Reducing it is instant, so an end-to-end
`svp_certified` request on it measures the comparator's fixed per-request
floor — process fork plus startup — with negligible n-dependent work. This
is the same trivial request the §Per-call comparator overhead note uses to
quote the Isabelle-certified floor; registering it makes that floor a
committed, reproducible measurement the comparator plot can subtract. -/
def processFloorInput : FirstShortVectorInput :=
  { rows := 2
    cols := 2
    basis := Matrix.ofFn fun i j => if i = j then 1 else 0
    hn := by decide }

/-- POSIX-style LCG used to make committed random-bounded fixtures
reproducible from a seed. -/
def lcgStep (x : Nat) : Nat :=
  (1103515245 * x + 12345) % 2147483648

def lcgIterate (seed : Nat) : Nat → Nat
  | 0 => seed
  | k + 1 => lcgIterate (lcgStep seed) k

/-- Map a 31-bit LCG output into `[-30, 30]`. -/
def randomBoundedEntry (raw : Nat) : Int :=
  Int.ofNat (raw % 61) - 30

/-- LCG-generated upper-triangular random-bounded basis. -/
def randomBoundedBasis (n seed : Nat) : Matrix Int n n :=
  Matrix.ofFn fun i j =>
    if j.val < i.val then
      0
    else if i = j then
      Int.ofNat (n - i.val + 1)
    else
      randomBoundedEntry (lcgIterate seed (i.val * n + j.val + 1))

/-- Committed seed for the random-bounded family. The `#guard` below checks
that after size-reducing row 1 against row 0, the first Lovasz comparison
fails, so the next LLL outer-loop step performs a swap. -/
def randomBoundedSwapSeed : Nat := 8

/-- Parametric random-bounded input family. The scientific ladder is densified
at `n in {30, 45, 60, 75, 90, 120, 150, 180}`. -/
def prepRandomBoundedInput (n : Nat) : FirstShortVectorInput :=
  let rows := max n 1
  let basis := randomBoundedBasis rows randomBoundedSwapSeed
  { rows := rows
    cols := rows
    basis := basis
    hn := by
      exact Nat.le_max_right n 1 }

/-- Check that the first Lovasz comparison fails after the first
size-reduction pass, forcing at least one swap in the subsequent LLL step. -/
def firstLovaszCheckForcesSwap (input : FirstShortVectorInput) : Bool :=
  if hrows : 2 < input.rows then
    let sReduced := (LLLState.ofBasisUnchecked input.basis).sizeReduce 1
    let f0 : Fin input.rows := ⟨0, by omega⟩
    let f1 : Fin input.rows := ⟨1, by omega⟩
    let d0 : Fin (input.rows + 1) := ⟨0, by omega⟩
    let d1 : Fin (input.rows + 1) := ⟨1, by omega⟩
    let d2 : Fin (input.rows + 1) := ⟨2, by omega⟩
    let dkPrev := sReduced.d.get d0
    let dk := sReduced.d.get d1
    let dkNext := sReduced.d.get d2
    let B := (sReduced.ν.get f1).get f0
    let lovaszLhs : Int := 4 * (Int.ofNat dkNext * Int.ofNat dkPrev + B ^ 2)
    let lovaszRhs : Int := 3 * (Int.ofNat dk ^ 2)
    lovaszLhs < lovaszRhs
  else
    false

#guard firstLovaszCheckForcesSwap (prepRandomBoundedInput 30)

/-- Entry scale for the verified-Isabelle harsh-cubic regime, whose
documented bit-length is approximately `3.3 * n`. -/
def harshCubicScale (n : Nat) : Int :=
  Int.ofNat (2 ^ ((33 * n) / 10))

/-- Harsh-cubic basis with entries around `2^(3.3n)`. The triangular spine
keeps the fixture independent while the off-diagonal LCG perturbations make
the reduction path nontrivial. -/
def harshCubicBasis (n : Nat) : Matrix Int n n :=
  Matrix.ofFn fun i j =>
    let scale := harshCubicScale n
    let noise := randomBoundedEntry (lcgIterate (97 + n) (i.val * n + j.val + 1))
    if j.val < i.val then
      0
    else if i = j then
      scale
    else
      noise

/-- Parametric harsh-cubic input family. The scientific ladder is densified at
`n in {15, 20, 25, 30, 35, 40, 45, 50, 55}`. -/
def prepHarshCubicInput (n : Nat) : FirstShortVectorInput :=
  let rows := max n 1
  let basis := harshCubicBasis rows
  { rows := rows
    cols := rows
    basis := basis
    hn := by
      exact Nat.le_max_right n 1 }

def getCachedInput (ref : IO.Ref (Option FirstShortVectorInput))
    (mk : Unit → FirstShortVectorInput) : IO FirstShortVectorInput := do
  match (← ref.get) with
  | some input => return input
  | none =>
      let input := mk ()
      ref.set (some input)
      return input

initialize randomBoundedInput30Ref : IO.Ref (Option FirstShortVectorInput) ←
  IO.mkRef none

initialize randomBoundedInput45Ref : IO.Ref (Option FirstShortVectorInput) ←
  IO.mkRef none

initialize randomBoundedInput60Ref : IO.Ref (Option FirstShortVectorInput) ←
  IO.mkRef none

initialize randomBoundedInput75Ref : IO.Ref (Option FirstShortVectorInput) ←
  IO.mkRef none

initialize randomBoundedInput90Ref : IO.Ref (Option FirstShortVectorInput) ←
  IO.mkRef none

initialize randomBoundedInput120Ref : IO.Ref (Option FirstShortVectorInput) ←
  IO.mkRef none

initialize randomBoundedInput150Ref : IO.Ref (Option FirstShortVectorInput) ←
  IO.mkRef none

initialize randomBoundedInput180Ref : IO.Ref (Option FirstShortVectorInput) ←
  IO.mkRef none

initialize harshCubicInput15Ref : IO.Ref (Option FirstShortVectorInput) ←
  IO.mkRef none

initialize harshCubicInput20Ref : IO.Ref (Option FirstShortVectorInput) ←
  IO.mkRef none

initialize harshCubicInput25Ref : IO.Ref (Option FirstShortVectorInput) ←
  IO.mkRef none

initialize harshCubicInput30Ref : IO.Ref (Option FirstShortVectorInput) ←
  IO.mkRef none

initialize harshCubicInput35Ref : IO.Ref (Option FirstShortVectorInput) ←
  IO.mkRef none

initialize harshCubicInput40Ref : IO.Ref (Option FirstShortVectorInput) ←
  IO.mkRef none

initialize harshCubicInput45Ref : IO.Ref (Option FirstShortVectorInput) ←
  IO.mkRef none

initialize harshCubicInput50Ref : IO.Ref (Option FirstShortVectorInput) ←
  IO.mkRef none

initialize harshCubicInput55Ref : IO.Ref (Option FirstShortVectorInput) ←
  IO.mkRef none

initialize harshCubicInput60Ref : IO.Ref (Option FirstShortVectorInput) ←
  IO.mkRef none

initialize harshCubicInput65Ref : IO.Ref (Option FirstShortVectorInput) ←
  IO.mkRef none

initialize certifiedRandomBounded30Ref : IO.Ref (Option (FirstShortVectorInput × Array Int)) ←
  IO.mkRef none

initialize certifiedRandomBounded45Ref : IO.Ref (Option (FirstShortVectorInput × Array Int)) ←
  IO.mkRef none

initialize certifiedRandomBounded60Ref : IO.Ref (Option (FirstShortVectorInput × Array Int)) ←
  IO.mkRef none

initialize certifiedRandomBounded75Ref : IO.Ref (Option (FirstShortVectorInput × Array Int)) ←
  IO.mkRef none

initialize certifiedRandomBounded90Ref : IO.Ref (Option (FirstShortVectorInput × Array Int)) ←
  IO.mkRef none

initialize certifiedRandomBounded120Ref : IO.Ref (Option (FirstShortVectorInput × Array Int)) ←
  IO.mkRef none

initialize certifiedRandomBounded150Ref : IO.Ref (Option (FirstShortVectorInput × Array Int)) ←
  IO.mkRef none

initialize certifiedRandomBounded180Ref : IO.Ref (Option (FirstShortVectorInput × Array Int)) ←
  IO.mkRef none

initialize certifiedHarshCubic15Ref : IO.Ref (Option (FirstShortVectorInput × Array Int)) ←
  IO.mkRef none

initialize certifiedHarshCubic20Ref : IO.Ref (Option (FirstShortVectorInput × Array Int)) ←
  IO.mkRef none

initialize certifiedHarshCubic25Ref : IO.Ref (Option (FirstShortVectorInput × Array Int)) ←
  IO.mkRef none

initialize certifiedHarshCubic30Ref : IO.Ref (Option (FirstShortVectorInput × Array Int)) ←
  IO.mkRef none

initialize certifiedHarshCubic35Ref : IO.Ref (Option (FirstShortVectorInput × Array Int)) ←
  IO.mkRef none

initialize certifiedHarshCubic40Ref : IO.Ref (Option (FirstShortVectorInput × Array Int)) ←
  IO.mkRef none

initialize certifiedHarshCubic45Ref : IO.Ref (Option (FirstShortVectorInput × Array Int)) ←
  IO.mkRef none

initialize certifiedHarshCubic50Ref : IO.Ref (Option (FirstShortVectorInput × Array Int)) ←
  IO.mkRef none

initialize certifiedHarshCubic55Ref : IO.Ref (Option (FirstShortVectorInput × Array Int)) ←
  IO.mkRef none

initialize certifiedHarshCubic60Ref : IO.Ref (Option (FirstShortVectorInput × Array Int)) ←
  IO.mkRef none

initialize certifiedHarshCubic65Ref : IO.Ref (Option (FirstShortVectorInput × Array Int)) ←
  IO.mkRef none

/-! ## Phase-4 `LLLState.ofBasis` input families. -/

/-- Entry generator for bounded random-looking square bases. -/
def ofBasisRandomBoundedEntry (rows row col salt : Nat) : Int :=
  let raw := ((row + 11) * 1_103 + (col + 7) * 2_009 + salt + rows * 97) % 61
  let centered := Int.ofNat raw - 30
  if col < row then
    0
  else if row = col then
    Int.ofNat (rows + 31)
  else
    centered

/-- Entry generator with input bit-length proportional to the dimension. -/
def ofBasisHarshCubicEntry (rows row col salt : Nat) : Int :=
  let sign : Int := if ((row + col + salt) % 2 = 0) then 1 else -1
  let low := ofBasisRandomBoundedEntry rows row col salt
  let bits := 3 * rows + ((row + 2 * col + salt) % 5)
  if col < row then
    0
  else if row = col then
    Int.ofNat (2 ^ bits)
  else
    sign * (Int.ofNat (2 ^ bits)) + low

/-- Deterministic row-major square basis for the random-bounded family. -/
def ofBasisRandomBoundedBasis (rows salt : Nat) : Matrix Int rows rows :=
  Matrix.ofFn fun i j => ofBasisRandomBoundedEntry rows i.val j.val salt

/-- Deterministic row-major square basis for the harsh-cubic family. -/
def ofBasisHarshCubicBasis (rows salt : Nat) : Matrix Int rows rows :=
  Matrix.ofFn fun i j => ofBasisHarshCubicEntry rows i.val j.val salt

/-- General constructor for an `LLLState.ofBasisUnchecked` benchmark fixture.
The benchmark parameter maps to `rows = n + 3`, so the final two row indices
are always available for the result checksum. -/
def prepOfBasisInput (n cols : Nat) (basis : Matrix Int (n + 3) cols) :
    OfBasisInput :=
  let rows := n + 3
  let j : Fin rows := ⟨n + 1, by simp [rows]⟩
  let k : Fin rows := ⟨n + 2, by simp [rows]⟩
  { rows := rows
    cols := cols
    basis := basis
    j := j
    k := k
    hjk := by
      change n + 1 < n + 2
      omega }

/-- Per-parameter fixture for the BZ recombination input family. -/
def prepOfBasisBzRecombinationInput (n : Nat) : OfBasisInput :=
  let rows := n + 3
  let basis := generatedBasis rows 311
  prepOfBasisInput n rows basis

/-- Per-parameter fixture for the random-bounded input family. -/
def prepOfBasisRandomBoundedInput (n : Nat) : OfBasisInput :=
  let rows := n + 3
  let basis := ofBasisRandomBoundedBasis rows 509
  prepOfBasisInput n rows basis

/-- Per-parameter fixture for the harsh-cubic input family. -/
def prepOfBasisHarshCubicInput (n : Nat) : OfBasisInput :=
  let rows := n + 3
  let basis := ofBasisHarshCubicBasis rows 887
  prepOfBasisInput n rows basis

/-- Stable checksum for integer vectors. -/
def intVectorChecksum (v : Vector Int n) : Int :=
  (List.finRange n).foldl
    (fun acc i => acc * 65_537 + v[i])
    0

/-- Stable checksum for natural vectors. -/
def natVectorChecksum (v : Vector Nat n) : Nat :=
  (List.finRange n).foldl
    (fun acc i => acc * 65_537 + v[i])
    0

/-- Stable checksum for two integer rows. -/
def intRowPairChecksum (M : Matrix Int n m) (i j : Fin n) : Int :=
  intVectorChecksum (M.row i) * 65_537 + intVectorChecksum (M.row j)

/-- Stable checksum for one row of the stored scaled-coefficient matrix. -/
def coeffRowChecksum (M : Matrix Int n n) (i : Fin n) : Int :=
  intVectorChecksum (M.row i)

/-- Stable checksum for a state update's affected row and determinant data. -/
def stateUpdateChecksum (s : LLLState n m) (i j : Fin n) : Int :=
  intRowPairChecksum s.b i j * 65_537 +
    coeffRowChecksum s.ν i * 257 +
    coeffRowChecksum s.ν j +
    Int.ofNat (natVectorChecksum s.d)

/-- Model for reducing one row against one previous row: one basis row update
over `m = n + 3` columns plus the affected coefficient prefix. -/
def sizeReduceColumnComplexity (n : Nat) : Nat :=
  2 * (n + 3)

/-- Model for reducing the final row against all earlier rows: `k` row updates
over `m` columns plus the triangular coefficient-prefix updates. -/
def sizeReduceComplexity (n : Nat) : Nat :=
  let rows := n + 3
  rows * rows + rows * rows

/-- Model for an adjacent swap update: one basis swap over `m` columns, one
determinant write, and linear coefficient updates in the affected rows/columns. -/
def swapStepComplexity (n : Nat) : Nat :=
  2 * (n + 3)

/-- Model for one stored rational coefficient projection. The executable body is
one rational division over stored Gram data, and the prepared fixture's
denominator bit-width grows linearly with the row parameter. -/
def gramSchmidtCoeffComplexity (n : Nat) : Nat :=
  n

/-- Model for multiplying the determinant prefix `d_1, ..., d_{rows-1}` with
determinant bit-width growth from the prepared integer fixture. -/
def potentialComplexity (n : Nat) : Nat :=
  let rows := n + 3
  rows * rows * rows

/-- Fixture-path LLL model for bounded-bit-size random bases. The committed
LCG seed is near-orthogonal and fires few swaps, so the measured public entry
point is dominated by the triangular size-reduction/ofBasis surface plus the
slowly growing exact-integer coefficient width. -/
def firstShortVectorRandomBoundedComplexity (n : Nat) : Nat :=
  n ^ 3 * Nat.log2 (n + 1)

/-- Fixture-path LLL model for harsh-cubic inputs. The input bit-width grows
linearly with `n`, but this committed near-orthogonal family does not exercise
the worst-case swap count; the public entry point scales with the quartic
row-operation surface and repeated exact-integer coefficient-growth factors
from the harsh fixture. -/
def firstShortVectorHarshCubicComplexity (n : Nat) : Nat :=
  n ^ 4 * (Nat.log2 (n + 1)) ^ 5

/-- Model for `LLLState.ofBasis`: Gram matrix construction plus one shared
Bareiss-style pass over the Gram matrix. -/
def ofBasisComplexity (rows cols : Nat) : Nat :=
  rows * rows * cols + rows * rows * rows

/-- BZ recombination `ofBasis` model for a square `(n + 3) x (n + 3)` basis. -/
def ofBasisBzRecombinationComplexity (n : Nat) : Nat :=
  let rows := n + 3
  ofBasisComplexity rows rows

/-- Random-bounded `ofBasis` model for a square `(n + 3) x (n + 3)` basis. -/
def ofBasisRandomBoundedComplexity (n : Nat) : Nat :=
  let rows := n + 3
  ofBasisComplexity rows rows

/-- Harsh-cubic `ofBasis` model: the same shared Bareiss-style pass, with a linear
entry bit-length factor from the fixture's `3 * rows + O(1)` bits and a
logarithmic exact-integer overhead. -/
def ofBasisHarshCubicComplexity (n : Nat) : Nat :=
  let rows := n + 3
  rows * ofBasisComplexity rows rows * Nat.log2 (rows + 1)

/-- Benchmark target: construct the initial integer LLL state for a basis. -/
def runOfBasisChecksum (input : OfBasisInput) : Int :=
  let s := LLLState.ofBasisUnchecked input.basis
  stateUpdateChecksum s input.j input.k

/-- Benchmark target for the BZ recombination input family. -/
def runOfBasisBzRecombinationChecksum (input : OfBasisInput) : Int :=
  runOfBasisChecksum input

/-- Benchmark target for the random-bounded input family. -/
def runOfBasisRandomBoundedChecksum (input : OfBasisInput) : Int :=
  runOfBasisChecksum input

/-- Benchmark target for the harsh-cubic input family. -/
def runOfBasisHarshCubicChecksum (input : OfBasisInput) : Int :=
  runOfBasisChecksum input

/-- Benchmark target: one targeted size-reduction step. -/
def runSizeReduceColumnChecksum (input : StateInput) : Int :=
  let s' := input.state.sizeReduceColumn input.j input.k input.hjk
  stateUpdateChecksum s' input.j input.k

/-- Benchmark target: full size reduction of the prepared final row. -/
def runSizeReduceChecksum (input : StateInput) : Int :=
  let s' := input.state.sizeReduce input.k.val
  stateUpdateChecksum s' input.j input.k

/-- Benchmark target: adjacent swap at the prepared final row. -/
def runSwapStepChecksum (input : StateInput) : Int :=
  let s' := input.state.swapStep input.k.val
  stateUpdateChecksum s' input.j input.k

/-- Benchmark target: recover one rational Gram-Schmidt coefficient from the
stored integer state and checksum its normalized numerator and denominator.
This is the computable body of `LLLState.gramSchmidtCoeff`; the public
projection is marked `noncomputable` for proof-layer signalling and cannot be
used directly as an executable benchmark target. -/
def runGramSchmidtCoeffChecksum (input : StateInput) : Int :=
  let q :=
    (((input.state.ν.get input.k).get input.j : Int) : Rat) /
      (input.state.d.get
        ⟨input.j.val + 1, Nat.succ_lt_succ input.j.isLt⟩ : Rat)
  q.num * 65_537 + Int.ofNat q.den

/-- Benchmark target: compute the LLL termination potential. -/
def runPotential (input : StateInput) : Nat :=
  input.state.potential

/-- `1/4 < 3/4`: the lower half of the `1/4 < δ ≤ 1` reducer precondition at the
bench δ = 3/4. -/
private theorem lllDeltaLower : (1 / 4 : Rat) < 3 / 4 := by
  grind

/-- `3/4 ≤ 1`: the upper half of the `1/4 < δ ≤ 1` reducer precondition at the
bench δ = 3/4. -/
private theorem lllDeltaUpper : (3 / 4 : Rat) ≤ 1 := by
  grind

/-- `121/400 < 3/4`: the lower-bound precondition for the certified δ = 121/400
reducer variant evaluated at the bench δ = 3/4. -/
private theorem lllCertifiedDeltaLower : (121 / 400 : Rat) < 3 / 4 := by
  grind

/-- Benchmark target: run LLL on one prepared basis and checksum the first row. -/
def runFirstShortVectorChecksum (input : FirstShortVectorInput) : Int :=
  intVectorChecksum
    (lll.firstShortVectorUnchecked input.basis (3 / 4)
      lllDeltaLower lllDeltaUpper input.hn)

/-- Benchmark target: run the public dispatched LLL path and checksum the
first row. If a real external provider is loaded, this target fails unless the
certified dispatch accepts at least one candidate. -/
def runDispatchedFirstShortVectorChecksum (input : FirstShortVectorInput) : IO Int := do
  LLLProvider.resetDiagnostics
  have hrows : 1 ≤ input.rows := input.hn
  let f0 : Fin input.rows := ⟨0, by omega⟩
  -- Drive the dispatch via the IO-based `tryReduce` so the provider call
  -- (and its diagnostic side-effects) fire eagerly (the pure `dispatch` uses
  -- `@[implemented_by]` side-effects that the compiled bench harness
  -- otherwise defers). Request the same stronger `(requestedDelta δ,
  -- requestedEta)` the public dispatch asks of the reducer; certification
  -- stays against `(δ, 11/20)`, exactly the path `dispatch` exposes to `lll`.
  let δ : Rat := 3 / 4
  let δFloat : Float := Float.ofInt (LLLProvider.requestedDelta δ).num
    / Float.ofNat (LLLProvider.requestedDelta δ).den
  let ηFloat : Float := Float.ofInt LLLProvider.requestedEta.num
    / Float.ofNat LLLProvider.requestedEta.den
  let entries := LLLProvider.matrixToEntries input.basis
  let candidate? ← LLLProvider.tryReduce
    (USize.ofNat input.rows) (USize.ofNat input.cols) entries
    δFloat ηFloat 0 true
  -- Track whether `certCheck` itself accepted, not merely whether the payload
  -- was shape-valid: `tryReduce`'s `accepted` tally counts shape validation,
  -- so guarding on it would pass even if certification rejected and we fell
  -- back to native. The smoke target must fail iff the certified path does.
  let (reduced, certified) ← match candidate? with
    | some cand =>
        let flat := #[0, Int.ofNat input.rows, Int.ofNat input.cols, 1]
          ++ cand.reduced ++ cand.transform ++ (cand.inverse?.getD #[])
        match LLLProvider.certifyFlat input.basis δ flat with
        | some triple => pure (triple.1, true)
        | none => pure (lllNative input.basis δ lllDeltaLower lllDeltaUpper input.hn, false)
    | none => pure (lllNative input.basis δ lllDeltaLower lllDeltaUpper input.hn, false)
  if LLLProvider.providerAvailable () && !certified then
    throw <| IO.userError
      "fplll provider loaded but the certified path rejected its candidate"
  return intVectorChecksum (Matrix.row reduced f0)

/-- Benchmark comparator observable: squared norm of Lean's first LLL vector.
The verified-Isabelle Haskell extraction reports the same scalar. Runs the
default native path (`lll.firstShortVectorUnchecked`, the approximation-steered
reducer with certified output). -/
def runFirstShortVectorNormSq (input : FirstShortVectorInput) : Int :=
  Vector.intNormSq
    (lll.firstShortVectorUnchecked input.basis (3 / 4)
      lllDeltaLower lllDeltaUpper input.hn)

/-- Benchmark comparator observable for the exact `d`/`ν` reducer: squared norm
of the first vector of `lllNative` run directly. This is the
fplll-independent exact integer reducer that the steered path demotes to its
certification fallback; measuring it directly keeps the exact-native curve of
the comparator plot independent of the steered default. -/
def runNativeFirstShortVectorNormSq (input : FirstShortVectorInput) : Int :=
  Vector.intNormSq
    ((lllNative input.basis (3 / 4) lllDeltaLower lllDeltaUpper input.hn).row
      ⟨0, Nat.lt_of_lt_of_le Nat.zero_lt_one input.hn⟩)

/-- Render an `Int` vector as Haskell list-literal syntax (`[a,b,c]`) for the
driver's stdin. -/
def intRowHaskell (v : Vector Int n) : String :=
  "[" ++ String.intercalate "," ((List.finRange n).map fun j => toString v[j]) ++ "]"

/-- Render an `Int` matrix as a Haskell list-of-lists literal (`[[..],[..]]`)
for the driver's stdin. -/
def matrixHaskell (b : Matrix Int n m) : String :=
  "[" ++
    String.intercalate "," ((List.finRange n).map fun i => intRowHaskell (b.row i)) ++
    "]"

initialize isabelleBinaryRef : IO.Ref (Option String) ← IO.mkRef none

initialize isabelleCertifiedBinaryRef : IO.Ref (Option String) ← IO.mkRef none

/-- Run a subprocess and throw on nonzero exit, returning its trimmed stdout. -/
def checkedProcessOutput (cmd : String) (args : Array String := #[]) : IO String := do
  let out ← IO.Process.output { cmd := cmd, args := args }
  if out.exitCode != 0 then
    throw <| IO.userError
      s!"process failed ({cmd}):\nstdout:\n{out.stdout}\nstderr:\n{out.stderr}"
  return out.stdout.trimAscii.toString

/-- Resolve the `svp_verified` driver path from the `HEX_LLL_ISABELLE_SVP` env
var or the setup script, caching it in the module ref. -/
def resolveIsabelleBinary : IO String := do
  if let some cached ← isabelleBinaryRef.get then
    return cached
  let path ←
    match (← IO.getEnv "HEX_LLL_ISABELLE_SVP") with
    | some p => pure p
    | none => checkedProcessOutput "scripts/oracle/setup_lll_isabelle.sh"
  isabelleBinaryRef.set (some path)
  return path

/-- Resolve the `svp_certified` driver path from the
`HEX_LLL_ISABELLE_CERTIFIED_SVP` env var or the setup script, caching it in the
module ref. -/
def resolveIsabelleCertifiedBinary : IO String := do
  if let some cached ← isabelleCertifiedBinaryRef.get then
    return cached
  let path ←
    match (← IO.getEnv "HEX_LLL_ISABELLE_CERTIFIED_SVP") with
    | some p => pure p
    | none => checkedProcessOutput "scripts/oracle/setup_lll_isabelle.sh" #["certified"]
  isabelleCertifiedBinaryRef.set (some path)
  return path

/-- Parse the driver's numeric squared-norm reply, throwing on non-numeric
output. -/
def parseIsabelleNormSq (text : String) : IO Int := do
  match text.trimAscii.toString.toNat? with
  | some n => return Int.ofNat n
  | none => throw <| IO.userError s!"svp_verified emitted non-numeric output: {text}"

/-- Persistent child process for a comparator that loops on stdin/stdout.

The `stdin` field is the writable handle extracted via `Child.takeStdin`;
the `child` field is the underlying handle (post-`takeStdin`, so its
`stdin` is `Unit`), kept so the process is not reaped while the
benchmark holds the comparator. -/
structure PersistentComparator where
  stdin : IO.FS.Handle
  child : IO.Process.Child
    { stdin := .null, stdout := .piped, stderr := .piped }

namespace PersistentComparator

/-- Spawn the comparator with piped stdio and take its stdin handle. -/
def spawn (cmd : String) (args : Array String := #[]) :
    IO PersistentComparator := do
  let raw ← IO.Process.spawn
    { cmd := cmd, args := args,
      stdin := .piped, stdout := .piped, stderr := .piped }
  let (stdin, child) ← raw.takeStdin
  return { stdin := stdin, child := child }

/-- Write one request line and read one reply line. The caller embeds
the framing protocol into `request`; this helper appends a newline,
flushes stdin, then blocks on `getLine`. -/
def requestLine (c : PersistentComparator) (request : String) : IO String := do
  c.stdin.putStr (request ++ "\n")
  c.stdin.flush
  c.child.stdout.getLine

end PersistentComparator

initialize isabelleChildRef : IO.Ref (Option PersistentComparator) ←
  IO.mkRef none

initialize isabelleCertifiedChildRef : IO.Ref (Option PersistentComparator) ←
  IO.mkRef none

/-- Lazily spawn the persistent `svp_verified` driver, or return the
cached handle. -/
def resolveIsabelleChild : IO PersistentComparator := do
  if let some ch ← isabelleChildRef.get then
    return ch
  let binary ← resolveIsabelleBinary
  let ch ← PersistentComparator.spawn binary
  isabelleChildRef.set (some ch)
  return ch

/-- Lazily spawn the persistent `svp_certified` driver, or return the
cached handle. -/
def resolveIsabelleCertifiedChild : IO PersistentComparator := do
  if let some ch ← isabelleCertifiedChildRef.get then
    return ch
  let binary ← resolveIsabelleCertifiedBinary
  let ch ← PersistentComparator.spawn binary
  isabelleCertifiedChildRef.set (some ch)
  return ch

/-- Send one matrix to the persistent driver and parse its reply.

On process death, EOF before a reply line, or any IO error from the
protocol, the cached handle is dropped, a fresh driver is spawned, and
the call retried once. Persistent failure surfaces as an `IO.userError`
from the retry path.

The `tag` argument is preserved for call-site documentation but is no
longer used to materialise per-call temp files. -/
def requestIsabelleLineWithRetry (request : String) : Nat → IO String
  | 0 => do
    let reply ← (← resolveIsabelleChild).requestLine request
    if reply.isEmpty then
      throw <| IO.userError "svp_verified closed stdout before replying"
    return reply
  | Nat.succ remaining => do
    try
      let reply ← (← resolveIsabelleChild).requestLine request
      if reply.isEmpty then
        throw <| IO.userError "svp_verified closed stdout before replying"
      return reply
    catch _ =>
      isabelleChildRef.set none
      requestIsabelleLineWithRetry request remaining

/-- The certified mirror of `requestIsabelleLineWithRetry`: one request/reply
against the persistent `svp_certified` driver, with a single respawn-and-retry
on process death or empty reply. -/
def requestIsabelleCertifiedLineWithRetry (request : String) : Nat → IO String
  | 0 => do
    let reply ← (← resolveIsabelleCertifiedChild).requestLine request
    if reply.isEmpty then
      throw <| IO.userError "svp_certified closed stdout before replying"
    return reply
  | Nat.succ remaining => do
    try
      let reply ← (← resolveIsabelleCertifiedChild).requestLine request
      if reply.isEmpty then
        throw <| IO.userError "svp_certified closed stdout before replying"
      return reply
    catch _ =>
      isabelleCertifiedChildRef.set none
      requestIsabelleCertifiedLineWithRetry request remaining

/-- Benchmark comparator target: send one basis to the `svp_verified` driver and
parse its squared-norm reply. -/
def runIsabelleShortVectorNormSq (_tag : String) (input : FirstShortVectorInput) :
    IO Int := do
  let request := matrixHaskell input.basis
  parseIsabelleNormSq (← requestIsabelleLineWithRetry request 1)

/-- Benchmark comparator target: send one basis to the `svp_certified` driver and
parse its certified squared-norm reply. -/
def runIsabelleCertifiedShortVectorNormSq (_tag : String) (input : FirstShortVectorInput) :
    IO Int := do
  let request := matrixHaskell input.basis
  parseIsabelleNormSq (← requestIsabelleCertifiedLineWithRetry request 1)

/-- Approximate `Rat → Float` for forwarding `δ` to the FFI provider. Precision
is not part of correctness: the certified path checks the resulting candidate
against the exact `δ` via integer arithmetic. Mirrors `LLLProvider.ratToFloat`
(which is private). -/
private def ratToFloat (r : Rat) : Float :=
  Float.ofInt r.num / Float.ofNat r.den

/-- Invoke fplll-ffi in-process via the dlopened provider and return the flat
`(status, rows, cols, has_inverse, reduced, U, V?)` payload. The same payload
shape powers both the raw fpLLL comparator (first-row checksum) and the
certified path (`LLLProvider.certifyFlat`), so one FFI call covers both.

Raises `IO.userError` if the provider is absent (no `HEX_FPLLL_FFI_LIB` /
unresolved `lean_fplll_lll_reduce`) or returns an error from `libfplll`. -/
def requestFpLLLFlat (input : FirstShortVectorInput) : IO (Array Int) := do
  if !LLLProvider.providerAvailable () then
    throw <| IO.userError
      "fplll-ffi provider absent — set HEX_FPLLL_FFI_LIB to libfplllffi"
  let δ : Rat := 3 / 4
  let entries := LLLProvider.matrixToEntries input.basis
  -- Request the same stronger `(requestedDelta δ, requestedEta)` the public
  -- dispatch asks of the reducer, so the certified curve measures the exact
  -- reducer call production makes; certification stays against `(δ, 11/20)`.
  match LLLProvider.providerReduce
      (USize.ofNat input.rows) (USize.ofNat input.cols) entries
      (ratToFloat (LLLProvider.requestedDelta δ)) (ratToFloat LLLProvider.requestedEta) 0 true with
  | .error e => throw <| IO.userError s!"fplll-ffi: {e}"
  | .ok flat => return flat

/-- Benchmark target: fpLLL reduction via fplll-ffi (one in-process C++ call
into `libfplll`) on one prepared basis; checksum the first reduced row.

The header `[status, rows, cols, has_inverse]` precedes the row-major reduced
basis at offset 4, so `flat[4 + j]` are the `cols` entries of the first row. -/
def runFpLLLFirstShortVectorChecksum (input : FirstShortVectorInput) : IO Int := do
  let flat ← requestFpLLLFlat input
  if flat.size < 4 + input.cols then
    throw <| IO.userError
      s!"fplll-ffi returned undersized payload (size {flat.size}, cols {input.cols})"
  return (List.range input.cols).foldl
    (fun acc j => acc * 65_537 + (flat[4 + j]!))
    0

def certifyPayloadChecksum (input : FirstShortVectorInput) (payload : Array Int) : IO Int := do
  match LLLProvider.certifyFlat input.basis (3 / 4 : Rat) payload with
  | some triple =>
      have hrows : 1 ≤ input.rows := input.hn
      let f0 : Fin input.rows := ⟨0, by omega⟩
      let last : Fin input.rows := ⟨input.rows - 1, by omega⟩
      return intRowPairChecksum triple.1 f0 last
  | none => throw <| IO.userError "fplll-ffi certified candidate rejected by certCheck"

/-- Benchmark target: fpLLL candidate production via fplll-ffi plus Lean's
executable certificate checker. The same in-process payload that drives
`runFpLLLFirstShortVectorChecksum` feeds `LLLProvider.certifyFlat`, so the
certified curve and the raw fpLLL curve measure the identical C++ reducer. -/
def runCertifiedFirstShortVectorChecksum (input : FirstShortVectorInput) : IO Int := do
  certifyPayloadChecksum input (← requestFpLLLFlat input)

def runCertifiedCheckerChecksum
    (ref : IO.Ref (Option (FirstShortVectorInput × Array Int)))
    (mk : Unit → FirstShortVectorInput) : Unit → IO Int := fun _ => do
  let (input, payload) ←
    match (← ref.get) with
    | some cached => pure cached
    | none =>
        let input := mk ()
        let payload ← requestFpLLLFlat input
        ref.set (some (input, payload))
        pure (input, payload)
  certifyPayloadChecksum input payload

/-- Fixed benchmark target: BZ recombination hot path at `p = 5`, `k = 2`,
and three lifted local factors. -/
def runFirstShortVectorBZRecombinationChecksum : Unit → IO Int := fun _ => do
  return runFirstShortVectorChecksum (← bzRecombinationInputRef.get)

/-- Fixed benchmark target: random-bounded first-short-vector bottom rung. -/
def runFirstShortVectorRandomBounded30Checksum : Unit → IO Int := fun _ => do
  return runFirstShortVectorChecksum
    (← getCachedInput randomBoundedInput30Ref (fun _ => prepRandomBoundedInput 30))

/-- Fixed benchmark target: harsh-cubic first-short-vector bottom rung. -/
def runFirstShortVectorHarshCubic15Checksum : Unit → IO Int := fun _ => do
  return runFirstShortVectorChecksum
    (← getCachedInput harshCubicInput15Ref (fun _ => prepHarshCubicInput 15))

/-- fpLLL comparator (via fplll-ffi) for the fixed BZ recombination input. -/
def runFpLLLFirstShortVectorBZRecombinationChecksum : Unit → IO Int := fun _ => do
  runFpLLLFirstShortVectorChecksum (← bzRecombinationInputRef.get)

/-- fpLLL comparator (via fplll-ffi) for the random-bounded bottom rung (`n = 30`). -/
def runFpLLLFirstShortVectorRandomBounded30Checksum : Unit → IO Int := fun _ => do
  runFpLLLFirstShortVectorChecksum
    (← getCachedInput randomBoundedInput30Ref (fun _ => prepRandomBoundedInput 30))

/-- fpLLL comparator (via fplll-ffi) for the random-bounded rung `n = 45`. -/
def runFpLLLFirstShortVectorRandomBounded45Checksum : Unit → IO Int := fun _ => do
  runFpLLLFirstShortVectorChecksum
    (← getCachedInput randomBoundedInput45Ref (fun _ => prepRandomBoundedInput 45))

/-- fpLLL comparator (via fplll-ffi) for the random-bounded rung `n = 60`. -/
def runFpLLLFirstShortVectorRandomBounded60Checksum : Unit → IO Int := fun _ => do
  runFpLLLFirstShortVectorChecksum
    (← getCachedInput randomBoundedInput60Ref (fun _ => prepRandomBoundedInput 60))

/-- fpLLL comparator (via fplll-ffi) for the random-bounded rung `n = 75`. -/
def runFpLLLFirstShortVectorRandomBounded75Checksum : Unit → IO Int := fun _ => do
  runFpLLLFirstShortVectorChecksum
    (← getCachedInput randomBoundedInput75Ref (fun _ => prepRandomBoundedInput 75))

/-- fpLLL comparator (via fplll-ffi) for the random-bounded rung `n = 90`. -/
def runFpLLLFirstShortVectorRandomBounded90Checksum : Unit → IO Int := fun _ => do
  runFpLLLFirstShortVectorChecksum
    (← getCachedInput randomBoundedInput90Ref (fun _ => prepRandomBoundedInput 90))

/-- fpLLL comparator (via fplll-ffi) for the random-bounded rung `n = 120`. -/
def runFpLLLFirstShortVectorRandomBounded120Checksum : Unit → IO Int := fun _ => do
  runFpLLLFirstShortVectorChecksum
    (← getCachedInput randomBoundedInput120Ref (fun _ => prepRandomBoundedInput 120))

/-- fpLLL comparator (via fplll-ffi) for the random-bounded rung `n = 150`. -/
def runFpLLLFirstShortVectorRandomBounded150Checksum : Unit → IO Int := fun _ => do
  runFpLLLFirstShortVectorChecksum
    (← getCachedInput randomBoundedInput150Ref (fun _ => prepRandomBoundedInput 150))

/-- fpLLL comparator (via fplll-ffi) for the random-bounded rung `n = 180`. -/
def runFpLLLFirstShortVectorRandomBounded180Checksum : Unit → IO Int := fun _ => do
  runFpLLLFirstShortVectorChecksum
    (← getCachedInput randomBoundedInput180Ref (fun _ => prepRandomBoundedInput 180))

/-- fpLLL comparator (via fplll-ffi) for the harsh-cubic bottom rung (`n = 15`). -/
def runFpLLLFirstShortVectorHarshCubic15Checksum : Unit → IO Int := fun _ => do
  runFpLLLFirstShortVectorChecksum
    (← getCachedInput harshCubicInput15Ref (fun _ => prepHarshCubicInput 15))

/-- fpLLL comparator (via fplll-ffi) for the harsh-cubic rung `n = 20`. -/
def runFpLLLFirstShortVectorHarshCubic20Checksum : Unit → IO Int := fun _ => do
  runFpLLLFirstShortVectorChecksum
    (← getCachedInput harshCubicInput20Ref (fun _ => prepHarshCubicInput 20))

/-- fpLLL comparator (via fplll-ffi) for the harsh-cubic rung `n = 25`. -/
def runFpLLLFirstShortVectorHarshCubic25Checksum : Unit → IO Int := fun _ => do
  runFpLLLFirstShortVectorChecksum
    (← getCachedInput harshCubicInput25Ref (fun _ => prepHarshCubicInput 25))

/-- fpLLL comparator (via fplll-ffi) for the harsh-cubic rung `n = 30`. -/
def runFpLLLFirstShortVectorHarshCubic30Checksum : Unit → IO Int := fun _ => do
  runFpLLLFirstShortVectorChecksum
    (← getCachedInput harshCubicInput30Ref (fun _ => prepHarshCubicInput 30))

/-- fpLLL comparator (via fplll-ffi) for the harsh-cubic rung `n = 35`. -/
def runFpLLLFirstShortVectorHarshCubic35Checksum : Unit → IO Int := fun _ => do
  runFpLLLFirstShortVectorChecksum
    (← getCachedInput harshCubicInput35Ref (fun _ => prepHarshCubicInput 35))

/-- fpLLL comparator (via fplll-ffi) for the harsh-cubic rung `n = 40`. -/
def runFpLLLFirstShortVectorHarshCubic40Checksum : Unit → IO Int := fun _ => do
  runFpLLLFirstShortVectorChecksum
    (← getCachedInput harshCubicInput40Ref (fun _ => prepHarshCubicInput 40))

/-- fpLLL comparator (via fplll-ffi) for the harsh-cubic rung `n = 45`. -/
def runFpLLLFirstShortVectorHarshCubic45Checksum : Unit → IO Int := fun _ => do
  runFpLLLFirstShortVectorChecksum
    (← getCachedInput harshCubicInput45Ref (fun _ => prepHarshCubicInput 45))

/-- fpLLL comparator (via fplll-ffi) for the harsh-cubic rung `n = 50`. -/
def runFpLLLFirstShortVectorHarshCubic50Checksum : Unit → IO Int := fun _ => do
  runFpLLLFirstShortVectorChecksum
    (← getCachedInput harshCubicInput50Ref (fun _ => prepHarshCubicInput 50))

/-- fpLLL comparator (via fplll-ffi) for the harsh-cubic rung `n = 55`. -/
def runFpLLLFirstShortVectorHarshCubic55Checksum : Unit → IO Int := fun _ => do
  runFpLLLFirstShortVectorChecksum
    (← getCachedInput harshCubicInput55Ref (fun _ => prepHarshCubicInput 55))

/-- fpLLL comparator (via fplll-ffi) for the harsh-cubic rung `n = 60`. -/
def runFpLLLFirstShortVectorHarshCubic60Checksum : Unit → IO Int := fun _ => do
  runFpLLLFirstShortVectorChecksum
    (← getCachedInput harshCubicInput60Ref (fun _ => prepHarshCubicInput 60))

/-- fpLLL comparator (via fplll-ffi) for the harsh-cubic rung `n = 65`. -/
def runFpLLLFirstShortVectorHarshCubic65Checksum : Unit → IO Int := fun _ => do
  runFpLLLFirstShortVectorChecksum
    (← getCachedInput harshCubicInput65Ref (fun _ => prepHarshCubicInput 65))

-- Exact `lllNative` ladder targets for the comparator's exact-native curve
-- (the steered default lives on the `runFirstShortVector*NormSq` targets).
/-- Exact native `runNativeFirstShortVectorNormSq` on the `random-bounded`
fixture at the rung `n = 30`, returning the first short vector's squared norm
for the exact-native ladder curve. -/
def runNativeFirstShortVectorRandomBoundedNormSq30 : Unit → IO Int := fun _ => do
  return runNativeFirstShortVectorNormSq
    (← getCachedInput randomBoundedInput30Ref (fun _ => prepRandomBoundedInput 30))

/-- Exact native `runNativeFirstShortVectorNormSq` on the `random-bounded`
fixture at the rung `n = 45`, returning the first short vector's squared norm
for the exact-native ladder curve. -/
def runNativeFirstShortVectorRandomBoundedNormSq45 : Unit → IO Int := fun _ => do
  return runNativeFirstShortVectorNormSq
    (← getCachedInput randomBoundedInput45Ref (fun _ => prepRandomBoundedInput 45))

/-- Exact native `runNativeFirstShortVectorNormSq` on the `random-bounded`
fixture at the rung `n = 60`, returning the first short vector's squared norm
for the exact-native ladder curve. -/
def runNativeFirstShortVectorRandomBoundedNormSq60 : Unit → IO Int := fun _ => do
  return runNativeFirstShortVectorNormSq
    (← getCachedInput randomBoundedInput60Ref (fun _ => prepRandomBoundedInput 60))

/-- Exact native `runNativeFirstShortVectorNormSq` on the `random-bounded`
fixture at the rung `n = 75`, returning the first short vector's squared norm
for the exact-native ladder curve. -/
def runNativeFirstShortVectorRandomBoundedNormSq75 : Unit → IO Int := fun _ => do
  return runNativeFirstShortVectorNormSq
    (← getCachedInput randomBoundedInput75Ref (fun _ => prepRandomBoundedInput 75))

/-- Exact native `runNativeFirstShortVectorNormSq` on the `random-bounded`
fixture at the rung `n = 90`, returning the first short vector's squared norm
for the exact-native ladder curve. -/
def runNativeFirstShortVectorRandomBoundedNormSq90 : Unit → IO Int := fun _ => do
  return runNativeFirstShortVectorNormSq
    (← getCachedInput randomBoundedInput90Ref (fun _ => prepRandomBoundedInput 90))

/-- Exact native `runNativeFirstShortVectorNormSq` on the `random-bounded`
fixture at the rung `n = 120`, returning the first short vector's squared norm
for the exact-native ladder curve. -/
def runNativeFirstShortVectorRandomBoundedNormSq120 : Unit → IO Int := fun _ => do
  return runNativeFirstShortVectorNormSq
    (← getCachedInput randomBoundedInput120Ref (fun _ => prepRandomBoundedInput 120))

/-- Exact native `runNativeFirstShortVectorNormSq` on the `random-bounded`
fixture at the rung `n = 150`, returning the first short vector's squared norm
for the exact-native ladder curve. -/
def runNativeFirstShortVectorRandomBoundedNormSq150 : Unit → IO Int := fun _ => do
  return runNativeFirstShortVectorNormSq
    (← getCachedInput randomBoundedInput150Ref (fun _ => prepRandomBoundedInput 150))

/-- Exact native `runNativeFirstShortVectorNormSq` on the `random-bounded`
fixture at the rung `n = 180`, returning the first short vector's squared norm
for the exact-native ladder curve. -/
def runNativeFirstShortVectorRandomBoundedNormSq180 : Unit → IO Int := fun _ => do
  return runNativeFirstShortVectorNormSq
    (← getCachedInput randomBoundedInput180Ref (fun _ => prepRandomBoundedInput 180))

def runNativeFirstShortVectorHarshCubicNormSq15 : Unit → IO Int := fun _ => do
  return runNativeFirstShortVectorNormSq
    (← getCachedInput harshCubicInput15Ref (fun _ => prepHarshCubicInput 15))

def runNativeFirstShortVectorHarshCubicNormSq20 : Unit → IO Int := fun _ => do
  return runNativeFirstShortVectorNormSq
    (← getCachedInput harshCubicInput20Ref (fun _ => prepHarshCubicInput 20))

def runNativeFirstShortVectorHarshCubicNormSq25 : Unit → IO Int := fun _ => do
  return runNativeFirstShortVectorNormSq
    (← getCachedInput harshCubicInput25Ref (fun _ => prepHarshCubicInput 25))

def runNativeFirstShortVectorHarshCubicNormSq30 : Unit → IO Int := fun _ => do
  return runNativeFirstShortVectorNormSq
    (← getCachedInput harshCubicInput30Ref (fun _ => prepHarshCubicInput 30))

def runNativeFirstShortVectorHarshCubicNormSq35 : Unit → IO Int := fun _ => do
  return runNativeFirstShortVectorNormSq
    (← getCachedInput harshCubicInput35Ref (fun _ => prepHarshCubicInput 35))

def runNativeFirstShortVectorHarshCubicNormSq40 : Unit → IO Int := fun _ => do
  return runNativeFirstShortVectorNormSq
    (← getCachedInput harshCubicInput40Ref (fun _ => prepHarshCubicInput 40))

def runNativeFirstShortVectorHarshCubicNormSq45 : Unit → IO Int := fun _ => do
  return runNativeFirstShortVectorNormSq
    (← getCachedInput harshCubicInput45Ref (fun _ => prepHarshCubicInput 45))

def runNativeFirstShortVectorHarshCubicNormSq50 : Unit → IO Int := fun _ => do
  return runNativeFirstShortVectorNormSq
    (← getCachedInput harshCubicInput50Ref (fun _ => prepHarshCubicInput 50))

def runNativeFirstShortVectorHarshCubicNormSq55 : Unit → IO Int := fun _ => do
  return runNativeFirstShortVectorNormSq
    (← getCachedInput harshCubicInput55Ref (fun _ => prepHarshCubicInput 55))

def runNativeFirstShortVectorHarshCubicNormSq60 : Unit → IO Int := fun _ => do
  return runNativeFirstShortVectorNormSq
    (← getCachedInput harshCubicInput60Ref (fun _ => prepHarshCubicInput 60))

def runNativeFirstShortVectorHarshCubicNormSq65 : Unit → IO Int := fun _ => do
  return runNativeFirstShortVectorNormSq
    (← getCachedInput harshCubicInput65Ref (fun _ => prepHarshCubicInput 65))

def runDispatchedFirstShortVectorRandomBounded30Checksum : Unit → IO Int := fun _ => do
  runDispatchedFirstShortVectorChecksum
    (← getCachedInput randomBoundedInput30Ref (fun _ => prepRandomBoundedInput 30))

def runCertifiedFirstShortVectorRandomBounded30Checksum : Unit → IO Int := fun _ => do
  runCertifiedFirstShortVectorChecksum
    (← getCachedInput randomBoundedInput30Ref (fun _ => prepRandomBoundedInput 30))

def runCertifiedCheckerRandomBounded30Checksum : Unit → IO Int :=
  runCertifiedCheckerChecksum certifiedRandomBounded30Ref (fun _ => prepRandomBoundedInput 30)

def runCertifiedFirstShortVectorRandomBounded45Checksum : Unit → IO Int := fun _ => do
  runCertifiedFirstShortVectorChecksum
    (← getCachedInput randomBoundedInput45Ref (fun _ => prepRandomBoundedInput 45))

def runCertifiedCheckerRandomBounded45Checksum : Unit → IO Int :=
  runCertifiedCheckerChecksum certifiedRandomBounded45Ref (fun _ => prepRandomBoundedInput 45)

def runCertifiedFirstShortVectorRandomBounded60Checksum : Unit → IO Int := fun _ => do
  runCertifiedFirstShortVectorChecksum
    (← getCachedInput randomBoundedInput60Ref (fun _ => prepRandomBoundedInput 60))

def runCertifiedCheckerRandomBounded60Checksum : Unit → IO Int :=
  runCertifiedCheckerChecksum certifiedRandomBounded60Ref (fun _ => prepRandomBoundedInput 60)

def runCertifiedFirstShortVectorRandomBounded75Checksum : Unit → IO Int := fun _ => do
  runCertifiedFirstShortVectorChecksum
    (← getCachedInput randomBoundedInput75Ref (fun _ => prepRandomBoundedInput 75))

def runCertifiedCheckerRandomBounded75Checksum : Unit → IO Int :=
  runCertifiedCheckerChecksum certifiedRandomBounded75Ref (fun _ => prepRandomBoundedInput 75)

def runCertifiedFirstShortVectorRandomBounded90Checksum : Unit → IO Int := fun _ => do
  runCertifiedFirstShortVectorChecksum
    (← getCachedInput randomBoundedInput90Ref (fun _ => prepRandomBoundedInput 90))

def runCertifiedCheckerRandomBounded90Checksum : Unit → IO Int :=
  runCertifiedCheckerChecksum certifiedRandomBounded90Ref (fun _ => prepRandomBoundedInput 90)

def runCertifiedFirstShortVectorRandomBounded120Checksum : Unit → IO Int := fun _ => do
  runCertifiedFirstShortVectorChecksum
    (← getCachedInput randomBoundedInput120Ref (fun _ => prepRandomBoundedInput 120))

def runCertifiedCheckerRandomBounded120Checksum : Unit → IO Int :=
  runCertifiedCheckerChecksum certifiedRandomBounded120Ref (fun _ => prepRandomBoundedInput 120)

def runCertifiedFirstShortVectorRandomBounded150Checksum : Unit → IO Int := fun _ => do
  runCertifiedFirstShortVectorChecksum
    (← getCachedInput randomBoundedInput150Ref (fun _ => prepRandomBoundedInput 150))

def runCertifiedCheckerRandomBounded150Checksum : Unit → IO Int :=
  runCertifiedCheckerChecksum certifiedRandomBounded150Ref (fun _ => prepRandomBoundedInput 150)

def runCertifiedFirstShortVectorRandomBounded180Checksum : Unit → IO Int := fun _ => do
  runCertifiedFirstShortVectorChecksum
    (← getCachedInput randomBoundedInput180Ref (fun _ => prepRandomBoundedInput 180))

def runCertifiedCheckerRandomBounded180Checksum : Unit → IO Int :=
  runCertifiedCheckerChecksum certifiedRandomBounded180Ref (fun _ => prepRandomBoundedInput 180)

def runDispatchedFirstShortVectorHarshCubic15Checksum : Unit → IO Int := fun _ => do
  runDispatchedFirstShortVectorChecksum
    (← getCachedInput harshCubicInput15Ref (fun _ => prepHarshCubicInput 15))

def runCertifiedFirstShortVectorHarshCubic15Checksum : Unit → IO Int := fun _ => do
  runCertifiedFirstShortVectorChecksum
    (← getCachedInput harshCubicInput15Ref (fun _ => prepHarshCubicInput 15))

def runCertifiedCheckerHarshCubic15Checksum : Unit → IO Int :=
  runCertifiedCheckerChecksum certifiedHarshCubic15Ref (fun _ => prepHarshCubicInput 15)

def runCertifiedFirstShortVectorHarshCubic20Checksum : Unit → IO Int := fun _ => do
  runCertifiedFirstShortVectorChecksum
    (← getCachedInput harshCubicInput20Ref (fun _ => prepHarshCubicInput 20))

def runCertifiedCheckerHarshCubic20Checksum : Unit → IO Int :=
  runCertifiedCheckerChecksum certifiedHarshCubic20Ref (fun _ => prepHarshCubicInput 20)

def runCertifiedFirstShortVectorHarshCubic25Checksum : Unit → IO Int := fun _ => do
  runCertifiedFirstShortVectorChecksum
    (← getCachedInput harshCubicInput25Ref (fun _ => prepHarshCubicInput 25))

def runCertifiedCheckerHarshCubic25Checksum : Unit → IO Int :=
  runCertifiedCheckerChecksum certifiedHarshCubic25Ref (fun _ => prepHarshCubicInput 25)

def runCertifiedFirstShortVectorHarshCubic30Checksum : Unit → IO Int := fun _ => do
  runCertifiedFirstShortVectorChecksum
    (← getCachedInput harshCubicInput30Ref (fun _ => prepHarshCubicInput 30))

def runCertifiedCheckerHarshCubic30Checksum : Unit → IO Int :=
  runCertifiedCheckerChecksum certifiedHarshCubic30Ref (fun _ => prepHarshCubicInput 30)

def runCertifiedFirstShortVectorHarshCubic35Checksum : Unit → IO Int := fun _ => do
  runCertifiedFirstShortVectorChecksum
    (← getCachedInput harshCubicInput35Ref (fun _ => prepHarshCubicInput 35))

def runCertifiedCheckerHarshCubic35Checksum : Unit → IO Int :=
  runCertifiedCheckerChecksum certifiedHarshCubic35Ref (fun _ => prepHarshCubicInput 35)

def runCertifiedFirstShortVectorHarshCubic40Checksum : Unit → IO Int := fun _ => do
  runCertifiedFirstShortVectorChecksum
    (← getCachedInput harshCubicInput40Ref (fun _ => prepHarshCubicInput 40))

def runCertifiedCheckerHarshCubic40Checksum : Unit → IO Int :=
  runCertifiedCheckerChecksum certifiedHarshCubic40Ref (fun _ => prepHarshCubicInput 40)

def runCertifiedFirstShortVectorHarshCubic45Checksum : Unit → IO Int := fun _ => do
  runCertifiedFirstShortVectorChecksum
    (← getCachedInput harshCubicInput45Ref (fun _ => prepHarshCubicInput 45))

def runCertifiedCheckerHarshCubic45Checksum : Unit → IO Int :=
  runCertifiedCheckerChecksum certifiedHarshCubic45Ref (fun _ => prepHarshCubicInput 45)

def runCertifiedFirstShortVectorHarshCubic50Checksum : Unit → IO Int := fun _ => do
  runCertifiedFirstShortVectorChecksum
    (← getCachedInput harshCubicInput50Ref (fun _ => prepHarshCubicInput 50))

def runCertifiedCheckerHarshCubic50Checksum : Unit → IO Int :=
  runCertifiedCheckerChecksum certifiedHarshCubic50Ref (fun _ => prepHarshCubicInput 50)

def runCertifiedFirstShortVectorHarshCubic55Checksum : Unit → IO Int := fun _ => do
  runCertifiedFirstShortVectorChecksum
    (← getCachedInput harshCubicInput55Ref (fun _ => prepHarshCubicInput 55))

def runCertifiedCheckerHarshCubic55Checksum : Unit → IO Int :=
  runCertifiedCheckerChecksum certifiedHarshCubic55Ref (fun _ => prepHarshCubicInput 55)

def runCertifiedFirstShortVectorHarshCubic60Checksum : Unit → IO Int := fun _ => do
  runCertifiedFirstShortVectorChecksum
    (← getCachedInput harshCubicInput60Ref (fun _ => prepHarshCubicInput 60))

def runCertifiedCheckerHarshCubic60Checksum : Unit → IO Int :=
  runCertifiedCheckerChecksum certifiedHarshCubic60Ref (fun _ => prepHarshCubicInput 60)

def runCertifiedFirstShortVectorHarshCubic65Checksum : Unit → IO Int := fun _ => do
  runCertifiedFirstShortVectorChecksum
    (← getCachedInput harshCubicInput65Ref (fun _ => prepHarshCubicInput 65))

def runCertifiedCheckerHarshCubic65Checksum : Unit → IO Int :=
  runCertifiedCheckerChecksum certifiedHarshCubic65Ref (fun _ => prepHarshCubicInput 65)

/-- Observable for the reducedness-decision tally: run the certified checker
once on every rung of both ladders, then read `Hex.checkerTally`. Fails if
any interval pass reached indecision (`exactFallback ≠ 0`); the
size-predictor split between interval-accepted and exact-primary is pinned
by the expected hash. The returned value encodes the tally as
`(interval · 65537 + exactPrimary) · 65537 + exactFallback`. -/
def runCertifiedCheckerIntervalTally : Unit → IO Int := fun _ => do
  Hex.resetCheckerTally
  let targets : List (Unit → IO Int) :=
    [runCertifiedCheckerRandomBounded30Checksum,
     runCertifiedCheckerRandomBounded45Checksum,
     runCertifiedCheckerRandomBounded60Checksum,
     runCertifiedCheckerRandomBounded75Checksum,
     runCertifiedCheckerRandomBounded90Checksum,
     runCertifiedCheckerRandomBounded120Checksum,
     runCertifiedCheckerRandomBounded150Checksum,
     runCertifiedCheckerRandomBounded180Checksum,
     runCertifiedCheckerHarshCubic15Checksum,
     runCertifiedCheckerHarshCubic20Checksum,
     runCertifiedCheckerHarshCubic25Checksum,
     runCertifiedCheckerHarshCubic30Checksum,
     runCertifiedCheckerHarshCubic35Checksum,
     runCertifiedCheckerHarshCubic40Checksum,
     runCertifiedCheckerHarshCubic45Checksum,
     runCertifiedCheckerHarshCubic50Checksum,
     runCertifiedCheckerHarshCubic55Checksum,
     runCertifiedCheckerHarshCubic60Checksum,
     runCertifiedCheckerHarshCubic65Checksum]
  for t in targets do
    discard <| t ()
  let tally ← Hex.checkerTally
  if tally.exactFallback != 0 then
    throw <| IO.userError
      s!"interval reducedness checker reached indecision: {repr tally}"
  return (Int.ofNat tally.interval * 65537 + Int.ofNat tally.exactPrimary) * 65537 +
    Int.ofNat tally.exactFallback


def runFirstShortVectorBZRecombinationNormSq : Unit → IO Int := fun _ => do
  return runFirstShortVectorNormSq (← bzRecombinationInputRef.get)

def runIsabelleBZRecombinationNormSq : Unit → IO Int := fun _ => do
  runIsabelleShortVectorNormSq "bz-recombination" (← bzRecombinationInputRef.get)

def runFirstShortVectorRandomBoundedNormSq30 : Unit → IO Int := fun _ => do
  return runFirstShortVectorNormSq
    (← getCachedInput randomBoundedInput30Ref (fun _ => prepRandomBoundedInput 30))

def runIsabelleRandomBoundedNormSq30 : Unit → IO Int := fun _ => do
  runIsabelleShortVectorNormSq "random-bounded-30"
    (← getCachedInput randomBoundedInput30Ref (fun _ => prepRandomBoundedInput 30))

def runFirstShortVectorRandomBoundedNormSq45 : Unit → IO Int := fun _ => do
  return runFirstShortVectorNormSq
    (← getCachedInput randomBoundedInput45Ref (fun _ => prepRandomBoundedInput 45))

def runIsabelleRandomBoundedNormSq45 : Unit → IO Int := fun _ => do
  runIsabelleShortVectorNormSq "random-bounded-45"
    (← getCachedInput randomBoundedInput45Ref (fun _ => prepRandomBoundedInput 45))

def runFirstShortVectorRandomBoundedNormSq60 : Unit → IO Int := fun _ => do
  return runFirstShortVectorNormSq
    (← getCachedInput randomBoundedInput60Ref (fun _ => prepRandomBoundedInput 60))

def runIsabelleRandomBoundedNormSq60 : Unit → IO Int := fun _ => do
  runIsabelleShortVectorNormSq "random-bounded-60"
    (← getCachedInput randomBoundedInput60Ref (fun _ => prepRandomBoundedInput 60))

def runFirstShortVectorRandomBoundedNormSq75 : Unit → IO Int := fun _ => do
  return runFirstShortVectorNormSq
    (← getCachedInput randomBoundedInput75Ref (fun _ => prepRandomBoundedInput 75))

def runIsabelleRandomBoundedNormSq75 : Unit → IO Int := fun _ => do
  runIsabelleShortVectorNormSq "random-bounded-75"
    (← getCachedInput randomBoundedInput75Ref (fun _ => prepRandomBoundedInput 75))

def runFirstShortVectorRandomBoundedNormSq90 : Unit → IO Int := fun _ => do
  return runFirstShortVectorNormSq
    (← getCachedInput randomBoundedInput90Ref (fun _ => prepRandomBoundedInput 90))

def runIsabelleRandomBoundedNormSq90 : Unit → IO Int := fun _ => do
  runIsabelleShortVectorNormSq "random-bounded-90"
    (← getCachedInput randomBoundedInput90Ref (fun _ => prepRandomBoundedInput 90))

def runFirstShortVectorRandomBoundedNormSq120 : Unit → IO Int := fun _ => do
  return runFirstShortVectorNormSq
    (← getCachedInput randomBoundedInput120Ref (fun _ => prepRandomBoundedInput 120))

def runIsabelleRandomBoundedNormSq120 : Unit → IO Int := fun _ => do
  runIsabelleShortVectorNormSq "random-bounded-120"
    (← getCachedInput randomBoundedInput120Ref (fun _ => prepRandomBoundedInput 120))

def runFirstShortVectorRandomBoundedNormSq150 : Unit → IO Int := fun _ => do
  return runFirstShortVectorNormSq
    (← getCachedInput randomBoundedInput150Ref (fun _ => prepRandomBoundedInput 150))

def runIsabelleRandomBoundedNormSq150 : Unit → IO Int := fun _ => do
  runIsabelleShortVectorNormSq "random-bounded-150"
    (← getCachedInput randomBoundedInput150Ref (fun _ => prepRandomBoundedInput 150))

def runFirstShortVectorRandomBoundedNormSq180 : Unit → IO Int := fun _ => do
  return runFirstShortVectorNormSq
    (← getCachedInput randomBoundedInput180Ref (fun _ => prepRandomBoundedInput 180))

def runIsabelleRandomBoundedNormSq180 : Unit → IO Int := fun _ => do
  runIsabelleShortVectorNormSq "random-bounded-180"
    (← getCachedInput randomBoundedInput180Ref (fun _ => prepRandomBoundedInput 180))

def runFirstShortVectorHarshCubicNormSq15 : Unit → IO Int := fun _ => do
  return runFirstShortVectorNormSq
    (← getCachedInput harshCubicInput15Ref (fun _ => prepHarshCubicInput 15))

def runIsabelleHarshCubicNormSq15 : Unit → IO Int := fun _ => do
  runIsabelleShortVectorNormSq "harsh-cubic-15"
    (← getCachedInput harshCubicInput15Ref (fun _ => prepHarshCubicInput 15))

def runFirstShortVectorHarshCubicNormSq20 : Unit → IO Int := fun _ => do
  return runFirstShortVectorNormSq
    (← getCachedInput harshCubicInput20Ref (fun _ => prepHarshCubicInput 20))

def runIsabelleHarshCubicNormSq20 : Unit → IO Int := fun _ => do
  runIsabelleShortVectorNormSq "harsh-cubic-20"
    (← getCachedInput harshCubicInput20Ref (fun _ => prepHarshCubicInput 20))

def runFirstShortVectorHarshCubicNormSq25 : Unit → IO Int := fun _ => do
  return runFirstShortVectorNormSq
    (← getCachedInput harshCubicInput25Ref (fun _ => prepHarshCubicInput 25))

def runIsabelleHarshCubicNormSq25 : Unit → IO Int := fun _ => do
  runIsabelleShortVectorNormSq "harsh-cubic-25"
    (← getCachedInput harshCubicInput25Ref (fun _ => prepHarshCubicInput 25))

def runFirstShortVectorHarshCubicNormSq30 : Unit → IO Int := fun _ => do
  return runFirstShortVectorNormSq
    (← getCachedInput harshCubicInput30Ref (fun _ => prepHarshCubicInput 30))

def runIsabelleHarshCubicNormSq30 : Unit → IO Int := fun _ => do
  runIsabelleShortVectorNormSq "harsh-cubic-30"
    (← getCachedInput harshCubicInput30Ref (fun _ => prepHarshCubicInput 30))

def runFirstShortVectorHarshCubicNormSq35 : Unit → IO Int := fun _ => do
  return runFirstShortVectorNormSq
    (← getCachedInput harshCubicInput35Ref (fun _ => prepHarshCubicInput 35))

def runIsabelleHarshCubicNormSq35 : Unit → IO Int := fun _ => do
  runIsabelleShortVectorNormSq "harsh-cubic-35"
    (← getCachedInput harshCubicInput35Ref (fun _ => prepHarshCubicInput 35))

def runFirstShortVectorHarshCubicNormSq40 : Unit → IO Int := fun _ => do
  return runFirstShortVectorNormSq
    (← getCachedInput harshCubicInput40Ref (fun _ => prepHarshCubicInput 40))

def runIsabelleHarshCubicNormSq40 : Unit → IO Int := fun _ => do
  runIsabelleShortVectorNormSq "harsh-cubic-40"
    (← getCachedInput harshCubicInput40Ref (fun _ => prepHarshCubicInput 40))

def runFirstShortVectorHarshCubicNormSq45 : Unit → IO Int := fun _ => do
  return runFirstShortVectorNormSq
    (← getCachedInput harshCubicInput45Ref (fun _ => prepHarshCubicInput 45))

def runIsabelleHarshCubicNormSq45 : Unit → IO Int := fun _ => do
  runIsabelleShortVectorNormSq "harsh-cubic-45"
    (← getCachedInput harshCubicInput45Ref (fun _ => prepHarshCubicInput 45))

def runFirstShortVectorHarshCubicNormSq50 : Unit → IO Int := fun _ => do
  return runFirstShortVectorNormSq
    (← getCachedInput harshCubicInput50Ref (fun _ => prepHarshCubicInput 50))

def runIsabelleHarshCubicNormSq50 : Unit → IO Int := fun _ => do
  runIsabelleShortVectorNormSq "harsh-cubic-50"
    (← getCachedInput harshCubicInput50Ref (fun _ => prepHarshCubicInput 50))

def runFirstShortVectorHarshCubicNormSq55 : Unit → IO Int := fun _ => do
  return runFirstShortVectorNormSq
    (← getCachedInput harshCubicInput55Ref (fun _ => prepHarshCubicInput 55))

def runIsabelleHarshCubicNormSq55 : Unit → IO Int := fun _ => do
  runIsabelleShortVectorNormSq "harsh-cubic-55"
    (← getCachedInput harshCubicInput55Ref (fun _ => prepHarshCubicInput 55))

def runFirstShortVectorHarshCubicNormSq60 : Unit → IO Int := fun _ => do
  return runFirstShortVectorNormSq
    (← getCachedInput harshCubicInput60Ref (fun _ => prepHarshCubicInput 60))

def runIsabelleHarshCubicNormSq60 : Unit → IO Int := fun _ => do
  runIsabelleShortVectorNormSq "harsh-cubic-60"
    (← getCachedInput harshCubicInput60Ref (fun _ => prepHarshCubicInput 60))

def runFirstShortVectorHarshCubicNormSq65 : Unit → IO Int := fun _ => do
  return runFirstShortVectorNormSq
    (← getCachedInput harshCubicInput65Ref (fun _ => prepHarshCubicInput 65))

def runIsabelleHarshCubicNormSq65 : Unit → IO Int := fun _ => do
  runIsabelleShortVectorNormSq "harsh-cubic-65"
    (← getCachedInput harshCubicInput65Ref (fun _ => prepHarshCubicInput 65))

/-- Fallback-rate diagnostic for the steered native reducer: run
`firstShortVectorUnchecked` (i.e. `lllSteered`) once on every rung of both
ladders, then read `Hex.steeredTally`. Fails if any steered candidate failed
certification and fell back to the exact reducer (`fellBack ≠ 0`) — a fallback
inside the ladder would make the steered medians dishonest. Only rungs the
`Hex.steerWins` predictor routes to steering (n ≥ 30) bump the tally; the
smaller rungs run `lllNative` directly. The returned value encodes the tally
as `certified · 65537 + fellBack`. -/
def runSteeredFallbackTally : Unit → IO Int := fun _ => do
  Hex.resetSteeredTally
  let targets : List (Unit → IO Int) :=
    [runFirstShortVectorRandomBoundedNormSq30,
     runFirstShortVectorRandomBoundedNormSq45,
     runFirstShortVectorRandomBoundedNormSq60,
     runFirstShortVectorRandomBoundedNormSq75,
     runFirstShortVectorRandomBoundedNormSq90,
     runFirstShortVectorRandomBoundedNormSq120,
     runFirstShortVectorRandomBoundedNormSq150,
     runFirstShortVectorRandomBoundedNormSq180,
     runFirstShortVectorHarshCubicNormSq15,
     runFirstShortVectorHarshCubicNormSq20,
     runFirstShortVectorHarshCubicNormSq25,
     runFirstShortVectorHarshCubicNormSq30,
     runFirstShortVectorHarshCubicNormSq35,
     runFirstShortVectorHarshCubicNormSq40,
     runFirstShortVectorHarshCubicNormSq45,
     runFirstShortVectorHarshCubicNormSq50,
     runFirstShortVectorHarshCubicNormSq55,
     runFirstShortVectorHarshCubicNormSq60,
     runFirstShortVectorHarshCubicNormSq65]
  for t in targets do
    discard <| t ()
  let tally ← Hex.steeredTally
  if tally.fellBack != 0 then
    throw <| IO.userError
      s!"steered reducer fell back to the exact reducer on a bench rung: {repr tally}"
  return Int.ofNat tally.certified * 65537 + Int.ofNat tally.fellBack

/-- Isabelle-certified per-request process floor: time a trivial 2×2 request
through `svp_certified`. The median is the fixed fork+startup overhead the
comparator plot subtracts from the Isabelle-certified curve, so the
adjustment uses a committed measurement rather than a hardcoded constant. -/
def runIsabelleCertifiedProcessFloorNormSq : Unit → IO Int := fun _ => do
  runIsabelleCertifiedShortVectorNormSq "process-floor" processFloorInput

def runIsabelleCertifiedRandomBoundedNormSq30 : Unit → IO Int := fun _ => do
  runIsabelleCertifiedShortVectorNormSq "random-bounded-30"
    (← getCachedInput randomBoundedInput30Ref (fun _ => prepRandomBoundedInput 30))

def runIsabelleCertifiedRandomBoundedNormSq45 : Unit → IO Int := fun _ => do
  runIsabelleCertifiedShortVectorNormSq "random-bounded-45"
    (← getCachedInput randomBoundedInput45Ref (fun _ => prepRandomBoundedInput 45))

def runIsabelleCertifiedRandomBoundedNormSq60 : Unit → IO Int := fun _ => do
  runIsabelleCertifiedShortVectorNormSq "random-bounded-60"
    (← getCachedInput randomBoundedInput60Ref (fun _ => prepRandomBoundedInput 60))

def runIsabelleCertifiedRandomBoundedNormSq75 : Unit → IO Int := fun _ => do
  runIsabelleCertifiedShortVectorNormSq "random-bounded-75"
    (← getCachedInput randomBoundedInput75Ref (fun _ => prepRandomBoundedInput 75))

def runIsabelleCertifiedRandomBoundedNormSq90 : Unit → IO Int := fun _ => do
  runIsabelleCertifiedShortVectorNormSq "random-bounded-90"
    (← getCachedInput randomBoundedInput90Ref (fun _ => prepRandomBoundedInput 90))

def runIsabelleCertifiedRandomBoundedNormSq120 : Unit → IO Int := fun _ => do
  runIsabelleCertifiedShortVectorNormSq "random-bounded-120"
    (← getCachedInput randomBoundedInput120Ref (fun _ => prepRandomBoundedInput 120))

def runIsabelleCertifiedRandomBoundedNormSq150 : Unit → IO Int := fun _ => do
  runIsabelleCertifiedShortVectorNormSq "random-bounded-150"
    (← getCachedInput randomBoundedInput150Ref (fun _ => prepRandomBoundedInput 150))

def runIsabelleCertifiedRandomBoundedNormSq180 : Unit → IO Int := fun _ => do
  runIsabelleCertifiedShortVectorNormSq "random-bounded-180"
    (← getCachedInput randomBoundedInput180Ref (fun _ => prepRandomBoundedInput 180))

def runIsabelleCertifiedHarshCubicNormSq15 : Unit → IO Int := fun _ => do
  runIsabelleCertifiedShortVectorNormSq "harsh-cubic-15"
    (← getCachedInput harshCubicInput15Ref (fun _ => prepHarshCubicInput 15))

def runIsabelleCertifiedHarshCubicNormSq20 : Unit → IO Int := fun _ => do
  runIsabelleCertifiedShortVectorNormSq "harsh-cubic-20"
    (← getCachedInput harshCubicInput20Ref (fun _ => prepHarshCubicInput 20))

def runIsabelleCertifiedHarshCubicNormSq25 : Unit → IO Int := fun _ => do
  runIsabelleCertifiedShortVectorNormSq "harsh-cubic-25"
    (← getCachedInput harshCubicInput25Ref (fun _ => prepHarshCubicInput 25))

def runIsabelleCertifiedHarshCubicNormSq30 : Unit → IO Int := fun _ => do
  runIsabelleCertifiedShortVectorNormSq "harsh-cubic-30"
    (← getCachedInput harshCubicInput30Ref (fun _ => prepHarshCubicInput 30))

def runIsabelleCertifiedHarshCubicNormSq35 : Unit → IO Int := fun _ => do
  runIsabelleCertifiedShortVectorNormSq "harsh-cubic-35"
    (← getCachedInput harshCubicInput35Ref (fun _ => prepHarshCubicInput 35))

def runIsabelleCertifiedHarshCubicNormSq40 : Unit → IO Int := fun _ => do
  runIsabelleCertifiedShortVectorNormSq "harsh-cubic-40"
    (← getCachedInput harshCubicInput40Ref (fun _ => prepHarshCubicInput 40))

def runIsabelleCertifiedHarshCubicNormSq45 : Unit → IO Int := fun _ => do
  runIsabelleCertifiedShortVectorNormSq "harsh-cubic-45"
    (← getCachedInput harshCubicInput45Ref (fun _ => prepHarshCubicInput 45))

def runIsabelleCertifiedHarshCubicNormSq50 : Unit → IO Int := fun _ => do
  runIsabelleCertifiedShortVectorNormSq "harsh-cubic-50"
    (← getCachedInput harshCubicInput50Ref (fun _ => prepHarshCubicInput 50))

def runIsabelleCertifiedHarshCubicNormSq55 : Unit → IO Int := fun _ => do
  runIsabelleCertifiedShortVectorNormSq "harsh-cubic-55"
    (← getCachedInput harshCubicInput55Ref (fun _ => prepHarshCubicInput 55))

def runIsabelleCertifiedHarshCubicNormSq60 : Unit → IO Int := fun _ => do
  runIsabelleCertifiedShortVectorNormSq "harsh-cubic-60"
    (← getCachedInput harshCubicInput60Ref (fun _ => prepHarshCubicInput 60))

def runIsabelleCertifiedHarshCubicNormSq65 : Unit → IO Int := fun _ => do
  runIsabelleCertifiedShortVectorNormSq "harsh-cubic-65"
    (← getCachedInput harshCubicInput65Ref (fun _ => prepHarshCubicInput 65))

/-- Parametric benchmark target: LCG random-bounded bases. -/
def runFirstShortVectorRandomBoundedChecksum (input : FirstShortVectorInput) : Int :=
  runFirstShortVectorChecksum input

/-- Parametric benchmark target: harsh-cubic bases. -/
def runFirstShortVectorHarshCubicChecksum (input : FirstShortVectorInput) : Int :=
  runFirstShortVectorChecksum input

def firstShortVectorRandomBoundedNormSqHash (n : Nat) : UInt64 :=
  Hashable.hash (runFirstShortVectorNormSq (prepRandomBoundedInput n))

def firstShortVectorHarshCubicNormSqHash (n : Nat) : UInt64 :=
  Hashable.hash (runFirstShortVectorNormSq (prepHarshCubicInput n))

/- Complexity derivation: `LLLState.ofBasis` builds the Gram matrix for a
square BZ recombination-style basis with `rows = cols = n + 3`, then runs the
shared fraction-free Bareiss-shaped pass used by `GramSchmidt.Int.data`.
The dominant work is `rows^2 * cols`
integer multiply-adds for Gram construction plus one cubic elimination over
the `rows x rows` Gram matrix. Hadamard bounds each leading Gram determinant's
bit-width by `O(k * (log rows + log cols + 2 log B))`; this bounded-coefficient
fixture keeps the bit-width factor uniform in the declared operation count. -/
setup_benchmark runOfBasisBzRecombinationChecksum n =>
    ofBasisBzRecombinationComplexity n
  with prep := prepOfBasisBzRecombinationInput
  where {
    paramFloor := 24
    paramCeiling := 72
    paramSchedule := .custom #[24, 36, 48, 60, 72]
    maxSecondsPerCall := 8.0
    signalFloorMultiplier := 1.0
  }

/- Complexity derivation: the random-bounded family uses a square
`rows = cols = n + 3` basis with entries in `[-30, 30]`. `ofBasis` first forms
all `rows^2` dot products of length `rows`, then computes `d` and `ν` in one
Bareiss-style pass over that Gram matrix. Hadamard
gives `O(k * (log rows + log 30))` pivot bit-width, so the registration
declares the cubic algebraic surface rather than the host-specific bigint
constant. -/
setup_benchmark runOfBasisRandomBoundedChecksum n =>
    ofBasisRandomBoundedComplexity n
  with prep := prepOfBasisRandomBoundedInput
  where {
    paramFloor := 48
    paramCeiling := 144
    paramSchedule := .custom #[48, 72, 96, 120, 144]
    maxSecondsPerCall := 12.0
    signalFloorMultiplier := 1.0
  }

/- Complexity derivation: the harsh-cubic family uses the same square
`rows = cols = n + 3` constructor path as random-bounded, but fixture entries
have bit-length `3 * rows + O(1)`. The same Hadamard bound makes Bareiss pivot
bit-width grow linearly with `rows` on top of the Gram construction and the two
cubic elimination passes, so the declared model multiplies the algebraic
`ofBasisComplexity rows rows` surface by `rows`. -/
setup_benchmark runOfBasisHarshCubicChecksum n =>
    ofBasisHarshCubicComplexity n
  with prep := prepOfBasisHarshCubicInput
  where {
    paramFloor := 12
    paramCeiling := 36
    paramSchedule := .custom #[12, 18, 24, 30, 36]
    maxSecondsPerCall := 30.0
    targetInnerNanos := 1_000_000_000
    signalFloorMultiplier := 1.0
  }

/- Complexity derivation: `prepStateInput n` gives `rows = n + 3` and
`cols = 2 * (n + 3) + 1`. A single targeted reduction updates one basis row
over `cols` entries and one coefficient prefix bounded by `rows`. -/
setup_benchmark runSizeReduceColumnChecksum n => sizeReduceColumnComplexity n
  with prep := prepStateInput
  where {
    paramFloor := 96
    paramCeiling := 160
    paramSchedule := .custom #[96, 128, 160]
    maxSecondsPerCall := 3.0
    signalFloorMultiplier := 1.0
  }

/- Complexity derivation: full size reduction of the final prepared row
performs one targeted row update for each earlier row, so the model is
`rows * cols` for basis entries plus the triangular coefficient-prefix surface,
bounded here by `rows^2`. -/
setup_benchmark runSizeReduceChecksum n => sizeReduceComplexity n
  with prep := prepStateInput
  where {
    paramFloor := 128
    paramCeiling := 160
    paramSchedule := .custom #[128, 144, 160]
    maxSecondsPerCall := 30.0
    signalFloorMultiplier := 1.0
  }

/- Complexity derivation: an adjacent swap exchanges two basis rows over
`cols` entries, rewrites one determinant, swaps the lower coefficient prefix,
and updates the two affected coefficient columns for rows above the pivot; all
terms are linear in rows. -/
setup_benchmark runSwapStepChecksum n => swapStepComplexity n
  with prep := prepStateInput
  where {
    paramFloor := 96
    paramCeiling := 160
    paramSchedule := .custom #[96, 128, 160]
    maxSecondsPerCall := 3.0
    signalFloorMultiplier := 1.0
  }

/- Complexity derivation: `gramSchmidtCoeff` reads one stored `ν[k][j]` entry
and one stored `d[j+1]` denominator, then performs a single rational division
whose denominator bit-width grows linearly with the prepared row parameter.
The elevated cap covers state preparation at the smallest scientific rung on
high-spawn-floor hosts; it is not part of the measured body. -/
setup_benchmark runGramSchmidtCoeffChecksum n => gramSchmidtCoeffComplexity n
  with prep := prepStateInput
  where {
    paramFloor := 32
    paramCeiling := 128
    paramSchedule := .custom #[32, 64, 96, 128]
    maxSecondsPerCall := 30.0
    targetInnerNanos := 2_000_000_000
    signalFloorMultiplier := 1.0
  }

/- Complexity derivation: `potential` folds once over the prepared state's
determinant prefix. The fixture has `rows = n + 3`, so the prefix length is
`n + 2`; each stored Gram determinant has row-dependent bit width, and the
running product's bit width grows across the prefix. The resulting executable
integer-arithmetic surface is cubic in `rows`. -/
setup_benchmark runPotential n => potentialComplexity n
  with prep := prepStateInput
  where {
    paramFloor := 192
    paramCeiling := 216
    paramSchedule := .custom #[192, 208, 216]
    maxSecondsPerCall := 8.0
    targetInnerNanos := 1_000_000_000
    signalFloorMultiplier := 1.0
  }

/- Fixed Phase-4 family: BZ-shaped triangular basis with three lifted local
factors, matching the conformance fixture in `HexLLL/EmitFixtures.lean`. This
fixed target records the downstream hot path inherited from
Berlekamp-Zassenhaus recombination. -/
setup_fixed_benchmark runFirstShortVectorBZRecombinationChecksum where {
    repeats := 5
    maxSecondsPerCall := 6.0
    expectedHash := some (Hashable.hash (runFirstShortVectorChecksum bzRecombinationInput))
  }

/- Fixed bottom-rung Lean/fpLLL comparison for the BZ recombination family.
The fpLLL target is informational and FFI-call based via fplll-ffi; scheduled
and release bench runs use
`compare runFirstShortVectorBZRecombinationChecksum runFpLLLFirstShortVectorBZRecombinationChecksum`
to record its ratio. -/
setup_fixed_benchmark runFpLLLFirstShortVectorBZRecombinationChecksum where {
    repeats := 5
    minTotalSeconds := 1.0
    maxSecondsPerCall := 20.0
    expectedHash := some 0x20001
    warmupFirstIter := true
  }

/- Fixed Lean/fpLLL comparison for the random-bounded family across the
post-HO-18 densified ladder. -/
setup_fixed_benchmark runFirstShortVectorRandomBounded30Checksum where {
    repeats := 5
    maxSecondsPerCall := 20.0
    expectedHash := some (Hashable.hash (runFirstShortVectorChecksum (prepRandomBoundedInput 30)))
  }

setup_fixed_benchmark runFpLLLFirstShortVectorRandomBounded30Checksum where {
    repeats := 5
    minTotalSeconds := 1.0
    maxSecondsPerCall := 20.0
    expectedHash := some 0x4
    warmupFirstIter := true
  }

setup_fixed_benchmark runFpLLLFirstShortVectorRandomBounded45Checksum where {
    repeats := 5
    minTotalSeconds := 1.0
    maxSecondsPerCall := 20.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runFpLLLFirstShortVectorRandomBounded60Checksum where {
    repeats := 5
    minTotalSeconds := 1.0
    maxSecondsPerCall := 30.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runFpLLLFirstShortVectorRandomBounded75Checksum where {
    repeats := 5
    minTotalSeconds := 1.0
    maxSecondsPerCall := 30.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runFpLLLFirstShortVectorRandomBounded90Checksum where {
    repeats := 5
    minTotalSeconds := 1.0
    maxSecondsPerCall := 40.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runFpLLLFirstShortVectorRandomBounded120Checksum where {
    repeats := 5
    minTotalSeconds := 1.0
    maxSecondsPerCall := 60.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runFpLLLFirstShortVectorRandomBounded150Checksum where {
    repeats := 5
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runFpLLLFirstShortVectorRandomBounded180Checksum where {
    repeats := 5
    minTotalSeconds := 1.0
    maxSecondsPerCall := 120.0
    warmupFirstIter := true
  }

/- Certified-path fixed registrations for the random-bounded ladder. The
`runCertifiedFirstShortVector*` targets measure fpLLL candidate production plus
`certCheck`; the paired `runCertifiedChecker*` targets cache one fpLLL payload
and re-run only Lean's checker after warmup. -/
setup_fixed_benchmark runDispatchedFirstShortVectorRandomBounded30Checksum where {
    repeats := 3
    maxSecondsPerCall := 20.0
    expectedHash := some (Hashable.hash (runFirstShortVectorChecksum (prepRandomBoundedInput 30)))
  }

setup_fixed_benchmark runCertifiedFirstShortVectorRandomBounded30Checksum where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 20.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runCertifiedCheckerRandomBounded30Checksum where {
    repeats := 3
    maxSecondsPerCall := 20.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runCertifiedFirstShortVectorRandomBounded45Checksum where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 30.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runCertifiedCheckerRandomBounded45Checksum where {
    repeats := 3
    maxSecondsPerCall := 20.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runCertifiedFirstShortVectorRandomBounded60Checksum where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 40.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runCertifiedCheckerRandomBounded60Checksum where {
    repeats := 3
    maxSecondsPerCall := 30.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runCertifiedFirstShortVectorRandomBounded75Checksum where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 50.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runCertifiedCheckerRandomBounded75Checksum where {
    repeats := 3
    maxSecondsPerCall := 40.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runCertifiedFirstShortVectorRandomBounded90Checksum where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 60.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runCertifiedCheckerRandomBounded90Checksum where {
    repeats := 3
    maxSecondsPerCall := 50.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runCertifiedFirstShortVectorRandomBounded120Checksum where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runCertifiedCheckerRandomBounded120Checksum where {
    repeats := 3
    maxSecondsPerCall := 80.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runCertifiedFirstShortVectorRandomBounded150Checksum where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 120.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runCertifiedCheckerRandomBounded150Checksum where {
    repeats := 3
    maxSecondsPerCall := 120.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runCertifiedFirstShortVectorRandomBounded180Checksum where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 180.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runCertifiedCheckerRandomBounded180Checksum where {
    repeats := 3
    maxSecondsPerCall := 180.0
    warmupFirstIter := true
  }

/- Fixed bottom-rung Lean/fpLLL comparison for the harsh-cubic family at
`n = 15`, the first rung of the scientific parametric ladder. The fpLLL
comparison also follows the full harsh-cubic comparator ladder. -/
setup_fixed_benchmark runFirstShortVectorHarshCubic15Checksum where {
    repeats := 5
    maxSecondsPerCall := 20.0
    expectedHash := some (Hashable.hash (runFirstShortVectorChecksum (prepHarshCubicInput 15)))
  }

setup_fixed_benchmark runFpLLLFirstShortVectorHarshCubic15Checksum where {
    repeats := 5
    minTotalSeconds := 1.0
    maxSecondsPerCall := 20.0
    expectedHash := some 0x6ccfd453f897ff98
    warmupFirstIter := true
  }

setup_fixed_benchmark runFpLLLFirstShortVectorHarshCubic20Checksum where {
    repeats := 5
    minTotalSeconds := 1.0
    maxSecondsPerCall := 20.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runFpLLLFirstShortVectorHarshCubic25Checksum where {
    repeats := 5
    minTotalSeconds := 1.0
    maxSecondsPerCall := 20.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runFpLLLFirstShortVectorHarshCubic30Checksum where {
    repeats := 5
    minTotalSeconds := 1.0
    maxSecondsPerCall := 20.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runFpLLLFirstShortVectorHarshCubic35Checksum where {
    repeats := 5
    minTotalSeconds := 1.0
    maxSecondsPerCall := 20.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runFpLLLFirstShortVectorHarshCubic40Checksum where {
    repeats := 5
    minTotalSeconds := 1.0
    maxSecondsPerCall := 20.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runFpLLLFirstShortVectorHarshCubic45Checksum where {
    repeats := 5
    minTotalSeconds := 1.0
    maxSecondsPerCall := 20.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runFpLLLFirstShortVectorHarshCubic50Checksum where {
    repeats := 5
    minTotalSeconds := 1.0
    maxSecondsPerCall := 20.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runFpLLLFirstShortVectorHarshCubic55Checksum where {
    repeats := 5
    minTotalSeconds := 1.0
    maxSecondsPerCall := 20.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runFpLLLFirstShortVectorHarshCubic60Checksum where {
    repeats := 5
    maxSecondsPerCall := 20.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runFpLLLFirstShortVectorHarshCubic65Checksum where {
    repeats := 5
    maxSecondsPerCall := 20.0
    warmupFirstIter := true
  }

/- Certified-path fixed registrations for the harsh-cubic ladder. -/
setup_fixed_benchmark runDispatchedFirstShortVectorHarshCubic15Checksum where {
    repeats := 3
    maxSecondsPerCall := 20.0
    expectedHash := some (Hashable.hash (runFirstShortVectorChecksum (prepHarshCubicInput 15)))
  }

setup_fixed_benchmark runCertifiedFirstShortVectorHarshCubic15Checksum where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 20.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runCertifiedCheckerHarshCubic15Checksum where {
    repeats := 3
    maxSecondsPerCall := 20.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runCertifiedFirstShortVectorHarshCubic20Checksum where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 20.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runCertifiedCheckerHarshCubic20Checksum where {
    repeats := 3
    maxSecondsPerCall := 20.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runCertifiedFirstShortVectorHarshCubic25Checksum where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 20.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runCertifiedCheckerHarshCubic25Checksum where {
    repeats := 3
    maxSecondsPerCall := 20.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runCertifiedFirstShortVectorHarshCubic30Checksum where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 20.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runCertifiedCheckerHarshCubic30Checksum where {
    repeats := 3
    maxSecondsPerCall := 20.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runCertifiedFirstShortVectorHarshCubic35Checksum where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 20.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runCertifiedCheckerHarshCubic35Checksum where {
    repeats := 3
    maxSecondsPerCall := 20.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runCertifiedFirstShortVectorHarshCubic40Checksum where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 20.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runCertifiedCheckerHarshCubic40Checksum where {
    repeats := 3
    maxSecondsPerCall := 20.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runCertifiedFirstShortVectorHarshCubic45Checksum where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 20.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runCertifiedCheckerHarshCubic45Checksum where {
    repeats := 3
    maxSecondsPerCall := 20.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runCertifiedFirstShortVectorHarshCubic50Checksum where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 20.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runCertifiedCheckerHarshCubic50Checksum where {
    repeats := 3
    maxSecondsPerCall := 20.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runCertifiedFirstShortVectorHarshCubic55Checksum where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 20.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runCertifiedCheckerHarshCubic55Checksum where {
    repeats := 3
    maxSecondsPerCall := 20.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runCertifiedFirstShortVectorHarshCubic60Checksum where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 20.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runCertifiedCheckerHarshCubic60Checksum where {
    repeats := 3
    maxSecondsPerCall := 20.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runCertifiedFirstShortVectorHarshCubic65Checksum where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 20.0
    warmupFirstIter := true
  }

setup_fixed_benchmark runCertifiedCheckerHarshCubic65Checksum where {
    repeats := 3
    maxSecondsPerCall := 20.0
    warmupFirstIter := true
  }

/- One certified check per rung of both ladders; the observed value pins the
reducedness-decision tally to "9 rungs dispatched to the interval checker
(harsh-cubic n ≥ 30, random-bounded n ≥ 180), 10 to the exact checker by
the size predictor, zero indecision fallbacks". -/
setup_fixed_benchmark runCertifiedCheckerIntervalTally where {
    repeats := 1
    maxSecondsPerCall := 120.0
    expectedHash := some (Hashable.hash (((9 * 65537 + 10) * 65537 : Int)))
  }

/- Fallback-rate diagnostic: the steered reducer certified on every steered rung
of both ladders (`fellBack = 0`). The pinned hash records the `certified` count
(16 = the rungs `Hex.steerWins` routes to steering under the unified `n ≥ 30`
floor: harsh-cubic n ≥ 30 — 8 rungs — and random-bounded n ≥ 30 — 8 rungs,
n=30 now included after the `(δ + 3)/4` steering-margin fix); a fallback would
flip `fellBack` nonzero and throw before the hash is reached. -/
setup_fixed_benchmark runSteeredFallbackTally where {
    repeats := 1
    maxSecondsPerCall := 120.0
    expectedHash := some (Hashable.hash ((16 * 65537 : Int)))
  }

/- Complexity derivation: random-bounded inputs have square dimension `n` and
entries generated by the committed LCG seed with `|entry| <= 30`. This
near-orthogonal fixture has few Lovasz swaps, so the public `firstShortVector`
entry point is dominated by `LLLState.ofBasis` plus triangular size reduction
rather than by the textbook worst-case swap count. The `Nat.log2 (n + 1)`
factor records the slow determinant/coefficient bit-width growth in the exact
integer state. -/
setup_benchmark runFirstShortVectorRandomBoundedChecksum n =>
    firstShortVectorRandomBoundedComplexity n
  with prep := prepRandomBoundedInput
  where {
    paramFloor := 30
    paramCeiling := 180
    paramSchedule := .custom #[30, 45, 60, 75, 90, 120, 150, 180]
    maxSecondsPerCall := 20.0
    targetInnerNanos := 1_000_000_000
    signalFloorMultiplier := 1.0
  }

/- Complexity derivation: harsh-cubic inputs have square dimension `n` and
entry bit-length approximately `3.3 * n`, following the verified-Isabelle
paper regime named in `phase4.input_families`. The committed fixture is still
near-orthogonal rather than worst-case LLL; it exercises the quartic row-
operation surface and repeated logarithmic coefficient-growth factors from the
exact-integer row operations, while the separate
`runOfBasisHarshCubicChecksum` target keeps the initial Gram-Schmidt
construction attributable. -/
setup_benchmark runFirstShortVectorHarshCubicChecksum n =>
    firstShortVectorHarshCubicComplexity n
  with prep := prepHarshCubicInput
  where {
    paramFloor := 15
    paramCeiling := 55
    paramSchedule := .custom #[15, 20, 25, 30, 35, 40, 45, 50, 55]
    maxSecondsPerCall := 20.0
    targetInnerNanos := 1_000_000_000
    signalFloorMultiplier := 1.0
  }

/- Fixed external-comparator registrations. The paired Lean and Isabelle
targets return the squared norm of the first LLL vector so `compare` can join
on a semantic scalar, not an implementation-specific reduced-basis encoding. -/
setup_fixed_benchmark runFirstShortVectorBZRecombinationNormSq where {
    repeats := 3
    maxSecondsPerCall := 60.0
    expectedHash := some (Hashable.hash (runFirstShortVectorNormSq bzRecombinationInput))
  }

setup_fixed_benchmark runIsabelleBZRecombinationNormSq where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 60.0
    expectedHash := some (Hashable.hash (runFirstShortVectorNormSq bzRecombinationInput))
    warmupFirstIter := true
  }

setup_fixed_benchmark runFirstShortVectorRandomBoundedNormSq30 where {
    repeats := 3
    maxSecondsPerCall := 20.0
    expectedHash := some (firstShortVectorRandomBoundedNormSqHash 30)
  }

setup_fixed_benchmark runIsabelleRandomBoundedNormSq30 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 20.0
    expectedHash := some (firstShortVectorRandomBoundedNormSqHash 30)
    warmupFirstIter := true
  }

setup_fixed_benchmark runFirstShortVectorRandomBoundedNormSq45 where {
    repeats := 3
    maxSecondsPerCall := 20.0
    expectedHash := some (firstShortVectorRandomBoundedNormSqHash 45)
  }

setup_fixed_benchmark runIsabelleRandomBoundedNormSq45 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 20.0
    expectedHash := some (firstShortVectorRandomBoundedNormSqHash 45)
    warmupFirstIter := true
  }

setup_fixed_benchmark runFirstShortVectorRandomBoundedNormSq60 where {
    repeats := 3
    maxSecondsPerCall := 30.0
    expectedHash := some (firstShortVectorRandomBoundedNormSqHash 60)
  }

setup_fixed_benchmark runIsabelleRandomBoundedNormSq60 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 30.0
    expectedHash := some (firstShortVectorRandomBoundedNormSqHash 60)
    warmupFirstIter := true
  }

setup_fixed_benchmark runFirstShortVectorRandomBoundedNormSq75 where {
    repeats := 3
    maxSecondsPerCall := 30.0
    expectedHash := some (firstShortVectorRandomBoundedNormSqHash 75)
  }

setup_fixed_benchmark runIsabelleRandomBoundedNormSq75 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 30.0
    expectedHash := some (firstShortVectorRandomBoundedNormSqHash 75)
    warmupFirstIter := true
  }

setup_fixed_benchmark runFirstShortVectorRandomBoundedNormSq90 where {
    repeats := 3
    maxSecondsPerCall := 40.0
    expectedHash := some (firstShortVectorRandomBoundedNormSqHash 90)
  }

setup_fixed_benchmark runIsabelleRandomBoundedNormSq90 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 40.0
    expectedHash := some (firstShortVectorRandomBoundedNormSqHash 90)
    warmupFirstIter := true
  }

setup_fixed_benchmark runFirstShortVectorRandomBoundedNormSq120 where {
    repeats := 3
    maxSecondsPerCall := 60.0
    expectedHash := some (firstShortVectorRandomBoundedNormSqHash 120)
  }

setup_fixed_benchmark runIsabelleRandomBoundedNormSq120 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 60.0
    expectedHash := some (firstShortVectorRandomBoundedNormSqHash 120)
    warmupFirstIter := true
  }

setup_fixed_benchmark runFirstShortVectorRandomBoundedNormSq150 where {
    repeats := 3
    maxSecondsPerCall := 90.0
    expectedHash := some (firstShortVectorRandomBoundedNormSqHash 150)
  }

setup_fixed_benchmark runIsabelleRandomBoundedNormSq150 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    expectedHash := some (firstShortVectorRandomBoundedNormSqHash 150)
    warmupFirstIter := true
  }

setup_fixed_benchmark runFirstShortVectorRandomBoundedNormSq180 where {
    repeats := 3
    maxSecondsPerCall := 120.0
    expectedHash := some (firstShortVectorRandomBoundedNormSqHash 180)
  }

setup_fixed_benchmark runIsabelleRandomBoundedNormSq180 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 120.0
    expectedHash := some (firstShortVectorRandomBoundedNormSqHash 180)
    warmupFirstIter := true
  }

setup_fixed_benchmark runFirstShortVectorHarshCubicNormSq15 where {
    repeats := 3
    maxSecondsPerCall := 20.0
    expectedHash := some (firstShortVectorHarshCubicNormSqHash 15)
  }

setup_fixed_benchmark runIsabelleHarshCubicNormSq15 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    expectedHash := some (firstShortVectorHarshCubicNormSqHash 15)
    warmupFirstIter := true
  }

setup_fixed_benchmark runFirstShortVectorHarshCubicNormSq20 where {
    repeats := 3
    maxSecondsPerCall := 20.0
    expectedHash := some (firstShortVectorHarshCubicNormSqHash 20)
  }

setup_fixed_benchmark runIsabelleHarshCubicNormSq20 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    expectedHash := some (firstShortVectorHarshCubicNormSqHash 20)
    warmupFirstIter := true
  }

setup_fixed_benchmark runFirstShortVectorHarshCubicNormSq25 where {
    repeats := 3
    maxSecondsPerCall := 30.0
    expectedHash := some (firstShortVectorHarshCubicNormSqHash 25)
  }

setup_fixed_benchmark runIsabelleHarshCubicNormSq25 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    expectedHash := some (firstShortVectorHarshCubicNormSqHash 25)
    warmupFirstIter := true
  }

setup_fixed_benchmark runFirstShortVectorHarshCubicNormSq30 where {
    repeats := 3
    maxSecondsPerCall := 40.0
    expectedHash := some (firstShortVectorHarshCubicNormSqHash 30)
  }

setup_fixed_benchmark runIsabelleHarshCubicNormSq30 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 40.0
    expectedHash := some (firstShortVectorHarshCubicNormSqHash 30)
    warmupFirstIter := true
  }

setup_fixed_benchmark runFirstShortVectorHarshCubicNormSq35 where {
    repeats := 3
    maxSecondsPerCall := 40.0
    expectedHash := some (firstShortVectorHarshCubicNormSqHash 35)
  }

setup_fixed_benchmark runIsabelleHarshCubicNormSq35 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 60.0
    expectedHash := some (firstShortVectorHarshCubicNormSqHash 35)
    warmupFirstIter := true
  }

setup_fixed_benchmark runFirstShortVectorHarshCubicNormSq40 where {
    repeats := 3
    maxSecondsPerCall := 50.0
    expectedHash := some (firstShortVectorHarshCubicNormSqHash 40)
  }

setup_fixed_benchmark runIsabelleHarshCubicNormSq40 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 60.0
    expectedHash := some (firstShortVectorHarshCubicNormSqHash 40)
    warmupFirstIter := true
  }

setup_fixed_benchmark runFirstShortVectorHarshCubicNormSq45 where {
    repeats := 3
    maxSecondsPerCall := 60.0
    expectedHash := some (firstShortVectorHarshCubicNormSqHash 45)
  }

setup_fixed_benchmark runIsabelleHarshCubicNormSq45 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 60.0
    expectedHash := some (firstShortVectorHarshCubicNormSqHash 45)
    warmupFirstIter := true
  }

setup_fixed_benchmark runFirstShortVectorHarshCubicNormSq50 where {
    repeats := 3
    maxSecondsPerCall := 60.0
    expectedHash := some (firstShortVectorHarshCubicNormSqHash 50)
  }

setup_fixed_benchmark runIsabelleHarshCubicNormSq50 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 60.0
    expectedHash := some (firstShortVectorHarshCubicNormSqHash 50)
    warmupFirstIter := true
  }

setup_fixed_benchmark runFirstShortVectorHarshCubicNormSq55 where {
    repeats := 3
    maxSecondsPerCall := 60.0
    expectedHash := some (firstShortVectorHarshCubicNormSqHash 55)
  }

setup_fixed_benchmark runIsabelleHarshCubicNormSq55 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 60.0
    expectedHash := some (firstShortVectorHarshCubicNormSqHash 55)
    warmupFirstIter := true
  }

setup_fixed_benchmark runFirstShortVectorHarshCubicNormSq60 where {
    repeats := 3
    maxSecondsPerCall := 60.0
    expectedHash := some (firstShortVectorHarshCubicNormSqHash 60)
  }

setup_fixed_benchmark runIsabelleHarshCubicNormSq60 where {
    repeats := 3
    maxSecondsPerCall := 60.0
    expectedHash := some (firstShortVectorHarshCubicNormSqHash 60)
    warmupFirstIter := true
  }

setup_fixed_benchmark runFirstShortVectorHarshCubicNormSq65 where {
    repeats := 3
    maxSecondsPerCall := 60.0
    expectedHash := some (firstShortVectorHarshCubicNormSqHash 65)
  }

setup_fixed_benchmark runNativeFirstShortVectorRandomBoundedNormSq30 where {
    repeats := 3
    maxSecondsPerCall := 20.0
    expectedHash := some (firstShortVectorRandomBoundedNormSqHash 30)
  }

setup_fixed_benchmark runNativeFirstShortVectorRandomBoundedNormSq45 where {
    repeats := 3
    maxSecondsPerCall := 20.0
    expectedHash := some (firstShortVectorRandomBoundedNormSqHash 45)
  }

setup_fixed_benchmark runNativeFirstShortVectorRandomBoundedNormSq60 where {
    repeats := 3
    maxSecondsPerCall := 30.0
    expectedHash := some (firstShortVectorRandomBoundedNormSqHash 60)
  }

setup_fixed_benchmark runNativeFirstShortVectorRandomBoundedNormSq75 where {
    repeats := 3
    maxSecondsPerCall := 30.0
    expectedHash := some (firstShortVectorRandomBoundedNormSqHash 75)
  }

setup_fixed_benchmark runNativeFirstShortVectorRandomBoundedNormSq90 where {
    repeats := 3
    maxSecondsPerCall := 40.0
    expectedHash := some (firstShortVectorRandomBoundedNormSqHash 90)
  }

setup_fixed_benchmark runNativeFirstShortVectorRandomBoundedNormSq120 where {
    repeats := 3
    maxSecondsPerCall := 60.0
    expectedHash := some (firstShortVectorRandomBoundedNormSqHash 120)
  }

setup_fixed_benchmark runNativeFirstShortVectorRandomBoundedNormSq150 where {
    repeats := 3
    maxSecondsPerCall := 90.0
    expectedHash := some (firstShortVectorRandomBoundedNormSqHash 150)
  }

setup_fixed_benchmark runNativeFirstShortVectorRandomBoundedNormSq180 where {
    repeats := 3
    maxSecondsPerCall := 120.0
    expectedHash := some (firstShortVectorRandomBoundedNormSqHash 180)
  }

setup_fixed_benchmark runNativeFirstShortVectorHarshCubicNormSq15 where {
    repeats := 3
    maxSecondsPerCall := 20.0
    expectedHash := some (firstShortVectorHarshCubicNormSqHash 15)
  }

setup_fixed_benchmark runNativeFirstShortVectorHarshCubicNormSq20 where {
    repeats := 3
    maxSecondsPerCall := 20.0
    expectedHash := some (firstShortVectorHarshCubicNormSqHash 20)
  }

setup_fixed_benchmark runNativeFirstShortVectorHarshCubicNormSq25 where {
    repeats := 3
    maxSecondsPerCall := 30.0
    expectedHash := some (firstShortVectorHarshCubicNormSqHash 25)
  }

setup_fixed_benchmark runNativeFirstShortVectorHarshCubicNormSq30 where {
    repeats := 3
    maxSecondsPerCall := 40.0
    expectedHash := some (firstShortVectorHarshCubicNormSqHash 30)
  }

setup_fixed_benchmark runNativeFirstShortVectorHarshCubicNormSq35 where {
    repeats := 3
    maxSecondsPerCall := 40.0
    expectedHash := some (firstShortVectorHarshCubicNormSqHash 35)
  }

setup_fixed_benchmark runNativeFirstShortVectorHarshCubicNormSq40 where {
    repeats := 3
    maxSecondsPerCall := 50.0
    expectedHash := some (firstShortVectorHarshCubicNormSqHash 40)
  }

setup_fixed_benchmark runNativeFirstShortVectorHarshCubicNormSq45 where {
    repeats := 3
    maxSecondsPerCall := 60.0
    expectedHash := some (firstShortVectorHarshCubicNormSqHash 45)
  }

setup_fixed_benchmark runNativeFirstShortVectorHarshCubicNormSq50 where {
    repeats := 3
    maxSecondsPerCall := 60.0
    expectedHash := some (firstShortVectorHarshCubicNormSqHash 50)
  }

setup_fixed_benchmark runNativeFirstShortVectorHarshCubicNormSq55 where {
    repeats := 3
    maxSecondsPerCall := 60.0
    expectedHash := some (firstShortVectorHarshCubicNormSqHash 55)
  }

setup_fixed_benchmark runNativeFirstShortVectorHarshCubicNormSq60 where {
    repeats := 3
    maxSecondsPerCall := 60.0
    expectedHash := some (firstShortVectorHarshCubicNormSqHash 60)
  }

setup_fixed_benchmark runNativeFirstShortVectorHarshCubicNormSq65 where {
    repeats := 3
    maxSecondsPerCall := 60.0
    expectedHash := some (firstShortVectorHarshCubicNormSqHash 65)
  }


setup_fixed_benchmark runIsabelleHarshCubicNormSq65 where {
    repeats := 3
    maxSecondsPerCall := 60.0
    expectedHash := some (firstShortVectorHarshCubicNormSqHash 65)
    warmupFirstIter := true
  }

/- Verified-Isabelle certified-LLL registrations. These use the Zenodo
`svp_certified` driver, which invokes the `fplll` binary per request and then
checks the two-transform certificate before returning the squared norm. -/
setup_fixed_benchmark runIsabelleCertifiedProcessFloorNormSq where {
    repeats := 5
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    expectedHash := none
    warmupFirstIter := true
  }

setup_fixed_benchmark runIsabelleCertifiedRandomBoundedNormSq30 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 20.0
    expectedHash := some (firstShortVectorRandomBoundedNormSqHash 30)
    warmupFirstIter := true
  }

setup_fixed_benchmark runIsabelleCertifiedRandomBoundedNormSq45 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 20.0
    expectedHash := some (firstShortVectorRandomBoundedNormSqHash 45)
    warmupFirstIter := true
  }

setup_fixed_benchmark runIsabelleCertifiedRandomBoundedNormSq60 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 30.0
    expectedHash := some (firstShortVectorRandomBoundedNormSqHash 60)
    warmupFirstIter := true
  }

setup_fixed_benchmark runIsabelleCertifiedRandomBoundedNormSq75 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 30.0
    expectedHash := some (firstShortVectorRandomBoundedNormSqHash 75)
    warmupFirstIter := true
  }

setup_fixed_benchmark runIsabelleCertifiedRandomBoundedNormSq90 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 40.0
    expectedHash := some (firstShortVectorRandomBoundedNormSqHash 90)
    warmupFirstIter := true
  }

setup_fixed_benchmark runIsabelleCertifiedRandomBoundedNormSq120 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 60.0
    expectedHash := some (firstShortVectorRandomBoundedNormSqHash 120)
    warmupFirstIter := true
  }

setup_fixed_benchmark runIsabelleCertifiedRandomBoundedNormSq150 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    expectedHash := some (firstShortVectorRandomBoundedNormSqHash 150)
    warmupFirstIter := true
  }

setup_fixed_benchmark runIsabelleCertifiedRandomBoundedNormSq180 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 120.0
    expectedHash := some (firstShortVectorRandomBoundedNormSqHash 180)
    warmupFirstIter := true
  }

setup_fixed_benchmark runIsabelleCertifiedHarshCubicNormSq15 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    expectedHash := some (firstShortVectorHarshCubicNormSqHash 15)
    warmupFirstIter := true
  }

setup_fixed_benchmark runIsabelleCertifiedHarshCubicNormSq20 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    expectedHash := some (firstShortVectorHarshCubicNormSqHash 20)
    warmupFirstIter := true
  }

setup_fixed_benchmark runIsabelleCertifiedHarshCubicNormSq25 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 90.0
    expectedHash := some (firstShortVectorHarshCubicNormSqHash 25)
    warmupFirstIter := true
  }

setup_fixed_benchmark runIsabelleCertifiedHarshCubicNormSq30 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 40.0
    expectedHash := some (firstShortVectorHarshCubicNormSqHash 30)
    warmupFirstIter := true
  }

setup_fixed_benchmark runIsabelleCertifiedHarshCubicNormSq35 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 60.0
    expectedHash := some (firstShortVectorHarshCubicNormSqHash 35)
    warmupFirstIter := true
  }

setup_fixed_benchmark runIsabelleCertifiedHarshCubicNormSq40 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 60.0
    expectedHash := some (firstShortVectorHarshCubicNormSqHash 40)
    warmupFirstIter := true
  }

setup_fixed_benchmark runIsabelleCertifiedHarshCubicNormSq45 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 60.0
    expectedHash := some (firstShortVectorHarshCubicNormSqHash 45)
    warmupFirstIter := true
  }

setup_fixed_benchmark runIsabelleCertifiedHarshCubicNormSq50 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 60.0
    expectedHash := some (firstShortVectorHarshCubicNormSqHash 50)
    warmupFirstIter := true
  }

setup_fixed_benchmark runIsabelleCertifiedHarshCubicNormSq55 where {
    repeats := 3
    minTotalSeconds := 1.0
    maxSecondsPerCall := 60.0
    expectedHash := some (firstShortVectorHarshCubicNormSqHash 55)
    warmupFirstIter := true
  }

setup_fixed_benchmark runIsabelleCertifiedHarshCubicNormSq60 where {
    repeats := 3
    maxSecondsPerCall := 60.0
    expectedHash := some (firstShortVectorHarshCubicNormSqHash 60)
    warmupFirstIter := true
  }

setup_fixed_benchmark runIsabelleCertifiedHarshCubicNormSq65 where {
    repeats := 3
    maxSecondsPerCall := 60.0
    expectedHash := some (firstShortVectorHarshCubicNormSqHash 65)
    warmupFirstIter := true
  }

end Hex.LLLBench

def main (args : List String) : IO UInt32 :=
  LeanBench.Cli.dispatch args
