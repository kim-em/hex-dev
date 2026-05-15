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

* `fpLLL via fpylll`: process-call registrations send each matrix to
  `scripts/oracle/lll_fpylll_bench_driver.py`, the persistent
  subprocess driver wired in HO-17 (#3660). The driver imports
  `fpylll` once at startup and calls `fpylll.LLL.reduction` with
  `delta = 0.75` (matching Lean's `δ = 3/4`) per request. The
  comparator is classified informational in
  `SPEC/Libraries/hex-lll.md` because fpLLL's floating-point
  Gram-Schmidt implementation (Nguyen-Stehle; fpylll 0.6 or newer
  supported by the existing oracle driver) bypasses the
  exact-integer operand-size drift paid by this verified
  implementation. Ratios are recorded for orientation but do not gate
  Phase 4. The conformance-mode entry point remains
  `scripts/oracle/lll_fpylll.py --check`.

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

## Comparator-call protocol (persistent subprocess)

Per `SPEC/benchmarking.md` (post-#3657) "External comparators / Process
call", Phase-4 process-call comparators with non-negligible per-call
overhead use a persistent subprocess: one driver is spawned per
`lake exe hexlll_bench run` invocation, and each measured call sends one
framed request to its stdin and reads one framed reply from its stdout.

**Framing.** Each request is one line containing the input matrix in
Haskell's `[[Integer]]` read syntax — exactly the string produced by
`matrixHaskell` — terminated by `\n`. The same request line feeds
both the Isabelle and the fpylll persistent drivers; each emits a
single scalar per request, terminated by `\n`. Isabelle returns the
squared norm of its first reduced row; fpylll returns the integer
first-row checksum matching `Hex.LLLBench.intVectorChecksum` (the
scalar paired with `runFirstShortVector*Checksum`). Malformed
fpylll requests come back as `ERROR: <message>`; the Lean parser
treats any non-integer reply as a driver fault and triggers the
retry path.

**Lifetime.** Each driver is spawned lazily on first use into a
module-level `IO.Ref (Option PersistentComparator)`
(`isabelleChildRef` for Isabelle, `fpylllChildRef` for fpylll) and
reused for every subsequent call in the same `hexlll_bench`
process. The child's stdin is held by the bench process via
`Child.takeStdin`; on process exit, the OS reaps each driver via
EOF on stdin.

**Error handling.** If `requestLine` raises any `IO` error, the
bench wiring drops the cached child handle, re-spawns the
relevant driver (Isabelle from
`scripts/oracle/setup_lll_isabelle.sh`; fpylll from the path in
`HEX_LLL_FPYLLL_BENCH_DRIVER` or the default
`scripts/oracle/lll_fpylll_bench_driver.py`), and retries the
request once. Persistent failure (e.g. setup script failure or
repeated driver crash) surfaces as an `IO.userError`.

**Per-call overhead.** Piping 10000 trivial inputs
(`[[1,0],[0,1]]`) through the patched Isabelle binary on the audit
host takes ~110 ms wall total (median of 5 trials), of which
~22 ms is the one-time GHC startup; per-call Isabelle protocol
overhead is ~9 µs in steady state. The persistent fpylll driver
pays a one-time CPython + `import fpylll` startup and per-call
steady-state overhead of ~34 µs (median of 5 trials of 1000
trivial `[[1,0],[0,1]]` requests on the audit host). The previous
shape paid ~116 ms per call to CPython start + fpylll import +
single `fpylll.LLL.reduction`. Both persistent figures are three
orders of magnitude below the per-call interpreter-start cost
and well below the 5 % overhead-to-measured-time floor
`SPEC/benchmarking.md` requires for honest ratios.

**Interaction with `setup_fixed_benchmark`.** `lean-bench` spawns
one fresh `hexlll_bench` child process per measured repeat of a
fixed benchmark, so each repeat starts with cold `isabelleChildRef`
and `fpylllChildRef`. The persistent harness still avoids per-call
`IO.Process.output` and per-call `IO.FS.writeFile` round-trips
inside one child, but the one-time GHC start (Isabelle) /
CPython + fpylll import (fpylll) cost is incurred per repeat at
this benchmark shape. Wall-time-per-call for fixed `runIsabelle*`
and `runFpylll*` targets remains dominated by interpreter startup;
the protocol-overhead figures above determine whether comparator
ratios qualify for the eligible range in HO-18's regenerated
report.

**Driver path overrides.** `HEX_LLL_FPYLLL_BENCH_DRIVER` overrides
the default driver script path (relative to the bench process's
cwd, which is the repo root under `lake exe`).
`HEX_LLL_FPYLLL_BENCH_PYTHON` overrides the interpreter command
(default `python3`). The Isabelle binary path is controlled by
`HEX_LLL_ISABELLE_SVP` as before.
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

/-- Matrix input for benchmarking `LLLState.ofBasis` itself. -/
structure OfBasisInput where
  rows : Nat
  cols : Nat
  basis : Matrix Int rows cols
  hind : basis.independent
  j : Fin rows
  k : Fin rows
  hjk : j.val < k.val

instance : Hashable OfBasisInput where
  hash input :=
    hash (input.rows, input.cols, input.j.val, input.k.val)

/-- Prepared basis for `lll.firstShortVector` benchmarks. -/
structure FirstShortVectorInput where
  rows : Nat
  cols : Nat
  basis : Matrix Int rows cols
  hn : 1 ≤ rows
  hind : basis.independent

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

private theorem generatedBasis_independent (rows salt : Nat) :
    (generatedBasis rows salt).independent := by
  apply Matrix.independent_of_upperTriangular_pos_diag
  · intro i j hij
    simp [generatedBasis, Matrix.ofFn, Vector.getElem_ofFn, entryValue, hij]
  · intro i
    simp [generatedBasis, Matrix.ofFn, Vector.getElem_ofFn, entryValue]
    omega

/-- Build the certified executable LLL state for a deterministic matrix. -/
def stateOf (b : Matrix Int n m) (hind : b.independent) : LLLState n m :=
  LLLState.ofBasis b hind

/-- Per-parameter fixture: a prepared `(n + 3) x (n + 3)` LLL state. -/
def prepStateInput (n : Nat) : StateInput :=
  let rows := n + 3
  let cols := rows
  let basis := generatedBasis rows 197
  let j : Fin rows := ⟨n + 1, by simp [rows]⟩
  let k : Fin rows := ⟨n + 2, by simp [rows]⟩
  { rows := rows
    cols := cols
    state := stateOf basis (generatedBasis_independent rows 197)
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
    hn := by decide
    hind := by
      apply Matrix.independent_of_upperTriangular_pos_diag <;> decide }

instance : Nonempty FirstShortVectorInput :=
  ⟨bzRecombinationInput⟩

initialize bzRecombinationInputRef : IO.Ref FirstShortVectorInput ←
  IO.mkRef bzRecombinationInput

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

private theorem randomBoundedBasis_independent (n seed : Nat) :
    (randomBoundedBasis n seed).independent := by
  apply Matrix.independent_of_upperTriangular_pos_diag
  · intro i j hij
    simp [randomBoundedBasis, Matrix.ofFn, Vector.getElem_ofFn, hij]
  · intro i
    simp [randomBoundedBasis, Matrix.ofFn, Vector.getElem_ofFn]

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
      exact Nat.le_max_right n 1
    hind := randomBoundedBasis_independent rows randomBoundedSwapSeed }

/-- Check that the first Lovasz comparison fails after the first
size-reduction pass, forcing at least one swap in the subsequent LLL step. -/
def firstLovaszCheckForcesSwap (input : FirstShortVectorInput) : Bool :=
  if hrows : 2 < input.rows then
    let sReduced := (LLLState.ofBasis input.basis input.hind).sizeReduce 1
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

private theorem harshCubicBasis_independent (n : Nat) :
    (harshCubicBasis n).independent := by
  apply Matrix.independent_of_upperTriangular_pos_diag
  · intro i j hij
    simp [harshCubicBasis, Matrix.ofFn, Vector.getElem_ofFn, hij]
  · intro i
    have hscale : (0 : Int) < harshCubicScale n := by
      dsimp [harshCubicScale]
      exact_mod_cast Nat.pow_pos (by decide : 0 < 2)
    simpa [harshCubicBasis, Matrix.ofFn, Vector.getElem_ofFn] using hscale

/-- Parametric harsh-cubic input family. The scientific ladder is densified at
`n in {15, 20, 25, 30, 35, 40, 45, 50, 55}`. -/
def prepHarshCubicInput (n : Nat) : FirstShortVectorInput :=
  let rows := max n 1
  let basis := harshCubicBasis rows
  { rows := rows
    cols := rows
    basis := basis
    hn := by
      exact Nat.le_max_right n 1
    hind := harshCubicBasis_independent rows }

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

private theorem ofBasisRandomBoundedBasis_independent (rows salt : Nat) :
    (ofBasisRandomBoundedBasis rows salt).independent := by
  apply Matrix.independent_of_upperTriangular_pos_diag
  · intro i j hij
    simp [ofBasisRandomBoundedBasis, Matrix.ofFn, Vector.getElem_ofFn,
      ofBasisRandomBoundedEntry, hij]
  · intro i
    simp [ofBasisRandomBoundedBasis, Matrix.ofFn, Vector.getElem_ofFn,
      ofBasisRandomBoundedEntry]
    omega

/-- Deterministic row-major square basis for the harsh-cubic family. -/
def ofBasisHarshCubicBasis (rows salt : Nat) : Matrix Int rows rows :=
  Matrix.ofFn fun i j => ofBasisHarshCubicEntry rows i.val j.val salt

private theorem ofBasisHarshCubicBasis_independent (rows salt : Nat) :
    (ofBasisHarshCubicBasis rows salt).independent := by
  apply Matrix.independent_of_upperTriangular_pos_diag
  · intro i j hij
    simp [ofBasisHarshCubicBasis, Matrix.ofFn, Vector.getElem_ofFn,
      ofBasisHarshCubicEntry, hij]
  · intro i
    have hpos : (0 : Int) <
        Int.ofNat (2 ^ (3 * rows + ((i.val + 2 * i.val + salt) % 5))) := by
      exact Int.ofNat_lt.mpr (Nat.pow_pos (by decide : 0 < 2))
    simpa [ofBasisHarshCubicBasis, Matrix.ofFn, Vector.getElem_ofFn,
      ofBasisHarshCubicEntry] using hpos

/-- General constructor for an `LLLState.ofBasis` benchmark fixture.
The benchmark parameter maps to `rows = n + 3`, so the final two row indices
are always available for the result checksum. -/
def prepOfBasisInput (n cols : Nat) (basis : Matrix Int (n + 3) cols)
    (hind : basis.independent) : OfBasisInput :=
  let rows := n + 3
  let j : Fin rows := ⟨n + 1, by simp [rows]⟩
  let k : Fin rows := ⟨n + 2, by simp [rows]⟩
  { rows := rows
    cols := cols
    basis := basis
    hind := hind
    j := j
    k := k
    hjk := by
      change n + 1 < n + 2
      omega }

/-- Per-parameter fixture for the BZ recombination input family. -/
def prepOfBasisBzRecombinationInput (n : Nat) : OfBasisInput :=
  let rows := n + 3
  let basis := generatedBasis rows 311
  prepOfBasisInput n rows basis (generatedBasis_independent rows 311)

/-- Per-parameter fixture for the random-bounded input family. -/
def prepOfBasisRandomBoundedInput (n : Nat) : OfBasisInput :=
  let rows := n + 3
  let basis := ofBasisRandomBoundedBasis rows 509
  prepOfBasisInput n rows basis (ofBasisRandomBoundedBasis_independent rows 509)

/-- Per-parameter fixture for the harsh-cubic input family. -/
def prepOfBasisHarshCubicInput (n : Nat) : OfBasisInput :=
  let rows := n + 3
  let basis := ofBasisHarshCubicBasis rows 887
  prepOfBasisInput n rows basis (ofBasisHarshCubicBasis_independent rows 887)

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

/-- Model for one stored rational coefficient projection. -/
def gramSchmidtCoeffComplexity (_n : Nat) : Nat :=
  1

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
row-operation surface and a logarithmic exact-integer overhead. -/
def firstShortVectorHarshCubicComplexity (n : Nat) : Nat :=
  n ^ 4 * (Nat.log2 (n + 1)) ^ 3

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
entry bit-length factor from the fixture's `3 * rows + O(1)` bits. -/
def ofBasisHarshCubicComplexity (n : Nat) : Nat :=
  let rows := n + 3
  rows * ofBasisComplexity rows rows

/-- Benchmark target: construct the initial integer LLL state for a basis. -/
def runOfBasisChecksum (input : OfBasisInput) : Int :=
  let s := LLLState.ofBasis input.basis input.hind
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

private theorem lllDeltaLower : (1 / 4 : Rat) < 3 / 4 := by
  grind

private theorem lllDeltaUpper : (3 / 4 : Rat) ≤ 1 := by
  grind

/-- Benchmark target: run LLL on one prepared basis and checksum the first row. -/
def runFirstShortVectorChecksum (input : FirstShortVectorInput) : Int :=
  intVectorChecksum
    (lll.firstShortVector input.basis (3 / 4)
      lllDeltaLower lllDeltaUpper input.hn input.hind)

/-- Benchmark comparator observable: squared norm of Lean's first LLL vector.
The verified-Isabelle Haskell extraction reports the same scalar. -/
def runFirstShortVectorNormSq (input : FirstShortVectorInput) : Int :=
  Vector.intNormSq
    (lll.firstShortVector input.basis (3 / 4)
      lllDeltaLower lllDeltaUpper input.hn input.hind)

def intRowHaskell (v : Vector Int n) : String :=
  "[" ++ String.intercalate "," ((List.finRange n).map fun j => toString v[j]) ++ "]"

def matrixHaskell (b : Matrix Int n m) : String :=
  "[" ++
    String.intercalate "," ((List.finRange n).map fun i => intRowHaskell (b.row i)) ++
    "]"

initialize isabelleBinaryRef : IO.Ref (Option String) ← IO.mkRef none

def checkedProcessOutput (cmd : String) (args : Array String := #[]) : IO String := do
  let out ← IO.Process.output { cmd := cmd, args := args }
  if out.exitCode != 0 then
    throw <| IO.userError
      s!"process failed ({cmd}):\nstdout:\n{out.stdout}\nstderr:\n{out.stderr}"
  return out.stdout.trimAscii.toString

def resolveIsabelleBinary : IO String := do
  if let some cached ← isabelleBinaryRef.get then
    return cached
  let path ←
    match (← IO.getEnv "HEX_LLL_ISABELLE_SVP") with
    | some p => pure p
    | none => checkedProcessOutput "scripts/oracle/setup_lll_isabelle.sh"
  isabelleBinaryRef.set (some path)
  return path

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

/-- Lazily spawn the persistent `svp_verified` driver, or return the
cached handle. -/
def resolveIsabelleChild : IO PersistentComparator := do
  if let some ch ← isabelleChildRef.get then
    return ch
  let binary ← resolveIsabelleBinary
  let ch ← PersistentComparator.spawn binary
  isabelleChildRef.set (some ch)
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

def runIsabelleShortVectorNormSq (_tag : String) (input : FirstShortVectorInput) :
    IO Int := do
  let request := matrixHaskell input.basis
  parseIsabelleNormSq (← requestIsabelleLineWithRetry request 1)

initialize fpylllChildRef : IO.Ref (Option PersistentComparator) ←
  IO.mkRef none

private def envOr (name : String) (default : String) : IO String := do
  match (← IO.getEnv name) with
  | some v => return v
  | none => return default

private def fpylllDriverPath : IO String :=
  envOr "HEX_LLL_FPYLLL_BENCH_DRIVER" "scripts/oracle/lll_fpylll_bench_driver.py"

private def fpylllPythonCommand : IO String :=
  envOr "HEX_LLL_FPYLLL_BENCH_PYTHON" "python3"

/-- Lazily spawn the persistent `lll_fpylll_bench_driver.py` driver,
or return the cached handle. -/
def resolveFpylllChild : IO PersistentComparator := do
  if let some ch ← fpylllChildRef.get then
    return ch
  let py ← fpylllPythonCommand
  let script ← fpylllDriverPath
  let ch ← PersistentComparator.spawn py #[script]
  fpylllChildRef.set (some ch)
  return ch

/-- Parse one reply line from `lll_fpylll_bench_driver.py`. The
driver emits a single integer per request on success or a line
beginning `ERROR:` on failure; treat the latter as a driver fault so
the retry path can re-spawn. -/
def parseFpylllChecksum (text : String) : IO Int := do
  let trimmed := text.trimAscii.toString
  if trimmed.startsWith "ERROR:" then
    throw <| IO.userError s!"lll_fpylll_bench_driver: {trimmed}"
  match trimmed.toInt? with
  | some n => return n
  | none =>
    throw <| IO.userError
      s!"lll_fpylll_bench_driver emitted non-integer output: {text}"

/-- Send one matrix to the persistent fpylll driver and return the
raw reply line.

On process death, EOF before a reply line, or any IO error from the
protocol, the cached handle is dropped, a fresh driver is spawned,
and the call is retried once. Persistent failure surfaces as an
`IO.userError` from the retry path. -/
def requestFpylllLineWithRetry (request : String) : Nat → IO String
  | 0 => do
    let reply ← (← resolveFpylllChild).requestLine request
    if reply.isEmpty then
      throw <| IO.userError "lll_fpylll_bench_driver closed stdout before replying"
    return reply
  | Nat.succ remaining => do
    try
      let reply ← (← resolveFpylllChild).requestLine request
      if reply.isEmpty then
        throw <| IO.userError "lll_fpylll_bench_driver closed stdout before replying"
      return reply
    catch _ =>
      fpylllChildRef.set none
      requestFpylllLineWithRetry request remaining

/-- Invoke fpylll on one prepared basis via the persistent driver
and parse the first-row checksum. -/
def runFpylllFirstShortVectorChecksum (input : FirstShortVectorInput) : IO Int := do
  let request := matrixHaskell input.basis
  parseFpylllChecksum (← requestFpylllLineWithRetry request 1)

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

/-- fpylll comparator for the fixed BZ recombination input. -/
def runFpylllFirstShortVectorBZRecombinationChecksum : Unit → IO Int := fun _ => do
  runFpylllFirstShortVectorChecksum (← bzRecombinationInputRef.get)

/-- fpylll comparator for the random-bounded bottom rung (`n = 30`). -/
def runFpylllFirstShortVectorRandomBounded30Checksum : Unit → IO Int := fun _ => do
  runFpylllFirstShortVectorChecksum
    (← getCachedInput randomBoundedInput30Ref (fun _ => prepRandomBoundedInput 30))

/-- fpylll comparator for the harsh-cubic bottom rung (`n = 15`). -/
def runFpylllFirstShortVectorHarshCubic15Checksum : Unit → IO Int := fun _ => do
  runFpylllFirstShortVectorChecksum
    (← getCachedInput harshCubicInput15Ref (fun _ => prepHarshCubicInput 15))

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
    maxSecondsPerCall := 8.0
    targetInnerNanos := 1_000_000_000
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
    maxSecondsPerCall := 5.0
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
  }

/- Complexity derivation: `gramSchmidtCoeff` reads one stored `ν[k][j]` entry
and one stored `d[j+1]` denominator, then performs a single rational division. -/
setup_benchmark runGramSchmidtCoeffChecksum n => gramSchmidtCoeffComplexity n
  with prep := prepStateInput
  where {
    paramFloor := 32
    paramCeiling := 128
    paramSchedule := .custom #[32, 64, 96, 128]
    maxSecondsPerCall := 4.0
    targetInnerNanos := 2_000_000_000
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

/- Fixed bottom-rung Lean/fpylll comparison for the BZ recombination family.
The fpylll target is informational and process-call based; scheduled and
release bench runs use
`compare runFirstShortVectorBZRecombinationChecksum runFpylllFirstShortVectorBZRecombinationChecksum`
to record its ratio. -/
setup_fixed_benchmark runFpylllFirstShortVectorBZRecombinationChecksum where {
    repeats := 5
    maxSecondsPerCall := 20.0
    expectedHash := some 0x20001
  }

/- Fixed bottom-rung Lean/fpylll comparison for the random-bounded family at
`n = 30`, the first rung of the scientific parametric ladder. -/
setup_fixed_benchmark runFirstShortVectorRandomBounded30Checksum where {
    repeats := 5
    maxSecondsPerCall := 20.0
    expectedHash := some (Hashable.hash (runFirstShortVectorChecksum (prepRandomBoundedInput 30)))
  }

setup_fixed_benchmark runFpylllFirstShortVectorRandomBounded30Checksum where {
    repeats := 5
    maxSecondsPerCall := 20.0
    expectedHash := some 0x4
  }

/- Fixed bottom-rung Lean/fpylll comparison for the harsh-cubic family at
`n = 15`, the first rung of the scientific parametric ladder. -/
setup_fixed_benchmark runFirstShortVectorHarshCubic15Checksum where {
    repeats := 5
    maxSecondsPerCall := 20.0
    expectedHash := some (Hashable.hash (runFirstShortVectorChecksum (prepHarshCubicInput 15)))
  }

setup_fixed_benchmark runFpylllFirstShortVectorHarshCubic15Checksum where {
    repeats := 5
    maxSecondsPerCall := 20.0
    expectedHash := some 0x6ccfd453f897ff98
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
  }

/- Complexity derivation: harsh-cubic inputs have square dimension `n` and
entry bit-length approximately `3.3 * n`, following the verified-Isabelle
paper regime named in `phase4.input_families`. The committed fixture is still
near-orthogonal rather than worst-case LLL; empirically and structurally it
exercises the quartic exact-integer row-operation surface plus logarithmic
coefficient-growth factors, while the separate `runOfBasisHarshCubicChecksum`
target keeps the initial Gram-Schmidt construction attributable. -/
setup_benchmark runFirstShortVectorHarshCubicChecksum n =>
    firstShortVectorHarshCubicComplexity n
  with prep := prepHarshCubicInput
  where {
    paramFloor := 15
    paramCeiling := 55
    paramSchedule := .custom #[15, 20, 25, 30, 35, 40, 45, 50, 55]
    maxSecondsPerCall := 20.0
    targetInnerNanos := 1_000_000_000
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
    maxSecondsPerCall := 60.0
    expectedHash := some (Hashable.hash (runFirstShortVectorNormSq bzRecombinationInput))
  }

setup_fixed_benchmark runFirstShortVectorRandomBoundedNormSq30 where {
    repeats := 3
    maxSecondsPerCall := 20.0
    expectedHash := some (firstShortVectorRandomBoundedNormSqHash 30)
  }

setup_fixed_benchmark runIsabelleRandomBoundedNormSq30 where {
    repeats := 3
    maxSecondsPerCall := 20.0
    expectedHash := some (firstShortVectorRandomBoundedNormSqHash 30)
  }

setup_fixed_benchmark runFirstShortVectorRandomBoundedNormSq45 where {
    repeats := 3
    maxSecondsPerCall := 20.0
    expectedHash := some (firstShortVectorRandomBoundedNormSqHash 45)
  }

setup_fixed_benchmark runIsabelleRandomBoundedNormSq45 where {
    repeats := 3
    maxSecondsPerCall := 20.0
    expectedHash := some (firstShortVectorRandomBoundedNormSqHash 45)
  }

setup_fixed_benchmark runFirstShortVectorRandomBoundedNormSq60 where {
    repeats := 3
    maxSecondsPerCall := 30.0
    expectedHash := some (firstShortVectorRandomBoundedNormSqHash 60)
  }

setup_fixed_benchmark runIsabelleRandomBoundedNormSq60 where {
    repeats := 3
    maxSecondsPerCall := 30.0
    expectedHash := some (firstShortVectorRandomBoundedNormSqHash 60)
  }

setup_fixed_benchmark runFirstShortVectorRandomBoundedNormSq75 where {
    repeats := 3
    maxSecondsPerCall := 30.0
    expectedHash := some (firstShortVectorRandomBoundedNormSqHash 75)
  }

setup_fixed_benchmark runIsabelleRandomBoundedNormSq75 where {
    repeats := 3
    maxSecondsPerCall := 30.0
    expectedHash := some (firstShortVectorRandomBoundedNormSqHash 75)
  }

setup_fixed_benchmark runFirstShortVectorRandomBoundedNormSq90 where {
    repeats := 3
    maxSecondsPerCall := 40.0
    expectedHash := some (firstShortVectorRandomBoundedNormSqHash 90)
  }

setup_fixed_benchmark runIsabelleRandomBoundedNormSq90 where {
    repeats := 3
    maxSecondsPerCall := 40.0
    expectedHash := some (firstShortVectorRandomBoundedNormSqHash 90)
  }

setup_fixed_benchmark runFirstShortVectorRandomBoundedNormSq120 where {
    repeats := 3
    maxSecondsPerCall := 60.0
    expectedHash := some (firstShortVectorRandomBoundedNormSqHash 120)
  }

setup_fixed_benchmark runIsabelleRandomBoundedNormSq120 where {
    repeats := 3
    maxSecondsPerCall := 60.0
    expectedHash := some (firstShortVectorRandomBoundedNormSqHash 120)
  }

setup_fixed_benchmark runFirstShortVectorRandomBoundedNormSq150 where {
    repeats := 3
    maxSecondsPerCall := 90.0
    expectedHash := some (firstShortVectorRandomBoundedNormSqHash 150)
  }

setup_fixed_benchmark runIsabelleRandomBoundedNormSq150 where {
    repeats := 3
    maxSecondsPerCall := 90.0
    expectedHash := some (firstShortVectorRandomBoundedNormSqHash 150)
  }

setup_fixed_benchmark runFirstShortVectorRandomBoundedNormSq180 where {
    repeats := 3
    maxSecondsPerCall := 120.0
    expectedHash := some (firstShortVectorRandomBoundedNormSqHash 180)
  }

setup_fixed_benchmark runIsabelleRandomBoundedNormSq180 where {
    repeats := 3
    maxSecondsPerCall := 120.0
    expectedHash := some (firstShortVectorRandomBoundedNormSqHash 180)
  }

setup_fixed_benchmark runFirstShortVectorHarshCubicNormSq15 where {
    repeats := 3
    maxSecondsPerCall := 20.0
    expectedHash := some (firstShortVectorHarshCubicNormSqHash 15)
  }

setup_fixed_benchmark runIsabelleHarshCubicNormSq15 where {
    repeats := 3
    maxSecondsPerCall := 90.0
    expectedHash := some (firstShortVectorHarshCubicNormSqHash 15)
  }

setup_fixed_benchmark runFirstShortVectorHarshCubicNormSq20 where {
    repeats := 3
    maxSecondsPerCall := 20.0
    expectedHash := some (firstShortVectorHarshCubicNormSqHash 20)
  }

setup_fixed_benchmark runIsabelleHarshCubicNormSq20 where {
    repeats := 3
    maxSecondsPerCall := 90.0
    expectedHash := some (firstShortVectorHarshCubicNormSqHash 20)
  }

setup_fixed_benchmark runFirstShortVectorHarshCubicNormSq25 where {
    repeats := 3
    maxSecondsPerCall := 30.0
    expectedHash := some (firstShortVectorHarshCubicNormSqHash 25)
  }

setup_fixed_benchmark runIsabelleHarshCubicNormSq25 where {
    repeats := 3
    maxSecondsPerCall := 90.0
    expectedHash := some (firstShortVectorHarshCubicNormSqHash 25)
  }

setup_fixed_benchmark runFirstShortVectorHarshCubicNormSq30 where {
    repeats := 3
    maxSecondsPerCall := 40.0
    expectedHash := some (firstShortVectorHarshCubicNormSqHash 30)
  }

setup_fixed_benchmark runIsabelleHarshCubicNormSq30 where {
    repeats := 3
    maxSecondsPerCall := 40.0
    expectedHash := some (firstShortVectorHarshCubicNormSqHash 30)
  }

setup_fixed_benchmark runFirstShortVectorHarshCubicNormSq35 where {
    repeats := 3
    maxSecondsPerCall := 40.0
    expectedHash := some (firstShortVectorHarshCubicNormSqHash 35)
  }

setup_fixed_benchmark runIsabelleHarshCubicNormSq35 where {
    repeats := 3
    maxSecondsPerCall := 60.0
    expectedHash := some (firstShortVectorHarshCubicNormSqHash 35)
  }

setup_fixed_benchmark runFirstShortVectorHarshCubicNormSq40 where {
    repeats := 3
    maxSecondsPerCall := 50.0
    expectedHash := some (firstShortVectorHarshCubicNormSqHash 40)
  }

setup_fixed_benchmark runIsabelleHarshCubicNormSq40 where {
    repeats := 3
    maxSecondsPerCall := 60.0
    expectedHash := some (firstShortVectorHarshCubicNormSqHash 40)
  }

setup_fixed_benchmark runFirstShortVectorHarshCubicNormSq45 where {
    repeats := 3
    maxSecondsPerCall := 60.0
    expectedHash := some (firstShortVectorHarshCubicNormSqHash 45)
  }

setup_fixed_benchmark runIsabelleHarshCubicNormSq45 where {
    repeats := 3
    maxSecondsPerCall := 60.0
    expectedHash := some (firstShortVectorHarshCubicNormSqHash 45)
  }

setup_fixed_benchmark runFirstShortVectorHarshCubicNormSq50 where {
    repeats := 3
    maxSecondsPerCall := 60.0
    expectedHash := some (firstShortVectorHarshCubicNormSqHash 50)
  }

setup_fixed_benchmark runIsabelleHarshCubicNormSq50 where {
    repeats := 3
    maxSecondsPerCall := 60.0
    expectedHash := some (firstShortVectorHarshCubicNormSqHash 50)
  }

setup_fixed_benchmark runFirstShortVectorHarshCubicNormSq55 where {
    repeats := 3
    maxSecondsPerCall := 60.0
    expectedHash := some (firstShortVectorHarshCubicNormSqHash 55)
  }

setup_fixed_benchmark runIsabelleHarshCubicNormSq55 where {
    repeats := 3
    maxSecondsPerCall := 60.0
    expectedHash := some (firstShortVectorHarshCubicNormSqHash 55)
  }

end Hex.LLLBench

def main (args : List String) : IO UInt32 :=
  LeanBench.Cli.dispatch args
