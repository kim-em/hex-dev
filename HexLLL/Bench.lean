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
  rectangular BZ-style recombination basis.
* `runOfBasisRandomBoundedChecksum`: build the initial integer state for a
  bounded-coefficient square basis.
* `runOfBasisHarshCubicChecksum`: build the initial integer state for a
  square basis whose entry bit-length grows linearly in the dimension.
* `runSizeReduceColumnChecksum`: one targeted column reduction against the
  previous row of a prepared `(n + 3) x (2(n + 3) + 1)` state.
* `runSizeReduceChecksum`: full reduction of the final prepared row.
* `runSwapStepChecksum`: one adjacent swap at the final prepared row.
* `runGramSchmidtCoeffChecksum`: rational coefficient recovery from stored
  integer `ν` and `d`.
* `runPotential`: prefix product of the stored Gram determinants.
* `runFirstShortVectorBZRecombinationChecksum`: fixed BZ-shaped recombination
  basis for `p = 5`, `k = 2`, and three lifted local factors.
* `runFirstShortVectorRandomBoundedChecksum`: random-bounded integer bases
  with `|entry| <= 30` at `n in {30, 60, 120, 240}`.
* `runFirstShortVectorHarshCubicChecksum`: harsh-cubic bases with entry
  bit-length approximately `3.3 * n` at `n in {15, 30, 45}`.

Informational external comparator:

* `fpLLL via fpylll`: process-call registrations shell out to
  `scripts/oracle/lll_fpylll.py --bench-checksum`, which uses
  `fpylll.LLL.reduction` with `delta = 0.75` (matching Lean's `δ = 3/4`).
  The comparator is classified informational in `SPEC/Libraries/hex-lll.md`
  because fpLLL's floating-point Gram-Schmidt implementation
  (Nguyen-Stehle; fpylll 0.6 or newer supported by the existing oracle
  driver) bypasses the exact-integer operand-size drift paid by this verified
  implementation. Ratios are recorded for orientation but do not gate Phase 4.

External comparator:

* `verified Isabelle LLL (AFP LLL_Basis_Reduction; Haskell extraction from
  Zenodo record 2636367, https://zenodo.org/records/2636367, archive SHA-256
  `5c975aeb2033540b8f9a05d2ffac87dca0f258e887a5807edefbe60178a547e0`)` is
  registered as the Phase-4 gating comparator for the bottom/shared
  `phase4.input_families` rungs. `scripts/oracle/setup_lll_isabelle.sh`
  downloads, verifies, caches, and builds `svp_verified`; set
  `HEX_LLL_ISABELLE_SVP` to an already-built binary to avoid setup in the
  first measured call.
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
  if row = col then centered + Int.ofNat (rows + 3) else centered

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

/-- Fixture independence witness for Phase-4 benchmark bases.

The benchmark target measures the executable construction of the `ν` and `d`
fields; the independence proof is erased and `LLLState.ofBasis` does not
inspect it at runtime. Non-identity fixture independence is discharged with the
LLL proof work rather than in this bench module. -/
private theorem benchFixtureIndependent {n m : Nat} (b : Matrix Int n m) :
    b.independent := by
  sorry

/-- Build the certified executable LLL state for a deterministic matrix. -/
def stateOf (b : Matrix Int n m) : LLLState n m :=
  LLLState.ofBasis b (benchFixtureIndependent b)

/-- Per-parameter fixture: a prepared `(n + 3) x (2(n + 3) + 1)` LLL state. -/
def prepStateInput (n : Nat) : StateInput :=
  let rows := n + 3
  let cols := 2 * rows + 1
  let flat : IntBasisInput :=
    { rows := rows
      cols := cols
      entries := flatBasis rows cols 197 }
  let j : Fin rows := ⟨n + 1, by simp [rows]⟩
  let k : Fin rows := ⟨n + 2, by simp [rows]⟩
  { rows := rows
    cols := cols
    state := stateOf (matrixOfFlat flat)
    j := j
    k := k
    hjk := by
      change n + 1 < n + 2
      omega }

/-! ## Phase-4 `lll.firstShortVector` input families. -/

/-- BZ recombination coefficient block from
`HexLLL/EmitFixtures.lean`: `p = 5`, `k = 2`, `coeffWidth = 4`, and
factors `[X + 1, X + 2, X + 3]`. -/
def bzRecombinationCoeff (factor col : Nat) : Int :=
  match factor, col with
  | 0, 0 => 1
  | 0, 1 => 1
  | 1, 0 => 2
  | 1, 1 => 1
  | 2, 0 => 3
  | 2, 1 => 1
  | _, _ => 0

/-- BZ recombination basis with a `p^k = 25` diagonal indicator block. -/
def bzRecombinationBasis : Matrix Int 3 7 :=
  Matrix.ofFn fun i j =>
    if j.val < 4 then
      bzRecombinationCoeff i.val j.val
    else if j.val - 4 = i.val then
      (25 : Int)
    else
      0

/-- Fixed BZ recombination input. -/
def bzRecombinationInput : FirstShortVectorInput :=
  { rows := 3
    cols := 7
    basis := bzRecombinationBasis
    hn := by decide
    hind := benchFixtureIndependent bzRecombinationBasis }

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

/-- LCG-generated random-bounded basis, `|entry| <= 30`. -/
def randomBoundedBasis (n seed : Nat) : Matrix Int n n :=
  Matrix.ofFn fun i j =>
    randomBoundedEntry (lcgIterate seed (i.val * n + j.val + 1))

/-- Committed seed for the random-bounded family. The `#guard` below checks
that after size-reducing row 1 against row 0, the first Lovasz comparison
fails, so the next LLL outer-loop step performs a swap. -/
def randomBoundedSwapSeed : Nat := 8

/-- Parametric random-bounded input family at `n in {30, 60, 120, 240}`. -/
def prepRandomBoundedInput (n : Nat) : FirstShortVectorInput :=
  let rows := max n 1
  let basis := randomBoundedBasis rows randomBoundedSwapSeed
  { rows := rows
    cols := rows
    basis := basis
    hn := by
      exact Nat.le_max_right n 1
    hind := benchFixtureIndependent basis }

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
    if i = j then
      scale + noise
    else if j.val < i.val then
      scale / 3 + noise
    else
      noise

/-- Parametric harsh-cubic input family at `n in {15, 30, 45}`. -/
def prepHarshCubicInput (n : Nat) : FirstShortVectorInput :=
  let rows := max n 1
  let basis := harshCubicBasis rows
  { rows := rows
    cols := rows
    basis := basis
    hn := by
      exact Nat.le_max_right n 1
    hind := benchFixtureIndependent basis }

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

initialize randomBoundedInput60Ref : IO.Ref (Option FirstShortVectorInput) ←
  IO.mkRef none

initialize randomBoundedInput120Ref : IO.Ref (Option FirstShortVectorInput) ←
  IO.mkRef none

initialize randomBoundedInput240Ref : IO.Ref (Option FirstShortVectorInput) ←
  IO.mkRef none

initialize harshCubicInput15Ref : IO.Ref (Option FirstShortVectorInput) ←
  IO.mkRef none

initialize harshCubicInput30Ref : IO.Ref (Option FirstShortVectorInput) ←
  IO.mkRef none

initialize harshCubicInput45Ref : IO.Ref (Option FirstShortVectorInput) ←
  IO.mkRef none

/-! ## Phase-4 `LLLState.ofBasis` input families. -/

/-- Entry generator for bounded random-looking square bases. -/
def ofBasisRandomBoundedEntry (rows row col salt : Nat) : Int :=
  let raw := ((row + 11) * 1_103 + (col + 7) * 2_009 + salt + rows * 97) % 61
  let centered := Int.ofNat raw - 30
  if row = col then
    if centered = 0 then 1 else centered
  else
    centered

/-- Entry generator with input bit-length proportional to the dimension. -/
def ofBasisHarshCubicEntry (rows row col salt : Nat) : Int :=
  let sign : Int := if ((row + col + salt) % 2 = 0) then 1 else -1
  let low := ofBasisRandomBoundedEntry rows row col salt
  let bits := 3 * rows + ((row + 2 * col + salt) % 5)
  sign * (Int.ofNat (2 ^ bits)) + low

/-- Deterministic row-major square basis for the random-bounded family. -/
def flatOfBasisRandomBoundedBasis (rows salt : Nat) : Array Int :=
  if rows = 0 then
    #[]
  else
    (Array.range (rows * rows)).map fun idx =>
      let row := idx / rows
      let col := idx % rows
      ofBasisRandomBoundedEntry rows row col salt

/-- Deterministic row-major square basis for the harsh-cubic family. -/
def flatOfBasisHarshCubicBasis (rows salt : Nat) : Array Int :=
  if rows = 0 then
    #[]
  else
    (Array.range (rows * rows)).map fun idx =>
      let row := idx / rows
      let col := idx % rows
      ofBasisHarshCubicEntry rows row col salt

/-- General constructor for an `LLLState.ofBasis` benchmark fixture.
The benchmark parameter maps to `rows = n + 3`, so the final two row indices
are always available for the result checksum. -/
def prepOfBasisInput (n cols : Nat) (entries : Array Int) : OfBasisInput :=
  let rows := n + 3
  let flat : IntBasisInput :=
    { rows := rows
      cols := cols
      entries := entries }
  let j : Fin rows := ⟨n + 1, by simp [rows]⟩
  let k : Fin rows := ⟨n + 2, by simp [rows]⟩
  let basis := matrixOfFlat flat
  { rows := rows
    cols := cols
    basis := basis
    hind := benchFixtureIndependent basis
    j := j
    k := k
    hjk := by
      change n + 1 < n + 2
      omega }

/-- Per-parameter fixture for the BZ recombination input family. -/
def prepOfBasisBzRecombinationInput (n : Nat) : OfBasisInput :=
  let rows := n + 3
  let cols := 2 * rows + 1
  prepOfBasisInput n cols (flatBasis rows cols 311)

/-- Per-parameter fixture for the random-bounded input family. -/
def prepOfBasisRandomBoundedInput (n : Nat) : OfBasisInput :=
  let rows := n + 3
  prepOfBasisInput n rows (flatOfBasisRandomBoundedBasis rows 509)

/-- Per-parameter fixture for the harsh-cubic input family. -/
def prepOfBasisHarshCubicInput (n : Nat) : OfBasisInput :=
  let rows := n + 3
  prepOfBasisInput n rows (flatOfBasisHarshCubicBasis rows 887)

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
over `m = 2(n + 3) + 1` columns plus the affected coefficient prefix. -/
def sizeReduceColumnComplexity (n : Nat) : Nat :=
  (2 * (n + 3) + 1) + n + 3

/-- Model for reducing the final row against all earlier rows: `k` row updates
over `m` columns plus the triangular coefficient-prefix updates. -/
def sizeReduceComplexity (n : Nat) : Nat :=
  let rows := n + 3
  rows * (2 * rows + 1) + rows * rows

/-- Model for an adjacent swap update: one basis swap over `m` columns, one
determinant write, and linear coefficient updates in the affected rows/columns. -/
def swapStepComplexity (n : Nat) : Nat :=
  (2 * (n + 3) + 1) + n + 3

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

/-- BZ recombination `ofBasis` model for a `(n + 3) x (2(n + 3) + 1)` basis. -/
def ofBasisBzRecombinationComplexity (n : Nat) : Nat :=
  let rows := n + 3
  ofBasisComplexity rows (2 * rows + 1)

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

/-- Whitespace matrix format consumed by
`scripts/oracle/lll_fpylll.py --bench-checksum`. -/
def firstShortVectorMatrixInput (input : FirstShortVectorInput) : String :=
  let entries :=
    (List.finRange input.rows).flatMap fun i =>
      (List.finRange input.cols).map fun j =>
        toString ((input.basis.row i)[j])
  s!"{input.rows} {input.cols}\n" ++ String.intercalate " " entries ++ "\n"

/-- Invoke fpylll on one prepared basis and parse the first-row checksum. -/
def runFpylllFirstShortVectorChecksum (input : FirstShortVectorInput) : IO Int := do
  let stdout ← IO.Process.runCmdWithInput "python3"
    #["scripts/oracle/lll_fpylll.py", "--bench-checksum"]
    (firstShortVectorMatrixInput input)
  let text := stdout.trimAscii.toString
  match text.toInt? with
  | some checksum => pure checksum
  | none => throw <| IO.userError s!"fpylll checksum was not an integer: {text}"

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

def ensureIsabelleInputDir : IO Unit := do
  discard <| checkedProcessOutput "mkdir" #["-p", ".cache/oracles/lll-isabelle/bench-inputs"]

def parseIsabelleNormSq (text : String) : IO Int := do
  match text.trimAscii.toString.toNat? with
  | some n => return Int.ofNat n
  | none => throw <| IO.userError s!"svp_verified emitted non-numeric output: {text}"

def runIsabelleShortVectorNormSq (tag : String) (input : FirstShortVectorInput) : IO Int := do
  let binary ← resolveIsabelleBinary
  ensureIsabelleInputDir
  let path := ".cache/oracles/lll-isabelle/bench-inputs/" ++ tag ++ ".txt"
  IO.FS.writeFile path (matrixHaskell input.basis)
  parseIsabelleNormSq (← checkedProcessOutput binary #[path])

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

def runFirstShortVectorRandomBoundedNormSq60 : Unit → IO Int := fun _ => do
  return runFirstShortVectorNormSq
    (← getCachedInput randomBoundedInput60Ref (fun _ => prepRandomBoundedInput 60))

def runIsabelleRandomBoundedNormSq60 : Unit → IO Int := fun _ => do
  runIsabelleShortVectorNormSq "random-bounded-60"
    (← getCachedInput randomBoundedInput60Ref (fun _ => prepRandomBoundedInput 60))

def runFirstShortVectorRandomBoundedNormSq120 : Unit → IO Int := fun _ => do
  return runFirstShortVectorNormSq
    (← getCachedInput randomBoundedInput120Ref (fun _ => prepRandomBoundedInput 120))

def runIsabelleRandomBoundedNormSq120 : Unit → IO Int := fun _ => do
  runIsabelleShortVectorNormSq "random-bounded-120"
    (← getCachedInput randomBoundedInput120Ref (fun _ => prepRandomBoundedInput 120))

def runFirstShortVectorRandomBoundedNormSq240 : Unit → IO Int := fun _ => do
  return runFirstShortVectorNormSq
    (← getCachedInput randomBoundedInput240Ref (fun _ => prepRandomBoundedInput 240))

def runIsabelleRandomBoundedNormSq240 : Unit → IO Int := fun _ => do
  runIsabelleShortVectorNormSq "random-bounded-240"
    (← getCachedInput randomBoundedInput240Ref (fun _ => prepRandomBoundedInput 240))

def runFirstShortVectorHarshCubicNormSq15 : Unit → IO Int := fun _ => do
  return runFirstShortVectorNormSq
    (← getCachedInput harshCubicInput15Ref (fun _ => prepHarshCubicInput 15))

def runIsabelleHarshCubicNormSq15 : Unit → IO Int := fun _ => do
  runIsabelleShortVectorNormSq "harsh-cubic-15"
    (← getCachedInput harshCubicInput15Ref (fun _ => prepHarshCubicInput 15))

def runFirstShortVectorHarshCubicNormSq30 : Unit → IO Int := fun _ => do
  return runFirstShortVectorNormSq
    (← getCachedInput harshCubicInput30Ref (fun _ => prepHarshCubicInput 30))

def runIsabelleHarshCubicNormSq30 : Unit → IO Int := fun _ => do
  runIsabelleShortVectorNormSq "harsh-cubic-30"
    (← getCachedInput harshCubicInput30Ref (fun _ => prepHarshCubicInput 30))

def runFirstShortVectorHarshCubicNormSq45 : Unit → IO Int := fun _ => do
  return runFirstShortVectorNormSq
    (← getCachedInput harshCubicInput45Ref (fun _ => prepHarshCubicInput 45))

def runIsabelleHarshCubicNormSq45 : Unit → IO Int := fun _ => do
  runIsabelleShortVectorNormSq "harsh-cubic-45"
    (← getCachedInput harshCubicInput45Ref (fun _ => prepHarshCubicInput 45))

/-- Parametric benchmark target: LCG random-bounded bases. -/
def runFirstShortVectorRandomBoundedChecksum (input : FirstShortVectorInput) : Int :=
  runFirstShortVectorChecksum input

/-- Parametric benchmark target: harsh-cubic bases. -/
def runFirstShortVectorHarshCubicChecksum (input : FirstShortVectorInput) : Int :=
  runFirstShortVectorChecksum input

/- Complexity derivation: `LLLState.ofBasis` builds the Gram matrix for a
rectangular BZ recombination-style basis with `rows = n + 3` and
`cols = 2 * rows + 1`, then runs the shared fraction-free Bareiss-shaped pass
used by `GramSchmidt.Int.data`. The dominant work is `rows^2 * cols`
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

/- Fixed Phase-4 family: BZ recombination basis with `p = 5`, `k = 2`,
`coeffWidth = 4`, and three lifted local factors, matching the conformance
fixture in `HexLLL/EmitFixtures.lean`. This fixed target records the downstream
hot path inherited from Berlekamp-Zassenhaus recombination. -/
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
    maxSecondsPerCall := 6.0
    expectedHash := some 0x3c0064007a0036
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
    expectedHash := some 0xf977db3a0120001a
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
    expectedHash := some 0x949fde47fa1fffb4
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
    paramCeiling := 240
    paramSchedule := .custom #[30, 60, 120, 240]
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
    paramCeiling := 45
    paramSchedule := .custom #[15, 30, 45]
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
    expectedHash := some 0x3a52
  }

setup_fixed_benchmark runIsabelleRandomBoundedNormSq30 where {
    repeats := 3
    maxSecondsPerCall := 20.0
    expectedHash := some 0x3a52
  }

setup_fixed_benchmark runFirstShortVectorRandomBoundedNormSq60 where {
    repeats := 3
    maxSecondsPerCall := 30.0
    expectedHash := some 0x98cc
  }

setup_fixed_benchmark runIsabelleRandomBoundedNormSq60 where {
    repeats := 3
    maxSecondsPerCall := 30.0
    expectedHash := some 0x98cc
  }

setup_fixed_benchmark runFirstShortVectorRandomBoundedNormSq120 where {
    repeats := 3
    maxSecondsPerCall := 60.0
    expectedHash := some 0x11860
  }

setup_fixed_benchmark runIsabelleRandomBoundedNormSq120 where {
    repeats := 3
    maxSecondsPerCall := 60.0
    expectedHash := some 0x11860
  }

setup_fixed_benchmark runFirstShortVectorRandomBoundedNormSq240 where {
    repeats := 3
    maxSecondsPerCall := 120.0
    expectedHash := some 0x2454a
  }

setup_fixed_benchmark runIsabelleRandomBoundedNormSq240 where {
    repeats := 3
    maxSecondsPerCall := 120.0
    expectedHash := some 0x2454a
  }

setup_fixed_benchmark runFirstShortVectorHarshCubicNormSq15 where {
    repeats := 3
    maxSecondsPerCall := 20.0
    expectedHash := some 0x700000000033a4
  }

setup_fixed_benchmark runIsabelleHarshCubicNormSq15 where {
    repeats := 3
    maxSecondsPerCall := 40.0
    expectedHash := some 0x700000000033a4
  }

setup_fixed_benchmark runFirstShortVectorHarshCubicNormSq30 where {
    repeats := 3
    maxSecondsPerCall := 40.0
    expectedHash := some 0x37cc
  }

setup_fixed_benchmark runIsabelleHarshCubicNormSq30 where {
    repeats := 3
    maxSecondsPerCall := 40.0
    expectedHash := some 0x37cc
  }

setup_fixed_benchmark runFirstShortVectorHarshCubicNormSq45 where {
    repeats := 3
    maxSecondsPerCall := 60.0
    expectedHash := some 0x6d1e
  }

setup_fixed_benchmark runIsabelleHarshCubicNormSq45 where {
    repeats := 3
    maxSecondsPerCall := 60.0
    expectedHash := some 0x6d1e
  }

end Hex.LLLBench

def main (args : List String) : IO UInt32 :=
  LeanBench.Cli.dispatch args
