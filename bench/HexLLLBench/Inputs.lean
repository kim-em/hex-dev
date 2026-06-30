/-
Copyright (c) 2026 Lean FRO, LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Kim Morrison
-/

module

public import HexLLL
public import LeanBench

public section

namespace Hex.LLLBench

open Hex.Internal

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
    let B := (sReduced.ν.getRow f1).get f0
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
    (((input.state.ν.getRow input.k).get input.j : Int) : Rat) /
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
  -- back to native. The verify target must fail iff the certified path does.
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
  Vector.normSq
    (lll.firstShortVectorUnchecked input.basis (3 / 4)
      lllDeltaLower lllDeltaUpper input.hn)

/-- Benchmark comparator observable for the exact `d`/`ν` reducer: squared norm
of the first vector of `lllNative` run directly. This is the
fplll-independent exact integer reducer that the steered path demotes to its
certification fallback; measuring it directly keeps the exact-native curve of
the comparator plot independent of the steered default. -/
def runNativeFirstShortVectorNormSq (input : FirstShortVectorInput) : Int :=
  Vector.normSq
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
once on every rung of both ladders, then read `Hex.Internal.checkerTally`. Fails if
any interval pass reached indecision (`exactFallback ≠ 0`); the
size-predictor split between interval-accepted and exact-primary is pinned
by the expected hash. The returned value encodes the tally as
`(interval · 65537 + exactPrimary) · 65537 + exactFallback`. -/
def runCertifiedCheckerIntervalTally : Unit → IO Int := fun _ => do
  Hex.Internal.resetCheckerTally
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
  let tally ← Hex.Internal.checkerTally
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

end Hex.LLLBench
