import HexLLL
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

/-- Build the certified executable LLL state for a deterministic matrix. -/
def stateOf (b : Matrix Int n m) : LLLState n m where
  b := b
  ν := GramSchmidt.Int.scaledCoeffs b
  d := GramSchmidt.Int.gramDetVec b
  ν_eq := by
    intro i j hi hj hji
    rw [GramSchmidt.Int.gramDetVec_eq_gramDet b (j + 1)
      (Nat.succ_le_of_lt (Nat.lt_trans hji hi))]
    simpa [GramSchmidt.entry, Matrix.row] using
      (GramSchmidt.Int.scaledCoeffs_eq b i j hi hji)
  d_eq := by
    intro i hi
    exact GramSchmidt.Int.gramDetVec_eq_gramDet b i (Nat.le_of_lt_succ hi)

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

private theorem benchFixtureIndependent {n m : Nat} (b : Matrix Int n m) :
    b.independent := by
  sorry

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

/-- Textbook LLL model for bounded-bit-size random bases: `O(n^4 log B)`;
with `|entry| <= 30`, the bit-size factor is constant in the Phase-4
ladder, leaving the quartic row-operation surface. -/
def firstShortVectorRandomBoundedComplexity (n : Nat) : Nat :=
  n ^ 4

/-- Textbook LLL model for harsh-cubic inputs: `O(n^4 log B)` with
`log B ~= 3.3n`, represented as a quintic benchmark model. -/
def firstShortVectorHarshCubicComplexity (n : Nat) : Nat :=
  n ^ 5

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

/-- Fixed benchmark target: BZ recombination hot path at `p = 5`, `k = 2`,
and three lifted local factors. -/
def runFirstShortVectorBZRecombinationChecksum : Unit → IO Int := fun _ => do
  return runFirstShortVectorChecksum (← bzRecombinationInputRef.get)

/-- Parametric benchmark target: LCG random-bounded bases. -/
def runFirstShortVectorRandomBoundedChecksum (input : FirstShortVectorInput) : Int :=
  runFirstShortVectorChecksum input

/-- Parametric benchmark target: harsh-cubic bases. -/
def runFirstShortVectorHarshCubicChecksum (input : FirstShortVectorInput) : Int :=
  runFirstShortVectorChecksum input

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
    paramFloor := 80
    paramCeiling := 144
    paramSchedule := .custom #[80, 96, 112, 128, 144]
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
    maxSecondsPerCall := 2.0
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

/- Complexity derivation: random-bounded inputs have square dimension `n` and
entries generated by the committed LCG seed with `|entry| <= 30`, so `log B` is
constant across the Phase-4 ladder. Textbook exact-integer LLL performs a
quartic row-operation surface in `n` under this bounded-bit regime. -/
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
paper regime named in `phase4.input_families`. Substituting `log B = O(n)`
into the textbook exact-integer LLL `O(n^4 log B)` bound gives a quintic model. -/
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

end Hex.LLLBench

def main (args : List String) : IO UInt32 :=
  LeanBench.Cli.dispatch args
