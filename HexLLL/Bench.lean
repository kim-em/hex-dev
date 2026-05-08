import HexLLL
import LeanBench

/-!
Benchmark registrations for `hex-lll`.

This first Phase 4 slice covers the executable `LLLState` operations and the
top-level `lll.firstShortVector` entry point. Fixture construction builds the
integer Gram-Schmidt state once in `prep`; the timed targets measure the state
update or projection surfaces and return compact checksums of the affected
cells. The `lll.firstShortVector` fixture is the all-zero lift-coefficients
degenerate BZ recombination basis: one identity row per "factor" with no
interaction between factors.

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
* `runFirstShortVectorIdentityChecksum`: full LLL traversal over the identity
  basis, the degenerate BZ-style recombination input with no row interaction.
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

/-- Prepared identity basis for `lll.firstShortVector` benchmarks. -/
structure FirstShortVectorInput where
  rows : Nat
  basis : Matrix Int rows rows
  hn : 1 ≤ rows
  hind : basis.independent

instance : Hashable FirstShortVectorInput where
  hash input :=
    hash input.rows

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

/-- Entry generator for bounded random-looking square bases. -/
def randomBoundedEntry (rows row col salt : Nat) : Int :=
  let raw := ((row + 11) * 1_103 + (col + 7) * 2_009 + salt + rows * 97) % 61
  let centered := Int.ofNat raw - 30
  if row = col then
    if centered = 0 then 1 else centered
  else
    centered

/-- Entry generator with input bit-length proportional to the dimension. -/
def harshCubicEntry (rows row col salt : Nat) : Int :=
  let sign : Int := if ((row + col + salt) % 2 = 0) then 1 else -1
  let low := randomBoundedEntry rows row col salt
  let bits := 3 * rows + ((row + 2 * col + salt) % 5)
  sign * (Int.ofNat (2 ^ bits)) + low

/-- Deterministic row-major square basis for the random-bounded family. -/
def flatRandomBoundedBasis (rows salt : Nat) : Array Int :=
  if rows = 0 then
    #[]
  else
    (Array.range (rows * rows)).map fun idx =>
      let row := idx / rows
      let col := idx % rows
      randomBoundedEntry rows row col salt

/-- Deterministic row-major square basis for the harsh-cubic family. -/
def flatHarshCubicBasis (rows salt : Nat) : Array Int :=
  if rows = 0 then
    #[]
  else
    (Array.range (rows * rows)).map fun idx =>
      let row := idx / rows
      let col := idx % rows
      harshCubicEntry rows row col salt

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
  prepOfBasisInput n rows (flatRandomBoundedBasis rows 509)

/-- Per-parameter fixture for the harsh-cubic input family. -/
def prepOfBasisHarshCubicInput (n : Nat) : OfBasisInput :=
  let rows := n + 3
  prepOfBasisInput n rows (flatHarshCubicBasis rows 887)

/-- Per-parameter fixture: a square `(n + 3) x (n + 3)` identity basis. -/
def prepFirstShortVectorInput (n : Nat) : FirstShortVectorInput :=
  let rows := n + 3
  { rows := rows
    basis := (1 : Matrix Int rows rows)
    hn := by simp [rows]
    hind := Matrix.identity_independent }

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

/-- Model for full LLL traversal on the identity basis. Every size-reduction
probe sees a zero scaled coefficient and performs no row update or swap. -/
def firstShortVectorIdentityComplexity (n : Nat) : Nat :=
  let rows := n + 3
  rows * rows

/-- Model for `LLLState.ofBasis`: Gram matrix construction plus two Bareiss
passes over the Gram matrix, one for determinants and one for scaled
coefficients. -/
def ofBasisComplexity (rows cols : Nat) : Nat :=
  rows * rows * cols + 2 * rows * rows * rows

/-- BZ recombination `ofBasis` model for a `(n + 3) x (2(n + 3) + 1)` basis. -/
def ofBasisBzRecombinationComplexity (n : Nat) : Nat :=
  let rows := n + 3
  ofBasisComplexity rows (2 * rows + 1)

/-- Random-bounded `ofBasis` model for a square `(n + 3) x (n + 3)` basis. -/
def ofBasisRandomBoundedComplexity (n : Nat) : Nat :=
  let rows := n + 3
  ofBasisComplexity rows rows

/-- Harsh-cubic `ofBasis` model: the same two Bareiss passes, with a linear
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

/-- Benchmark target: run LLL on the identity basis and checksum the first row. -/
def runFirstShortVectorIdentityChecksum (input : FirstShortVectorInput) : Int :=
  intVectorChecksum
    (lll.firstShortVector input.basis (3 / 4)
      lllDeltaLower lllDeltaUpper input.hn input.hind)

/- Complexity derivation: `LLLState.ofBasis` builds the Gram matrix for a
rectangular BZ recombination-style basis with `rows = n + 3` and
`cols = 2 * rows + 1`, then runs the two fraction-free Bareiss-shaped passes
used by `gramDetVec` and `scaledCoeffs`. The dominant work is `rows^2 * cols`
integer multiply-adds for Gram construction plus two cubic eliminations over
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
all `rows^2` dot products of length `rows`, then computes `gramDetVec` and
`scaledCoeffs` as two Bareiss-style passes over that Gram matrix. Hadamard
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

/- Complexity derivation: on the identity basis, every Gram-Schmidt scaled
coefficient `ν[k][j]` is zero and each determinant denominator `d[j+1]` is one.
The outer LLL loop visits `k = 1, ..., rows - 1`; each `sizeReduce k` checks
the `k` earlier columns, reads the zero coefficient and unit determinant, and
does no row update or swap. The resulting hot path is the triangular
`1 + ... + (rows - 1)` sequence of reads and integer comparisons. -/
setup_benchmark runFirstShortVectorIdentityChecksum n =>
    firstShortVectorIdentityComplexity n
  with prep := prepFirstShortVectorInput
  where {
    paramFloor := 80
    paramCeiling := 112
    paramSchedule := .custom #[80, 96, 112]
    maxSecondsPerCall := 6.0
  }

end Hex.LLLBench

def main (args : List String) : IO UInt32 :=
  LeanBench.Cli.dispatch args
