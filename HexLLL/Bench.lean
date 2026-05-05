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
