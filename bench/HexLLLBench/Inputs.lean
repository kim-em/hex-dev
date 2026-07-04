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

/-- Matrix input for benchmarking `LLLState.ofBasis` itself. -/
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

/-- Prepared basis for `lllNative.firstShortVector` benchmarks. -/
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
  LLLState.ofBasis b

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

/-- Committed seed for the random-bounded family. -/
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

/-! ### Ajtai-style worst-case family (fplll `gen_trg` port)

This is the lower-triangular worst-case family that drives LLL toward its
`Θ(d² log B)` swap bound (Nguyen-Stehlé, *LLL on the Average*, ANTS-VII 2006).
It is a faithful port of fplll's `gen_trg` (`latticegen t <d> <alpha>`,
`fplll/nr/matrix.cpp`), not the (nonexistent in fplll 5.5.0) `gen_ajtai`:

  for each column `i`: `bits_i = floor((2d - i)^alpha)`, the diagonal
  `D_i` is uniform in `[2, 2^bits_i]`, and each below-diagonal entry in
  column `i` is uniform in `(-D_i/2, D_i/2)`; the upper triangle is zero.

Entry-for-entry equality with fplll is impossible (fplll draws from GMP's
generator; we draw from the committed POSIX LCG), so fidelity is structural:
same orientation, same `bits_i` diagonal bit-length profile, and the same
`|off| < D_i/2` envelope. `scripts/dev/validate_latticegen.py` checks this. -/

/-- Floor of the integer `k`-th root of `n` (largest `r` with `r^k ≤ n`),
by binary search over a bit-length-bounded window. Mathlib-free. -/
def natIRootGo (k n : Nat) : Nat → Nat → Nat → Nat
  | _,  lo, 0 => lo
  | hi, lo, fuel + 1 =>
      if hi ≤ lo then lo
      else
        let mid := (lo + hi + 1) / 2
        if mid ^ k ≤ n then natIRootGo k n hi mid fuel
        else natIRootGo k n (mid - 1) lo fuel

/-- `natIRoot k n = ⌊n^(1/k)⌋`. -/
def natIRoot (k n : Nat) : Nat :=
  if k = 0 then 0
  else
    let hi := 2 ^ (Nat.log2 (n + 1) / k + 1)
    natIRootGo k n hi 0 (Nat.log2 (n + 1) + 2)

/-- Diagonal bit-length `⌊(2d - i)^1.2⌋` (alpha = 6/5), matching fplll
`gen_trg`'s `(int)pow(2d - i, alpha)` to within floating-point rounding. -/
def ajtaiBits (d i : Nat) : Nat := natIRoot 5 ((2 * d - i) ^ 6)

/-- A `bits`-wide pseudo-random natural in `[0, 2^bits)`, built by
concatenating 31-bit LCG draws so the Ajtai-style entries can actually span
`~2^bits` (the project LCG alone only yields 31-bit values). -/
def wideRandom (seed bits : Nat) : Nat :=
  let chunks := (bits + 30) / 31
  let raw := (List.range chunks).foldl
    (fun acc k => acc * 2147483648 + lcgIterate seed (k + 1) % 2147483648) 0
  if bits = 0 then 0 else raw % (2 ^ bits)

/-- Committed seed for the Ajtai-style family. -/
def ajtaiSeed : Nat := 1000003

/-- Diagonal `D_i ∈ [2, 2^bits_i]` for column `i` (fplll `randm(2^bits−1)+2`). -/
def ajtaiDiag (d col : Nat) : Nat :=
  let bits := ajtaiBits d col
  wideRandom (ajtaiSeed + 1000003 * (col + 1)) bits % (2 ^ bits - 1) + 2

/-- Below-diagonal entry `(row, col)`, `row > col`: uniform in `(−D_col/2, D_col/2)`. -/
def ajtaiOff (d row col : Nat) : Int :=
  let bound := ajtaiDiag d col / 2
  let bits := ajtaiBits d col
  let mag := wideRandom (ajtaiSeed + 7919 * (col * d + row + 1)) bits % bound
  if lcgIterate (ajtaiSeed + 104729) (col * d + row + 1) % 2 = 1 then
    -Int.ofNat mag
  else
    Int.ofNat mag

/-- Lower-triangular Ajtai-style worst-case basis (fplll `gen_trg`, alpha 1.2). -/
def ajtaiBasis (d : Nat) : Matrix Int d d :=
  Matrix.ofFn fun i j =>
    if j.val > i.val then
      0
    else if i = j then
      Int.ofNat (ajtaiDiag d j.val)
    else
      ajtaiOff d i.val j.val

/-- Parametric Ajtai-style input family. The scientific ladder is calibrated so
verified Isabelle native stays under the ~10 s ceiling at its top rung. -/
def prepAjtaiInput (n : Nat) : FirstShortVectorInput :=
  let rows := max n 1
  let basis := ajtaiBasis rows
  { rows := rows
    cols := rows
    basis := basis
    hn := by
      exact Nat.le_max_right n 1 }

/-- The Ajtai-style diagonal bit-length profile `bits_i = ⌊(2d - i)^1.2⌋` is
strictly decreasing in `i`; this steep super-geometric profile is the
structural cause of the family's worst-case `Θ(d² log B)` swap count. -/
def ajtaiProfileSteep (d : Nat) : Bool :=
  (List.range (d - 1)).all fun i => ajtaiBits d (i + 1) < ajtaiBits d i

-- Structural evidence the family exercises the swap branch: the diagonal
-- profile is steeply decreasing (a plain comment, not a doc-comment, since
-- `#guard` is a command and cannot carry a docstring).
#guard ajtaiProfileSteep 8

/-! ### q-ary (LWE/SIS) family (fplll `gen_qary` port)

Faithful port of fplll's `gen_qary` (`latticegen q <d> <k> <b>`): the `d × d`
block matrix `[[I_{d-k}, H], [0, q·I_k]]` with `H` uniform mod `q` and
`q = 2^(b-1) + rand(b-1)` (fplll `gen_q`; not required prime for the `b` flag).
The unreduced basis is a step profile (a plateau at `q` over a plateau at `1`)
LLL must smooth into the characteristic Z-shape, concentrating swaps in the
transition band — a distinct stress from a triangular near-orthogonal basis. -/
def qarySeed : Nat := 2000003

/-- fplll `gen_q`: `q = 2^(b-1) + rand(b-1)`, a random `b`-bit modulus. -/
def qaryModulus (b : Nat) : Nat := 2 ^ (b - 1) + wideRandom qarySeed (b - 1)

/-- Modulus bit-length for the q-ary family. -/
def qaryBits : Nat := 30

/-- q-ary basis `[[I_{d-k}, H], [0, q·I_k]]`, `H` uniform mod `q`. -/
def qaryBasis (d k b : Nat) : Matrix Int d d :=
  let q := qaryModulus b
  Matrix.ofFn fun i j =>
    if i.val < d - k then
      if j.val < d - k then (if i = j then 1 else 0)
      else Int.ofNat (wideRandom (qarySeed + 1009 * (i.val * d + j.val + 1)) b % q)
    else
      if i = j then Int.ofNat q else 0

/-- Parametric q-ary input family (square `d × d`, `k = d / 2`). -/
def prepQaryInput (n : Nat) : FirstShortVectorInput :=
  let rows := max n 1
  { rows := rows
    cols := rows
    basis := qaryBasis rows (rows / 2) qaryBits
    hn := by exact Nat.le_max_right n 1 }

#guard qaryModulus 8 ≥ 128 && qaryModulus 8 < 256

/-! ### NTRU family (fplll `gen_ntrulike` port)

Faithful port of fplll's `gen_ntrulike` (`latticegen n <2d> <b>`): the `2d × 2d`
block matrix `[[I, Rot(h)], [0, q·I]]` where `Rot(h)` is the circulant of a
vector `h` uniform mod `q` with `h[0]` fixed so `h(1) ≡ 0 mod q`. The planted
dense structure plus the q-block give a profile distinct from the other
families. (latticegen's flavor uses a uniform `h`, not a genuine NTRU key.) -/
def ntruSeed : Nat := 3000017
def ntruBits : Nat := 30
def ntruModulus : Nat := 2 ^ (ntruBits - 1) + wideRandom ntruSeed (ntruBits - 1)

/-- `h[i]` (uniform mod q for `i ≥ 1`; `h[0] = (−Σ_{i≥1} h[i]) mod q`, so
`h(1) = Σ_i h[i] ≡ 0 mod q`). -/
def ntruH (d i : Nat) : Nat :=
  let q := ntruModulus
  if i = 0 then
    let s := (List.range (d - 1)).foldl
      (fun acc t => (acc + wideRandom (ntruSeed + 4001 * (t + 1)) ntruBits % q) % q) 0
    (q - s) % q
  else
    wideRandom (ntruSeed + 4001 * i) ntruBits % q

/-- NTRU-like basis `[[I, Rot(h)], [0, q·I]]` on `2d × 2d`. -/
def ntruBasis (d : Nat) : Matrix Int (2 * d) (2 * d) :=
  let q := ntruModulus
  Matrix.ofFn fun i j =>
    let r := i.val
    let c := j.val
    if r < d then
      if c < d then (if r = c then 1 else 0)
      else Int.ofNat (ntruH d ((c - r) % d))
    else
      if c < d then 0 else (if r = c then Int.ofNat q else 0)

/-- Parametric NTRU input family (dimension `2n`). -/
def prepNtruInput (n : Nat) : FirstShortVectorInput :=
  let d := max n 1
  { rows := 2 * d
    cols := 2 * d
    basis := ntruBasis d
    hn := by have h := Nat.le_max_right n 1; omega }

-- The planted property `h(1) ≡ 0 mod q` (the row sum of `Rot(h)` is `0 mod q`).
#guard (let q := ntruModulus; (List.range 4).foldl (fun a i => (a + ntruH 4 i) % q) 0 == 0)

/-! ### knapsack / integer-relation family (fplll `gen_intrel` port)

Faithful port of fplll's `gen_intrel` (`latticegen r <d> <b>`): the **rectangular**
`d × (d+1)` matrix whose row `i` is `[rand_b, e_{i+1}]` (a random `b`-bit weight
in column 0, then the `i`-th canonical unit vector). This is the only family with
`cols ≠ rows`, so it exercises the `m > n` Gram construction in `ofBasis`. -/
def knapsackSeed : Nat := 4000037

/-- Weight bit-length at dimension `n`, targeting density `d = n / b ≈ 0.9`. -/
def knapsackBits (n : Nat) : Nat := (n * 10) / 9 + 1

/-- Rectangular `d × (d+1)` integer-relation basis (fplll `gen_intrel`). -/
def knapsackBasis (d b : Nat) : Matrix Int d (d + 1) :=
  Matrix.ofFn fun i j =>
    if j.val = 0 then Int.ofNat (wideRandom (knapsackSeed + 5003 * (i.val + 1)) b)
    else if j.val = i.val + 1 then 1
    else 0

/-- Parametric knapsack input family (rectangular `n × (n+1)`). -/
def prepKnapsackInput (n : Nat) : FirstShortVectorInput :=
  let rows := max n 1
  { rows := rows
    cols := rows + 1
    basis := knapsackBasis rows (knapsackBits rows)
    hn := by exact Nat.le_max_right n 1 }

-- density d = n/b ≈ 0.9 (b = ⌈10n/9⌉ + 1), and the basis is rectangular n×(n+1).
#guard knapsackBits 9 == 11

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

/-- General constructor for an `LLLState.ofBasis` benchmark fixture.
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
  let s := LLLState.ofBasis input.basis
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
    (lllNative.firstShortVector input.basis (3 / 4)
      lllDeltaLower lllDeltaUpper input.hn)

/-- Explicitly install the fpLLL provider for the bench process from the shared
library named by `HEX_FPLLL_FFI_LIB`, if that variable is set and non-empty.
Idempotent: once a provider is active this is a cheap no-op, so the provider
targets can call it lazily. This is the bench's opt-in replacement for the old
implicit env read — the public `Hex.lll` surface no longer consults the
environment; the bench does so explicitly here via `Hex.lll.loadProvider`. -/
def ensureProviderLoaded : IO Unit := do
  if ← lll.providerActive then
    return
  match ← IO.getEnv "HEX_FPLLL_FFI_LIB" with
  | some path => if path != "" then discard <| lll.loadProvider path
  | none => pure ()

/-- Benchmark target: run the public dispatched LLL path and checksum the
first row. If a real external provider is loaded, this target fails unless the
certified dispatch accepts at least one candidate. -/
def runDispatchedFirstShortVectorChecksum (input : FirstShortVectorInput) : IO Int := do
  ensureProviderLoaded
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
exact native path (`lllNative.firstShortVector`, i.e. `lllNative`). -/
def runFirstShortVectorNormSq (input : FirstShortVectorInput) : Int :=
  Vector.normSq
    (lllNative.firstShortVector input.basis (3 / 4)
      lllDeltaLower lllDeltaUpper input.hn)

/-- Benchmark comparator observable for the exact `d`/`ν` reducer: squared norm
of the first vector of `lllNative` run directly. This is the
fplll-independent exact integer reducer; measuring it directly gives the
exact-native curve of the comparator plot. -/
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
  ensureProviderLoaded
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
-- (the default `runFirstShortVector*NormSq` targets also run `lllNative`).
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
