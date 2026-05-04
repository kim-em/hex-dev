# hex-lll (LLL lattice basis reduction, depends on hex-gram-schmidt)

`hex-lll` is the recombination primitive used by
`hex-berlekamp-zassenhaus`: BZ encodes the lifted local factors of an
integer polynomial as a lattice basis, runs `lll`, and reads off
candidate `Z[x]` factors from the short vectors. The Phase 1 surface
must be self-contained — usable from BZ without any `sorry`-blocked
constructors — and must include a short-vector recovery entry point
described under "Short-vector recovery for downstream consumers"
below.

**Contents:**
- LLL algorithm using the d-representation (all integer arithmetic,
  no rationals stored; rational GS quantities as `noncomputable` projections)
- Size reduction (ensure |coeffs[i][j]| ≤ 1/2)
- Lovász condition check and basis swap
- A `LLLState.ofBasis` initial-state constructor whose proof
  obligations (`ν_eq`, `d_eq`) are discharged in this library, and a
  short-vector recovery entry point for BZ recombination

**Definitions:**
```lean
/-- v is in the integer lattice spanned by the rows of b. -/
def Matrix.memLattice (b : Matrix Int n m) (v : Vector Int m) : Prop :=
    ∃ c : Vector Int n, b.mulVec c = v

/-- The rows of b are linearly independent (all Gram determinants positive). -/
def Matrix.independent (b : Matrix Int n m) : Prop :=
    ∀ k : Fin n, 0 < det (b.gramMatrix.submatrix k)

/-- Squared L2 norm of an integer vector. -/
def Vector.normSq (v : Vector Int m) : Int := v.dotProduct v
```

`dotProduct`, `normSq`, and `gramMatrix` live in hex-matrix.
`memLattice`, `independent`, and `isLLLReduced` live in hex-lll.

**delta-LLL-reduced.** A basis b is delta-LLL-reduced (for
delta in (1/4, 1]) if it satisfies two conditions:

1. **Size-reduced:** |(coeffs b)[i][j]| <= 1/2 for all 0 <= j < i < n.

2. **Lovász condition:** For all 0 <= i < n-1:
       delta * ||(basis b)[i]||^2 <= ||(basis b)[i+1]||^2 + (coeffs b)[i+1][i]^2 * ||(basis b)[i]||^2

   Equivalently: (delta - (coeffs b)[i+1][i]^2) * ||(basis b)[i]||^2 <= ||(basis b)[i+1]||^2

**Key properties.** All theorems require
`hδ : 1/4 < δ`, `hδ' : δ ≤ 1`, `hn : 1 ≤ n`, and
`hli : b.independent`.

`δ > 1/4` so that `α = 1/(δ - 1/4)` is well-defined and positive.
`δ ≤ 1` for termination (the Lovász failure condition is strict, so
each swap gives `gramDet b' k < δ · gramDet b k ≤ gramDet b k`,
strictly decreasing the potential even at `δ = 1`). Linear
independence ensures all Gram determinants `gramDet b k > 0`, which
is needed for the GS orthogonalization to exist and for the
scaledCoeffs denominators to be nonzero.

```lean
theorem lll_same_lattice (b : Matrix Int n m) (δ : Rat) ... :
    (lll b δ ...).memLattice v ↔ b.memLattice v

theorem lll_reduced (b : Matrix Int n m) (δ : Rat) ... :
    isLLLReduced (lll b δ ...) δ

theorem lll_short_vector (b : Matrix Int n m) (δ : Rat)
    (hδ : 1/4 < δ) (hδ' : δ ≤ 1)
    (hn : 1 ≤ n) (hli : b.independent)
    (v : Vector Int m) :
    b.memLattice v → v ≠ 0 →
    (lll b δ hδ hδ' hn hli).row 0 |>.normSq ≤ α^(n-1) * v.normSq
  where α := 1 / (δ - 1/4)
```

The short vector guarantee with `δ = 3/4` gives `‖b₁‖ ≤ 2^{(n-1)/2} · λ₁`.

## LLLState and algorithm

The algorithm operates on a single integer state: basis vectors,
Gram determinants, and scaled GS coefficients. The rational GS
quantities (coeffs, basis norms) are never stored or computed at
runtime — they exist only as `noncomputable` projections for use
in proofs.

```lean
/-- LLL state. All fields are integers; no rationals stored. -/
structure LLLState (n m : Nat) where
  b : Matrix Int n m            -- basis vectors
  ν : Matrix Int n n            -- ν[i][j] = d[j+1] * coeffs[i][j] for j < i
  d : Vector Nat (n + 1)        -- Gram determinants d_0, ..., d_n
  ν_eq : ∀ i j, j < i → (ν[i][j] : Rat) = (d[j + 1] : Rat) * (GramSchmidt.Int.coeffs b)[i][j]
  d_eq : ∀ i, d[i] = GramSchmidt.Int.gramDet b i ‹_›

/-- Recover a single rational GS coefficient from the integer state.
    Marked noncomputable: exists only for the proof layer. -/
noncomputable def LLLState.gramSchmidtCoeff (s : LLLState n m) (i j : Nat) : Rat :=
  (s.ν[i][j] : Rat) / (s.d[j + 1] : Rat)

-- Use https://github.com/leanprover/lean4/pull/13200 when available.
def LLLState.potential (s : LLLState n m) : Nat :=
  s.d[1:n].foldl (· * ·) 1    -- d_1 * d_2 * ... * d_{n-1}
```

The signatures shown for `sizeReduce` and `swapStep` below are the
required types; the body must implement the algorithm described in
the prose that follows each block.

**Size reduction.** Size-reduce b[k] against b[k-1], ..., b[0].
Updates b and ν; d is unchanged (basis is unchanged by size
reduction).

```lean
def LLLState.sizeReduce (s : LLLState n m) (k : Nat) : LLLState n m
```

For j = k-1 downto 0: if 2 * |ν[k][j]| > d[j+1] (i.e., |coeffs[k][j]| > 1/2):

    r := Int.fdiv (2 * ν[k][j] + d[j+1]) (2 * d[j+1])
    b[k] := b[k] - r * b[j]
    ν[k][l] := ν[k][l] - r * ν[j][l]    for l < j
    ν[k][j] := ν[k][j] - r * d[j+1]

These are pointwise updates: only ν cells in row k change, only d[j+1]
is read, and d itself is unchanged. Implementations must do targeted
writes — `O(k)` cells per j-step, `O(k^2)` per `sizeReduce` call.
Rebuilding the full ν matrix via `Matrix.ofFn` (or any equivalent that
allocates a fresh n × n matrix per step) is forbidden — that turns
size reduction into `O(n^3)` per column and the overall algorithm
into `O(n^5 · log B)`.

**Swap step.** Swap b[k] and b[k-1], updating ν and d.

```lean
def LLLState.swapStep (s : LLLState n m) (k : Nat) : LLLState n m
```

Let B = ν[k][k-1]. After swapping b[k] and b[k-1]:

*d update:*

    d[k]' = (d[k+1] * d[k-1] + B^2) / d[k]

This division is exact (see integrality section below). All other
d[i] are unchanged.

*ν updates* (Cohen Algorithm 2.6.3, 0-indexed):

ν[k][k-1]' = B (unchanged: (scaledCoeffs b')[k][k-1] = (scaledCoeffs b)[k][k-1]).

For j < k-1: ν[k-1][j] and ν[k][j] simply swap.

For i > k, the two affected columns update simultaneously:

    ν[i][k-1]' = (d[k-1] * ν[i][k] + B * ν[i][k-1]) / d[k]
    ν[i][k]'   = (d[k+1] * ν[i][k-1] - B * ν[i][k]) / d[k]

(Derivation: ν[i][k-1]' = d[k]' * coeffs(b')[i][k-1] and
d[k]' / ‖basis(b')[k-1]‖² = d[k-1], so the d[k-1] factor in the prev
update absorbs the d[k]' coming from the scaledCoeffs definition.
Similarly d[k+1] = d[k+1]' appears in the curr update because
‖basis(b')[k]‖² = d[k] · d[k+1] / (d[k-1]·d[k+1] + B²) and d[k]·d[k-1]
combine through the gramDet identity.) All divisions are exact (see
integrality section below). Only d[k] changes among d-values, and
only ν values with one index equal to k or k-1 change.

These are pointwise updates: targeted writes only. Rebuilding the full
ν matrix or d vector via `Matrix.ofFn` / `Vector.ofFn` per swap is
forbidden — that turns a per-swap `O(n)` update into `O(n^2)` and adds
a factor of `n` to the overall LLL cost.

**Main loop.** The Lovász condition in integer form (see integrality
section below for derivation) is:

    d[k+1] * d[k-1] + ν[k][k-1]^2 >= δ * d[k]^2

For δ = p/q rational, this becomes a comparison of integers (no
division): `q * (d[k+1] * d[k-1] + ν[k][k-1]^2) >= p * d[k]^2`.

```lean
def lllAux (s : LLLState n m) (k : Nat) (δ : Rat)
    (hδ : 1/4 < δ) (hδ' : δ ≤ 1) (hind : s.b.independent)
    (hk : 1 ≤ k) (hkn : k ≤ n) : Matrix Int n m :=
  if h : k = n then s.b
  else
    let s := s.sizeReduce k
    -- Check Lovász condition (integer arithmetic, no division):
    if δ.den * (s.d[k+1] * s.d[k-1] + s.ν[k][k-1]^2) ≥ δ.num * s.d[k]^2 then
      -- Lovász holds: advance
      lllAux s (k + 1) δ hδ hδ' ‹_› (by omega) (by omega)
    else
      -- Lovász fails: swap and decrement
      let s := s.swapStep k
      lllAux s (max (k - 1) 1) δ hδ hδ' ‹_› (by omega) (by omega)
termination_by (s.potential, n - k)
-- Termination uses only ν_eq, d_eq, and correctness of sizeReduce/swapStep.
-- Advance: sizeReduce preserves d (GS vectors unchanged), so potential
--   unchanged; n - k decreases.
-- Swap: the failing Lovász condition (read from d and ν via d_eq/ν_eq)
--   gives d[k]' < δ * d[k] ≤ d[k]; potential strictly decreases.

/-- Initial `LLLState` constructor: builds the integer state directly
    from a basis matrix and discharges `ν_eq`/`d_eq` by composing the
    existing `hex-gram-schmidt` lemmas
    `GramSchmidt.Int.gramDetVec_eq_gramDet` and
    `GramSchmidt.Int.scaledCoeffs_eq` (suitably massaged through the
    `Rat` casts in their statements). -/
def LLLState.ofBasis (b : Matrix Int n m) (hind : b.independent) :
    LLLState n m :=
  { b
    ν := GramSchmidt.Int.scaledCoeffs b
    d := GramSchmidt.Int.gramDetVec b
    ν_eq := by
      -- combine GramSchmidt.Int.scaledCoeffs_eq with
      -- GramSchmidt.Int.gramDetVec_eq_gramDet
      sorry
    d_eq := by
      -- direct from GramSchmidt.Int.gramDetVec_eq_gramDet
      sorry }

def lll (b : Matrix Int n m) (δ : Rat)
    (hδ : 1/4 < δ) (hδ' : δ ≤ 1) (hn : 1 ≤ n) (hind : b.independent) : Matrix Int n m :=
  lllAux (LLLState.ofBasis b hind) 1 δ hδ hδ' hind (by omega) (by omega)
```

The `scaledCoeffs_eq` and `gramDetVec_eq_gramDet` lemmas referenced
above already exist in `hex-gram-schmidt` (`HexGramSchmidt/Int.lean`).
They are currently `sorry`'d, but that is acceptable here: the
obligation of `LLLState.ofBasis` at Phase 1 is to be a named,
type-correct constructor that names its witness lemmas in proof
position. The two `sorry`s above are discharged as part of Phase 5
work in `hex-gram-schmidt` / `hex-lll`, not as part of getting `lll`
to a usable shape. What changes from the previous SPEC is that the
constructor lives in `hex-lll` rather than as inline anonymous
`sorry, sorry` proof fields in the body of `lll`. Treating the
constructor itself as deferrable is incompatible with `hex-lll`
being on the BZ critical path.

### Short-vector recovery for downstream consumers

The reduced basis returned by `lll` is canonically ordered with
shorter vectors first; `hex-berlekamp-zassenhaus` consumes this
ordering to drive recombination. The Phase 1 entry point exposed for
that consumer is:

```lean
/-- The first row of the reduced basis (shortest vector under the
    LLL guarantee). Marked as the canonical short-vector entry point
    for downstream consumers such as hex-berlekamp-zassenhaus. -/
def lll.firstShortVector (b : Matrix Int n m) (δ : Rat)
    (hδ : 1/4 < δ) (hδ' : δ ≤ 1) (hn : 1 ≤ n) (hind : b.independent) :
    Vector Int m :=
  (lll b δ hδ hδ' hn hind)[0]

/-- The full reduced basis viewed as an ordered list of candidate
    short vectors. -/
def lll.shortVectors (b : Matrix Int n m) (δ : Rat)
    (hδ : 1/4 < δ) (hδ' : δ ≤ 1) (hn : 1 ≤ n) (hind : b.independent) :
    Array (Vector Int m) :=
  (lll b δ hδ hδ' hn hind).toArray
```

Both entry points are Phase 1 deliverables; conformance must exercise
them on the kind of basis matrix BZ recombination produces (one row
per lifted local factor), and Phase 4 benchmarks must register
`lll`/`lll.firstShortVector` as the recombination hot path inherited
from `hex-berlekamp-zassenhaus`.

The swap bound `potential_initial ≤ (maxNormSq b)^{n*(n-1)/2}` follows
from Hadamard's inequality: `gramDet b k ≤ prod_{i<k} ||b[i]||^2 ≤
(maxNormSq b)^k`.

## Loop invariant

At the top of the loop with current index k, expressed in terms of
the noncomputable projections `s.gramSchmidtCoeff` and the GS vectors
(which are mathematical functions of `s.b`, not stored):

(I1) b[0], ..., b[n-1] is a basis of the same lattice L as the input.
(I2) basis[0], ..., basis[n-1] and coeffs[i][j] are the correct
     Gram-Schmidt orthogonalization of the current basis. (This is
     captured by `s.ν_eq` and `s.d_eq`, which assert that the stored
     integer values track the mathematical GS quantities.)
(I3) **Size-reduced below k:** |s.gramSchmidtCoeff i j| <= 1/2 for all j < i < k.
(I4) **Lovász condition below k:** for all 0 <= i < k-1,
     (delta - (s.gramSchmidtCoeff (i+1) i)^2) * ||basis[i]||^2 <= ||basis[i+1]||^2.
(I5) 1 <= k <= n.

Together, (I3) and (I4) say: the first k vectors form a
delta-LLL-reduced basis of the sublattice they span.

**Size-reduction sub-invariant.** The inner loop
`for j in [k-1, k-2, ..., 0]` has its own invariant, parameterized
by the current column j.
After processing column j (and before processing j-1), the following
hold in addition to (I1)-(I5):

(SR1) |s.gramSchmidtCoeff k l| <= 1/2 for all l with j <= l < k.
(SR2) s.gramSchmidtCoeff k l is unchanged for l < j.
(SR3) All basis[i] vectors are unchanged (size reduction preserves GS).
(SR4) The lattice is unchanged (unimodular row operations).

Before processing j = k-1, (SR1) is vacuous (no columns have been
processed yet). After processing column j, (SR1) holds for j <= l < k.
At exit (all columns processed), (SR1) gives
|s.gramSchmidtCoeff k l| <= 1/2 for all l < k, establishing (I3) for the new k.

**Preservation of the outer invariant:**

- *Size reduction (full inner loop):* Preserves the lattice (I1) and
  all basis[i] (I2) — these follow from (SR3)+(SR4). Establishes
  |s.gramSchmidtCoeff k j| <= 1/2 for all j < k — this follows from (SR1) at
  exit. The Lovász conditions for indices < k-1 are unaffected (I4),
  since only coeffs values in row k change and the basis[i] are unchanged.

- *Advance (k <- k+1):* Only happens when the Lovász condition holds
  at index k-1. Combined with the already-established conditions
  below k-1, we now have all conditions below k, so (I3)+(I4) hold
  for the new k.

- *Swap (b[k] <-> b[k-1], k <- max(k-1, 1)):* Preserves the lattice
  (I1). Changes only basis[k-1] and basis[k] among the GS vectors (I2).
  The Lovász conditions for indices < k-2 are unaffected (I4). We
  lose the size-reduction guarantee at the new k (the swapped vector
  may not be size-reduced), so (I3) is only claimed for indices
  below the new k. We may need to re-check at the new k, hence
  decrementing k.

## Short vector bound proof

The proof has three steps.

**Step 1: Consecutive GS norm bound.** From the Lovász condition
with the size-reduction guarantee |coeffs[i+1][i]| <= 1/2:

    (delta - coeffs[i+1][i]^2) * ||basis[i]||^2 <= ||basis[i+1]||^2
    (delta - 1/4) * ||basis[i]||^2 <= ||basis[i+1]||^2

Set alpha = 1 / (delta - 1/4). Then:

    ||basis[i]||^2 <= alpha * ||basis[i+1]||^2

By telescoping (induction on the gap):

    ||basis[0]||^2 <= alpha^i * ||basis[i]||^2     for all 0 <= i < n

More usefully:

    ||basis[0]||^2 <= alpha^{n-1} * min_{0 <= i < n} ||basis[i]||^2

**Step 2: Lower bound lemma.** For any nonzero lattice vector
v in L, we have:

    ||v||^2 >= min_{0 <= i < n} ||basis[i]||^2

*Proof.* Write v = sum_{i=0}^{n-1} a_i * b[i] with a_i in Z (not all
zero). Let k be the largest index with a_k != 0. Expand in the
GS basis:

    v = sum_{i=0}^{k} a_i * b[i]
      = sum_{i=0}^{k} a_i * (basis[i] + sum_{j<i} coeffs[i][j] * basis[j])
      = sum_{i=0}^{k} c_i * basis[i]

for some real coefficients c_i, where crucially c_k = a_k (because
b[k] = basis[k] + sum_{j<k} coeffs[k][j] * basis[j], and no later
b[i] contributes to the basis[k] component). Since a_k is a nonzero
integer, |c_k| >= 1.

By orthogonality of the basis[i]:

    ||v||^2 = sum_{i=0}^{k} c_i^2 * ||basis[i]||^2
            >= c_k^2 * ||basis[k]||^2
            >= ||basis[k]||^2
            >= min_{0 <= i < n} ||basis[i]||^2     QED

**Step 3: Combining.** For any nonzero v in L:

    ||b[0]||^2 = ||basis[0]||^2              (b[0] = basis[0] by definition)
              <= alpha^{n-1} * min_i ||basis[i]||^2    (Step 1)
              <= alpha^{n-1} * ||v||^2                 (Step 2)

This gives the main theorem:

    ||b[0]||^2 <= alpha^{n-1} * ||v||^2

for any nonzero lattice vector v, where alpha = 1/(delta - 1/4).

For the standard choice delta = 3/4, alpha = 2, and we get
||b[0]|| <= 2^{(n-1)/2} * lambda_1(L).

## Integrality and integer representation

This section provides the proofs that the integer update formulas
are correct and that all divisions are exact. (The integrality of
scaledCoeffs itself is proved in hex-gram-schmidt; here we derive
the LLL-specific update formulas.)

**Derivation of the integer Lovász condition.** The rational Lovász
condition rearranged (following Cohen, section 2.6.3):

    ||basis[k]||^2 + coeffs[k][k-1]^2 * ||basis[k-1]||^2 >= delta * ||basis[k-1]||^2

Substitute ||basis[i]||^2 = gramDet (i+1)/gramDet i and
coeffs[k][k-1] = scaledCoeffs[k][k-1]/gramDet k:

    gramDet (k+1)/gramDet k + (scaledCoeffs[k][k-1]/gramDet k)^2 * (gramDet k/gramDet (k-1))
        >= delta * (gramDet k/gramDet (k-1))

Multiply through by gramDet k * gramDet (k-1) (both positive):

    gramDet (k+1) * gramDet (k-1) + scaledCoeffs[k][k-1]^2 >= delta * gramDet k^2

(Negated for the swap trigger: swap when this fails.)

**Correctness of size-reduction updates.** The rational size-reduction
step sets coeffs[k][j] <- coeffs[k][j] - r (and
coeffs[k][l] <- coeffs[k][l] - r * coeffs[j][l] for l < j).
Multiplying through by gramDet (j+1) (resp. gramDet (l+1)) gives
the scaledCoeffs update formulas:

    scaledCoeffs[k][l] <- scaledCoeffs[k][l] - r * scaledCoeffs[j][l]    for l < j
    scaledCoeffs[k][j] <- scaledCoeffs[k][j] - r * gramDet (j+1)

The gramDet values are unchanged because size reduction preserves the
GS basis.

**Rounding.** Define:

```lean
/-- Round to nearest integer (ties round up). -/
def Rat.round (q : Rat) : Int := (q + 1/2).floor
-- Key property: |q - q.round| ≤ 1/2 (from floor_le and lt_floor_add_one)
```

The rounding value r = round(coeffs[k][j]) =
round(scaledCoeffs[k][j] / gramDet (j+1)) is computed as
`Int.fdiv (2 * scaledCoeffs[k][j] + gramDet (j+1)) (2 * gramDet (j+1))`,
which is pure integer arithmetic since gramDet (j+1) > 0.

**Correctness of swap updates.** Let b' be the basis after swapping
b[k] and b[k-1], and let B = (scaledCoeffs b)[k][k-1]. The gramDet
update:

    gramDet b' k = (gramDet b (k+1) * gramDet b (k-1) + B^2) / gramDet b k

follows from the determinant identity for the Gram matrix after the
swap. The scaledCoeffs updates for i > k:

    (scaledCoeffs b')[i][k-1] = (gramDet b (k-1) * (scaledCoeffs b)[i][k] + B * (scaledCoeffs b)[i][k-1]) / gramDet b k
    (scaledCoeffs b')[i][k]   = (gramDet b (k+1) * (scaledCoeffs b)[i][k-1] - B * (scaledCoeffs b)[i][k]) / gramDet b k

follow from substituting the definitions scaledCoeffs = gramDet * coeffs
into the rational coeffs update formulas and simplifying. For j < k-1,
(scaledCoeffs b')[k-1][j] and (scaledCoeffs b')[k][j] are
(scaledCoeffs b)[k][j] and (scaledCoeffs b)[k-1][j] respectively
(simply swapped).

## Termination

**Potential function.** Define:

    D = prod_{i=1}^{n-1} gramDet i

This is the product of the first n-1 Gram determinants. Equivalently:

    D = prod_{k=0}^{n-2} ||basis[k]||^{2(n-1-k)}

(since gramDet i = prod_{j=0}^{i-1} ||basis[j]||^2, each
||basis[k]||^2 appears in gramDet i for i = k+1, k+2, ..., n-1,
contributing exponent n-1-k to the product). Since the basis remains
linearly independent throughout (unimodular row operations preserve
independence), each gramDet i is a positive integer, so D >= 1.

**Size reduction preserves D.** Size reduction does not change
basis b, so all gramDet b i (and hence D) are unchanged.

**Each swap decreases D.** Let b' be the basis after swapping b[k]
and b[k-1], with the Lovász condition failing:

    gramDet b' k = (gramDet b (k+1) * gramDet b (k-1) + (scaledCoeffs b)[k][k-1]^2) / gramDet b k

The Lovász condition fails, meaning:

    gramDet b (k+1) * gramDet b (k-1) + (scaledCoeffs b)[k][k-1]^2 < delta * (gramDet b k)^2

So gramDet b' k < delta * gramDet b k. Since only gramDet at
index k changes (gramDet b' i = gramDet b i for i ≠ k), and
gramDet b k appears exactly once in the product D:

    D' = D * (gramDet b' k / gramDet b k) < D * delta

Since D >= 1 is a positive integer and each swap strictly decreases
D (because gramDet b' k < gramDet b k for integer gramDet values),
the algorithm terminates with at most D_initial - 1 swaps.

For delta < 1, the stronger bound gramDet b' k < delta * gramDet b k
gives D' < delta * D, so:

    #swaps <= log_{1/delta}(D_initial)

Using D_initial <= (max_i ||b[i]||^2)^{n(n-1)/2} (by Hadamard's
inequality: gramDet b k <= prod_{i<k} ||b[i]||^2 <= (maxNormSq b)^k):

    #swaps <= n(n-1)/2 * log(max_i ||b[i]||^2) / log(1/delta)

This is polynomial in n and the bit-size of the input. (At delta = 1,
termination is still guaranteed but the log bound degenerates; the
integer bound #swaps <= D_initial - 1 applies instead.)

**Lean formalization strategy for termination:** Use well-founded
recursion on the pair (D, n - k), lexicographically ordered. Each
iteration either decreases D (swap) or increases k (advance), and
k is bounded by n.

## Formalization strategy: single-state architecture

**Approach.** Unlike the Isabelle AFP formalization (Bottesch et al.,
ITP 2018, JAR 2020), which uses a two-layer bisimulation between a
rational specification and an integer implementation, we use a
single-state design. The `LLLState` stores only integers (b, ν, d).
The rational GS quantities are recovered via `noncomputable`
projections (`LLLState.gramSchmidtCoeff`, and similarly for
`||(basis b)[k]||^2 = gramDet b (k+1) / gramDet b k`), which exist
only for the proof layer.

The key advantage: no bisimulation proof is needed. There is one
state, one algorithm, and the correctness proofs unfold the
`noncomputable` definitions to connect integer update formulas
to their rational counterparts (see integrality section above).
The `noncomputable` marker makes it syntactically impossible for the
rational quantities to leak into the executable code.

**Proof structure.** For each step (size-reduce, swap, advance):
1. Show the integer update formulas preserve `ν_eq` and `d_eq`
   (i.e., the stored integers still track the GS quantities of
   the new basis). This uses the integrality derivations above.
2. Show the loop invariant (I1)–(I5) is preserved. This uses the
   `noncomputable` projections to state conditions in their natural
   rational form.
3. The short vector bound is proved purely in terms of mathematical
   GS properties. Termination uses the integer state directly (the
   potential is a product of gramDet values, and the swap decrease
   follows from the integer Lovász failure).

**Highest-risk proof areas:**

- **Swap update formulas.** The explicit formulas for how
  `GramSchmidt.Int.basis`, `GramSchmidt.Int.coeffs`, `gramDet`, and
  `scaledCoeffs` change under a swap are the most error-prone part.
  Each formula must be verified algebraically and the exact division
  proofs must be discharged.
- **Exact division under swap.** Proving that
  `(gramDet b (k+1) * gramDet b (k-1) + (scaledCoeffs b)[k][k-1]^2) / gramDet b k`
  and the scaledCoeffs update divisions are exact requires the
  determinant-based integrality arguments from hex-gram-schmidt.

**Prior art.** The Isabelle AFP formalization (~14,800 lines across
14 modules) uses a two-layer bisimulation: `LLL.thy` defines a
rational specification with loop invariant proofs, and `LLL_Impl.thy`
defines the d-representation implementation with a step-refinement
proof connecting the two. Their `upw` ("update needed") boolean in
the outer invariant avoids exposing the size-reduction inner-loop
index. We chose not to follow this architecture, instead using a
single integer state with `noncomputable` projections.

**References:**
- Lenstra, Lenstra, Lovász, "Factoring polynomials with rational
  coefficients," *Math. Ann.* 261, 1982, pp. 515-534 (original paper)
- Von zur Gathen & Gerhard, *Modern Computer Algebra*, 3rd ed., 2013,
  ch. 16 (primary reference for formalization)
- Cohen, *A Course in Computational Algebraic Number Theory*, 1993,
  section 2.6 (integral LLL algorithm)
- Galbraith, *Mathematics of Public Key Cryptography*, 2012, ch. 17
  (good exposition; free PDF at math.auckland.ac.nz/~sgal018/crypto-book/)
- Bottesch et al., "A Formalization of the LLL Basis Reduction
  Algorithm," ITP 2018 (Isabelle formalization, conference version)
- Bottesch et al., "Formalizing the LLL Basis Reduction Algorithm and
  the LLL Factorization Algorithm in Isabelle/HOL," *J. Automated
  Reasoning* 64, 2020, pp. 1-42 (Isabelle formalization, journal version)
- Nguyen & Stehlé, "Floating-Point LLL Revisited," EUROCRYPT 2005
  (L^2 algorithm; not needed for our formalization but relevant context)
