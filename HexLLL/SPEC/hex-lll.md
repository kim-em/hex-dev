# hex-lll (LLL lattice basis reduction, depends on hex-gram-schmidt)

`hex-lll` is the recombination primitive used by
`hex-berlekamp-zassenhaus`: BZ encodes the lifted local factors of an
integer polynomial as a lattice basis, runs `lll`, and reads off
candidate `Z[x]` factors from the short vectors. The public surface
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

**delta-LLL-reduced.** Reducedness is parameterized by a size-reduction
bound `η`. A basis `b` is `(δ, η)`-LLL-reduced (for `η ≥ 1/2` and
`η² < δ ≤ 1`) if it satisfies two conditions:

1. **Size-reduced:** |(coeffs b)[i][j]| <= η for all 0 <= j < i < n.

2. **Lovász condition:** For all 0 <= i < n-1:
       delta * ||(basis b)[i]||^2 <= ||(basis b)[i+1]||^2 + (coeffs b)[i+1][i]^2 * ||(basis b)[i]||^2

   Equivalently: (delta - (coeffs b)[i+1][i]^2) * ||(basis b)[i]||^2 <= ||(basis b)[i+1]||^2

The predicate is `isLLLReduced b δ η`. Two values of `η` are pinned:

- **`η = 1/2`** (the classical bound), carried by the native algorithm
  `lllNative`, which produces exact-integer `|μ| ≤ 1/2`.
- **`η = 11/20`**, carried by the public `lll`. This is the bound any
  function that may route through an external reducer can guarantee
  uniformly; it is reached either by `lllNative` (whose `|μ| ≤ 1/2` is
  stronger) or by certifying an external candidate (see *Certified external
  dispatch*).

**Key properties.** Theorems require `hη : 1/2 ≤ η`, `hδη : η² < δ`,
`hδ' : δ ≤ 1`, `hn : 1 ≤ n`, and `hli : b.independent`.

`η² < δ` so that `α = 1/(δ − η²)` is well-defined and positive (at `η = 1/2`
this is `δ > 1/4`). `δ ≤ 1` for termination (the Lovász failure condition is
strict, so each swap gives `gramDet b' k < δ · gramDet b k ≤ gramDet b k`,
strictly decreasing the potential even at `δ = 1`). Linear independence
ensures all Gram determinants `gramDet b k > 0`, which is needed for the GS
orthogonalization to exist and for the scaledCoeffs denominators to be
nonzero.

The short-vector bound is factored through one lemma over the size-reduction
bound:

```lean
theorem short_vector_bound_of_size_bound (b : Matrix Int n m) {δ η : Rat}
    (hη : 1/2 ≤ η) (hδη : η² < δ) (hδ' : δ ≤ 1) (hn : 1 ≤ n)
    (hli : b.independent) (hred : isLLLReduced b δ η)
    (v : Vector Int m) :
    b.memLattice v → v ≠ 0 →
    (b.row 0).normSq ≤ (1/(δ - η²))^(n-1) * v.normSq
```

The public `lll` (η = 11/20) and the native `lllNative` (η = 1/2) instantiate
it:

```lean
theorem lll_same_lattice (b : Matrix Int n m) (δ : Rat) ... :
    (lll b δ ...).memLattice v ↔ b.memLattice v

theorem lll_reduced (b : Matrix Int n m) (δ : Rat) ... :
    isLLLReduced (lll b δ ...) δ (11/20)

theorem lll_short_vector (b : Matrix Int n m) (δ : Rat)
    (hδ : 121/400 < δ) (hδ' : δ ≤ 1)
    (hn : 1 ≤ n) (hli : b.independent)
    (v : Vector Int m) :
    b.memLattice v → v ≠ 0 →
    (lll b δ hδ hδ' hn hli).row 0 |>.normSq ≤ (1/(δ - 121/400))^(n-1) * v.normSq

theorem lllNative_short_vector (b : Matrix Int n m) (δ : Rat)
    (hδ : 1/4 < δ) (hδ' : δ ≤ 1) (hn : 1 ≤ n) (hli : b.independent)
    (v : Vector Int m) :
    b.memLattice v → v ≠ 0 →
    (lllNative b δ hδ hδ' hn hli).row 0 |>.normSq ≤ (1/(δ - 1/4))^(n-1) * v.normSq
```

The classical bound and the wide `δ > 1/4` range live on `lllNative`: at
`δ = 3/4` it gives `‖b₁‖ ≤ 2^{(n-1)/2} · λ₁`. The public `lll` carries the
`η = 11/20` bound (`α = 1/(δ − 121/400)`, precondition `δ > 121/400`).

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
def lllLoop (s : LLLState n m) (k : Nat) (δ : Rat)
    (hδ : 1/4 < δ) (hδ' : δ ≤ 1)
    (hk : 1 ≤ k) (hkn : k ≤ n) : Nat → Matrix Int n m :=
  | 0 => s.b
  | fuel + 1 =>
      if h : k = n then s.b
      else
        let s := s.sizeReduce k
        -- Check Lovász condition (integer arithmetic, no division):
        if δ.den * (s.d[k+1] * s.d[k-1] + s.ν[k][k-1]^2) ≥ δ.num * s.d[k]^2 then
          -- Lovász holds: advance
          lllLoop s (k + 1) δ hδ hδ' (by omega) (by omega) fuel
        else
          -- Lovász fails: swap and decrement
          let s := s.swapStep k
          lllLoop s (max (k - 1) 1) δ hδ hδ' (by omega) (by omega) fuel

def lllFuel (s : LLLState n m) : Nat :=
  (s.potential + 1) * (n + 1)

def lllAux (s : LLLState n m) (k : Nat) (δ : Rat)
    (hδ : 1/4 < δ) (hδ' : δ ≤ 1)
    (hk : 1 ≤ k) (hkn : k ≤ n) : Matrix Int n m :=
  lllLoop s k δ hδ hδ' hk hkn (lllFuel s)

/-- Initial `LLLState` constructor: builds the integer state directly
    from a basis matrix and discharges `ν_eq`/`d_eq` by composing the
    `hex-gram-schmidt` lemmas `GramSchmidt.Int.gramDetVec_eq_gramDet`
    and `GramSchmidt.Int.scaledCoeffs_eq` (suitably massaged through the
    `Rat` casts in their statements). -/
def LLLState.ofBasis (b : Matrix Int n m) (hind : b.independent) :
    LLLState n m :=
  { b
    ν := GramSchmidt.Int.scaledCoeffs b
    d := GramSchmidt.Int.gramDetVec b
    ν_eq := by …   -- from scaledCoeffs_eq and gramDetVec_eq_gramDet
    d_eq := by … } -- from gramDetVec_eq_gramDet

def lll (b : Matrix Int n m) (δ : Rat)
    (hδ : 1/4 < δ) (hδ' : δ ≤ 1) (hn : 1 ≤ n) (hind : b.independent) : Matrix Int n m :=
  lllAux (LLLState.ofBasis b hind) 1 δ hδ hδ' (by omega) (by omega)
```

The `ν_eq` and `d_eq` fields are discharged from the `hex-gram-schmidt`
lemmas `GramSchmidt.Int.scaledCoeffs_eq` and
`GramSchmidt.Int.gramDetVec_eq_gramDet`. `LLLState.ofBasis` is a total
constructor with no deferred proof obligation: `hex-lll` is on the
`hex-berlekamp-zassenhaus` critical path, so its public surface must be
usable without any `sorry`.

### Native default reducer

The native reducer `lllNative` is the **exact all-integer `d`/`ν` reducer**. It
carries the exact Gram-determinant vector `d` and scaled coefficients `ν` of the
`LLLState` representation and drives the standard LLL outer loop — integer
size-reduction and adjacent Lovász swaps — from that exact data alone. Every
basis mutation is one of the proven-lattice-preserving exact integer row
operations (`GramSchmidt.Int.sizeReduce`, the size-reduction row combination,
and `GramSchmidt.Int.adjacentSwap`, the adjacent row swap), so the generated
lattice of the output equals that of the input **by construction**, and the loop
terminates by fuel. Its size-reduction step produces exact `|μ| ≤ 1/2`, so
`lllNative` carries the classical `η = 1/2` contract (precondition `1/4 < δ`,
short-vector constant `1/(δ − 1/4)`).

The public `lll` keeps exactly two paths, both satisfying the same
`(δ, 11/20)` post-condition:

1. the **certified external-candidate** dispatch (provider → `certCheck`, see
   *Certified external dispatch*), and
2. the **exact** `lllNative`, run directly when no provider candidate certifies.

Both pinned `η` values are unchanged: `lllNative` retains `η = 1/2` and the
public `lll` retains `η = 11/20`. The public `lll` contract — same lattice,
`isLLLReduced (lll …) δ (11/20)`, and the `lll_short_vector` bound — holds
verbatim whether the result comes from the certified external candidate or the
exact native path. The `11/20` loosening exists **solely** because a black-box
external reducer cannot be forced to `|μ| ≤ 1/2` exactly; the native path lands
at `1/2` and is the direct `1/4 < δ` entry point.

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
per lifted local factor).

### Required Phase 4 bench-input families

Phase 4 benchmarks must register `lll`/`lll.firstShortVector` as the
recombination hot path inherited from `hex-berlekamp-zassenhaus`,
and must exercise the algorithm on three input families. These are
cross-referenced as `phase4.input_families` in [`libraries.yml`](https://github.com/kim-em/hex-dev/blob/main/libraries.yml):

- **`bz-recombination`** — the Berlekamp–Zassenhaus recombination
  basis at the documented `(p, k, factors)` configurations.
  This is the downstream hot path; performance here is what the
  HexBerlekampZassenhaus pipeline observes.
- **`random-bounded`** — LCG-generated random integer bases with
  bounded entries `|·| ≤ 30` at `n ∈ {30, 60, 120, 240}`. This
  exercises the LLL outer loop on basically-orthogonal input
  where size reduction does most of the work and few swaps fire.
- **`harsh-cubic`** — inputs matching the verified-Isabelle paper's
  regime (entry bit-length `~ 3.3 · n`) at `n ∈ {15, 30, 45}`.
  This exercises bigint operand-size drift in both `LLLState.ofBasis`
  and the swap path; entry sizes grow with `n`, so total input
  size is cubic in `n`.
- **`ajtai`** — Ajtai-style worst-case lower-triangular bases, a
  faithful port of fplll's `gen_trg` (`latticegen t <d> 1.2`): per
  column `i`, `bits_i = ⌊(2d − i)^1.2⌋`, the diagonal `D_i` is uniform
  in `[2, 2^bits_i]`, and below-diagonal entries are uniform in
  `(−D_i/2, D_i/2)`. The steeply decreasing diagonal profile drives the
  `Θ(d² log B)` swap count (Nguyen–Stehlé, *LLL on the Average*,
  ANTS-VII 2006) — the **iteration-count** scaling axis the
  near-orthogonal `random-bounded` and `harsh-cubic` families leave
  unmeasured. Fidelity is structural, not entry-exact (fplll draws from
  GMP, the Lean port from the committed LCG via `wideRandom`):
  `scripts/dev/validate_latticegen.py` checks both satisfy the same
  lower-triangular / `bits_i` / `|off| < D_i/2` envelope.
- **`q-ary`** — LWE/SIS bases `[[I_{d-k}, H], [0, q·I_k]]` (faithful
  port of fplll's `gen_qary` / `latticegen q`), `H` uniform mod
  `q = 2^(b-1) + rand(b-1)`. The unreduced basis is a step profile (a
  plateau at `q` over a plateau at `1`) LLL must smooth into the
  characteristic Z-shape, concentrating swaps in the transition band —
  the realistic cryptographic regime, distinct from a triangular basis.
- **`ntru`** — NTRU-like bases `[[I, Rot(h)], [0, q·I]]` on `2d × 2d`
  (faithful port of fplll's `gen_ntrulike` / `latticegen n`), with
  `Rot(h)` the circulant of `h` uniform mod `q` and `h[0]` fixed so
  `h(1) ≡ 0 mod q` (checked by `#guard`). Planted dense structure plus
  the q-block.
- **`knapsack`** — the **rectangular** `d × (d+1)` integer-relation
  basis (faithful port of fplll's `gen_intrel` / `latticegen r`), row
  `i` = `[rand_b, e_{i+1}]`. The only family with `cols ≠ rows`, so it
  exercises the `m > n` Gram construction in `ofBasis` that every square
  family leaves untested. It also drives the success-vs-density recovery
  chart (planted-vector recovery vs density `d = n/b`).

**At least one family must demonstrably exercise the swap branch of
the LLL outer loop.** For `bz-recombination`, `harsh-cubic`, and
`ajtai` this is automatic (the Ajtai diagonal is steeply decreasing by
construction, checked by the `ajtaiProfileSteep` `#guard`); for
`random-bounded` the family must include at least one committed seed
where ≥ 1 Lovász swap fires, recorded in the bench module as a fixed
fixture so the swap-firing property is verifiable from the SPEC alone.

**Best-case inputs are not sole Phase-4 evidence.** Per
[SPEC/benchmarking.md §Anti-patterns](https://github.com/kim-em/hex-dev/blob/main/SPEC/benchmarking.md#anti-patterns),
inputs the algorithm walks past in its happy path may appear as
supplemental smoke or fixed cases, but never as the sole end-to-end
evidence. Exemplar to avoid: the identity basis. The LLL outer loop
visits every k but does no row update and no swap fires (`ν[k][j] = 0`
for every `j < k`, so `sizeReduce k` is a no-op; the Lovász
condition is trivially satisfied). The registration measures the
loop's traversal cost and nothing about size reduction or swaps.

### External comparators

Three external comparators are required for HexLLL Phase 4. The
classification below is mirrored as structured metadata in
[`libraries.yml`](https://github.com/kim-em/hex-dev/blob/main/libraries.yml) under `HexLLL.phase4.comparators`:

- **`fpLLL via fplll-ffi`** — `informational`. fpLLL implements
  floating-point Gram–Schmidt variants (Nguyen–Stehlé) which
  bypass the integer-arithmetic operand-size drift our verified
  implementation pays. The constant-factor gap is structural, not
  algorithmic, so the ratio is recorded for orientation but does
  not gate Phase 4. See
  [SPEC/benchmarking.md §Comparator classification](https://github.com/kim-em/hex-dev/blob/main/SPEC/benchmarking.md#comparator-classification-gating-vs-informational).
  fpLLL is measured through the **FFI shim** `fplll-ffi` (the preferred
  comparator pattern per
  [SPEC/benchmarking.md §External comparators](https://github.com/kim-em/hex-dev/blob/main/SPEC/benchmarking.md#external-comparators)),
  an in-process C++ call into `libfplll` — not a Python (`fpylll`) subprocess,
  whose interpreter and IPC overhead the runtime path never pays. This is the
  same `fplll-ffi` the certified external-dispatch path resolves at runtime, so
  the fpLLL curve and the certified path measure the identical C++ reducer.
  fpLLL also serves as the external reducer behind *Certified external
  dispatch*; the certified path's measured cost is the `fplll-ffi` call —
  which returns `(reduced, U, V)` directly — plus the verified checker.
- **`verified Isabelle certified-LLL`** — `gating`. The Isabelle
  formalisation's own certified-output configuration (JAR 2020 §7): a
  verified checker over an untrusted floating-point reducer. It is the
  `svp_certified` executable of the same Zenodo 2636367 `LLL_Basis_Reduction`
  extraction that supplies the native comparator — built from one extra
  `make` target on that archive — which shells out to the `fplll` binary for
  `(reduced, U, V)`, verifies the same two-transform certificate this library
  uses (`F = U·reduced` ∧ `reduced = V·F`), and confirms reducedness by
  re-running the verified LLL. It is the apples-to-apples yardstick for the
  certified path. **Performance goal:** the hex certified path (fpLLL +
  checker) is **at least as fast as** the Isabelle certified-LLL on shared
  canonical inputs at the largest eligible rung of each
  `phase4.input_families` ladder. The headline report records the ratio, the
  checker's share of the cost, and the candidate rejection rate, and notes the
  architectural asymmetries the comparison is read against — the Isabelle path
  spawns the `fplll` binary per call (this library uses in-process `fplll-ffi`)
  and re-runs the full verified LLL to confirm reducedness (this library runs
  the `lllReducedInt` integer check).
- **`verified Isabelle LLL`** — `gating`. The Bottesch–Divasón–
  Haslbeck–Joosten–Thiemann–Yamada formalisation in the Archive of
  Formal Proofs (entry `LLL_Basis_Reduction`) is the only other
  formally-verified LLL implementation. Its executable form is the
  Haskell code generated from the Isabelle development, deposited
  on Zenodo as record 2636367 ("Experiments_LLL"). It implements
  the same Cohen Algorithm 2.6.3 integer-only recurrence we use,
  so the comparison is apples-to-apples and the constant-factor
  gap is the right yardstick for Phase 4.

  **Performance goal:** Lean LLL is **at least as fast as the
  verified Isabelle LLL** on shared canonical inputs, evaluated at
  the largest eligible rung of each `phase4.input_families` parameter
  ladder per
  [SPEC/benchmarking.md §Headline reports — Comparator ratios](https://github.com/kim-em/hex-dev/blob/main/SPEC/benchmarking.md#headline-reports).
  "Eligible" is the rung range between the comparator-overhead-
  dominance floor and the per-call wallclock ceiling (10 s hard,
  1 s soft) defined there. The headline report at
  `reports/hex-lll-performance.md` records measured ratios across
  the full ladder, with raw and overhead-adjusted values; bottom-rung
  ratios are reported for context but do not constitute the verdict.
  An adverse trend (Lean steadily losing ground as the parameter
  grows) is itself an audit-found Concern per
  [PLAN/Conventions.md §Bench-found, conformance-found, and
  audit-found issues](https://github.com/kim-em/hex-dev/blob/main/PLAN/Conventions.md#bench-found-conformance-found-and-audit-found-issues),
  even when the highest-rung verdict happens to pass.

  **Comparator-call protocol.** `fpLLL` is an in-process FFI call through
  `fplll-ffi` (one C++ call per request). The bench obtains `fplll-ffi` the
  same way the certified dispatch resolves it at runtime, and with **no Lake
  dependency** on it: a setup script builds the `fplll-ffi` shared library and
  a path override (env var, mirroring the Isabelle binary-path overrides) makes
  the bench `dlopen` it at start-up, after which the dispatch's `dlsym` probe
  resolves the provider and the fpLLL comparator calls it directly. The two
  Isabelle comparators (`verified Isabelle LLL` and `verified Isabelle certified-LLL`)
  are wired as persistent subprocesses per
  [SPEC/benchmarking.md §External comparators — Process call](https://github.com/kim-em/hex-dev/blob/main/SPEC/benchmarking.md#external-comparators):
  one subprocess per comparator per `lake exe hexlll_bench run`,
  looping on stdin. Per-call overhead is measured for each
  comparator (FFI call overhead for fpLLL, steady-state request overhead for
  the subprocess comparators) and recorded in
  `reports/hex-lll-performance.md §"Comparator ratios"`. Ratios
  are reported across the full (potentially densified) parameter
  ladder of each input family, with both raw and overhead-adjusted
  values where the thresholds in
  [§Headline reports — Comparator ratios](https://github.com/kim-em/hex-dev/blob/main/SPEC/benchmarking.md#headline-reports)
  apply.

  **Headline comparator plot — five curves.** The per-family plots at
  `reports/figures/hex-lll-comparator-<family>.svg`, generated by
  `scripts/plots/hex-lll-comparator.py` and embedded in
  `reports/hex-lll-performance.md`, draw five log-y wall-time-per-call
  curves across the family's eligible range:

  1. **fpLLL** — the raw floating-point reducer alone (unverified).
  2. **Lean native LLL** — the exact integer `d`/`ν` algorithm (`lllNative`),
     the in-tree default reducer. Data comes from the `runNativeFirstShortVector*`
     (equivalently `runFirstShortVector*`) bench targets.
  3. **verified Isabelle native LLL** — the `LLL_Basis_Reduction` extraction.
  4. **Lean certified** — fpLLL candidate production plus the Lean verified
     checker (`certCheck`); the certified external-dispatch path. Data comes
     from the `runCertified*` bench targets.
  5. **verified Isabelle certified-LLL** — fpLLL candidate production plus the
     Isabelle verified checker (the `svp_certified` JAR 2020 §7 configuration
     of the Zenodo 2636367 extraction).

  Curves 1–3 compare the reducers — the raw floating-point reducer, the exact
  Lean integer algorithm, and the Isabelle extraction; curves 4–5 are the
  apples-to-apples verification comparison — the *same* fpLLL output certified by
  the Lean checker versus the Isabelle checker — which is the yardstick for the
  `verified Isabelle certified-LLL` gating goal. A comparator with fewer than two
  committed data points on a family is listed in §Concerns rather than dropped
  from the plot silently. A curve whose reducer exceeds its per-call wall-time cap
  at a rung (a `null` median in the export) simply stops at that ceiling:
  per-curve x-ranges differ, so the verified Isabelle curves end where the worst
  case outgrows the cap while the cheap fpLLL/certified curves continue.

  **Per-call floor calibration.** The `svp_certified` comparator runs as a
  *persistent* subprocess (one per `lake exe hexlll_bench run`, looping on
  stdin), so its per-request cost is not a fork: it is a fixed round-trip floor
  — request marshalling plus the per-request fplll candidate production and
  Isabelle check — independent of `n`. That floor is ~21 ms on carica in the
  committed exports. It is measured once per run by the
  `runIsabelleCertifiedProcessFloorNormSq` target (a trivial 2×2 request) and
  subtracted from the `verified Isabelle certified-LLL` curve by
  `subtract_request_floor`, so the plotted value is the marginal reduction cost,
  not the fixed per-request overhead. Each family's floor is resolved per family
  (`default_floor_path`, commit-matched to the data export); a run that has no
  floor export plots the curve unadjusted and leaves it labelled `Isabelle
  certified` (never mislabelled as adjusted). Rungs whose raw time is within
  15% of the floor are *floor-dominated* — the subtracted value is within the
  floor's own measurement noise — and are dropped, so the adjusted curve begins
  where the reduction cost rises clearly above the floor.

  **Success-vs-density plot (knapsack only).** The `knapsack` family also
  commits a second chart type at
  `reports/figures/hex-lll-knapsack-success.svg`, generated by
  `scripts/plots/hex-lll-knapsack-success.py`: planted-vector **recovery rate**
  versus lattice density `d = n / b` per reducer, over a fixed-`n` sweep across
  many committed seeds. This is the only family whose interesting signal is
  solution *quality* (a phase transition), not wall time; the Lagarias–Odlyzko
  `0.646` and CJLOSS `0.940` constants are drawn as annotated **reference
  density lines with citations**, not as guaranteed thresholds (the guarantee
  holds only when the embedding matches the literature setup). The recovery
  sweep runs in a separate non-timed driver so its many-seed membership checks
  never pollute the wall-time harness.

  **Headline-SVG selection rule.** The README `# Performance` section embeds one
  figure. The default headline is the `harsh-cubic` plot, where the exact
  reducers climb super-quintically as operands widen while the certified path
  (fpLLL candidate + Lean `certCheck`) stays near fpLLL's slope; a worst-case
  family (e.g. `ajtai`) may be promoted when it shows the certified path holding
  flat while the exact reducers provably diverge over ≥ 3 overlapping rungs. The
  rule is fixed in advance so the choice is not post-hoc cherry-picking.

### `LLLState.ofBasis` is its own bench target

The integer Gram–Schmidt construction in `LLLState.ofBasis` —
implemented as a per-row Schur-complement recurrence over the
Gram matrix (per
[SPEC/Libraries/hex-gram-schmidt.md](hex-gram-schmidt.md)) — is
asymptotically significant in its own right: classical analysis
gives ~ n³ integer arithmetic operations with operand bit-width
growing in `n` per Hadamard's bound. This shape is distinct from
the LLL outer loop's ~ n² iterations × O(n) work on
near-orthogonal random input. Per the
[SPEC/benchmarking.md §Attribution rule](https://github.com/kim-em/hex-dev/blob/main/SPEC/benchmarking.md#the-attribution-rule),
each must be verified by its own `setup_benchmark` so a future
profiling finding is attributable to one phase or the other:

- a `setup_benchmark` for `LLLState.ofBasis n => …` declaring the
  GS-prep complexity over the bench's input family;
- a `setup_benchmark` for `lll`/`lll.firstShortVector` (or a fixed
  benchmark on a family-specific canonical input) declaring the
  outer-loop complexity over that input family.

The headline report's §Profile subsection cross-checks: the
dominant inclusive cost on each input family must be attributable
to one of these registered targets, or the audit files an
audit-found issue per
[PLAN/Conventions.md §Bench-found, conformance-found, and audit-found
issues](https://github.com/kim-em/hex-dev/blob/main/PLAN/Conventions.md#bench-found-conformance-found-and-audit-found-issues).

HexLLL's parametric scientific registrations use
`signalFloorMultiplier := 1.0` per
[SPEC/benchmarking.md §Spawn-floor filter](https://github.com/kim-em/hex-dev/blob/main/SPEC/benchmarking.md#spawn-floor-filter).
The registered targets run warm child-side inner-repeat batches; a
slow scheduled host startup should be visible in the export metadata
but must not by itself erase the fixed Phase-4 ladder.

The swap bound `potential_initial ≤ (maxNormSq b)^{n*(n-1)/2}` follows
from Hadamard's inequality: `gramDet b k ≤ prod_{i<k} ||b[i]||^2 ≤
(maxNormSq b)^k`.

## Certified external dispatch

The public `lll` runs the native algorithm `lllNative` by default, and when
an optional external reducer is present in the process it instead certifies
that reducer's output, falling back to `lllNative` whenever the candidate is
absent or fails certification. The two paths satisfy the identical
post-condition (`isLLLReduced (lll …) δ (11/20)`, same lattice, the
`lll_short_vector` bound), so dispatch is invisible to callers and to proofs.
`lll`'s guarantee is property-level, not value-level: two calls may return
different `(δ, 11/20)`-reduced bases of the same lattice.

**Certificate and checker.** An external candidate is a triple
`(B', U, V)` — a reduced basis with integer transforms. It is accepted iff
the executable checker `certCheck B B' U V δ η : Bool` returns `true`, where
`certCheck` verifies, over integer arithmetic only:

- `U.mul B = B'` and `V.mul B' = B`, which together give `lattice B =
  lattice B'` by row-combination composition (no determinant and no
  matrix-inverse reasoning). Each product equality `M·A = C` is verified
  without forming the matrix product: every row of `A` and of `C` is packed
  into a single integer in balanced base `2^K`, and row `i` of the
  unformed product is compared as the packed big-integer dot product
  `Σ_l M[i][l]·packA[l]` against `packC[i]`. The digit width `K` is
  computed from an entry bound covering both sides (`n · max|M| · max|A| +
  max|C|`, or any provably sufficient bound) so that every digit `x` of
  either side satisfies `2·|x| < 2^K`; that bound makes the balanced
  base-`2^K` representation injective, which is the soundness argument.
  The packed comparison is complete as well as sound: by linearity of
  packing it accepts exactly when the products are equal. For word-scale
  transforms and bases, the same-lattice clause costs `O(n²)`
  big-by-small multiplications rather
  than the `O(n²·m)` entry products of a materialized `Matrix.mul`. For
  wide entries, the packed dot products have the same bit-operation scale
  as the materialized product, plus bound-scan and repacking overhead,
  while preserving the same acceptance predicate `M·A = C`;
- `B'` independent and `(δ, η)`-size-reduced and Lovász. The clause is
  decided by a sound fixed-precision enclosure Gram-Schmidt pass over the
  exact integer Gram matrix of `B'`: a closed dyadic interval
  representation with `Int` endpoint mantissas at a shared power-of-two
  scale (no floating point anywhere in the trusted path), per-operation
  containment for add / sub / mul / div-by-positive, and an `O(n³)`
  pass that produces enclosures of every `‖b*_i‖²` and `μ[i][j]`. The
  pass costs `O(n³)` operations on fixed-width mantissas, independent of
  the Gram-determinant bit growth of the input family — which is the
  whole point: the exact `d`/`ν` checker pays `O(n²)` exact-integer
  operations whose operands grow with `n`, while the enclosure pass
  rounds out to a fixed working precision. Acceptance requires every
  independence enclosure (`0 < ‖b*_i‖²` lower bound), every
  size-reduction enclosure (`|μ[i][j]| ≤ η` enclosure strictly inside
  `[−η, η]`), and every Lovász enclosure (the upper-bound enclosure of
  `δ·‖b*_i‖²` strictly below the lower-bound enclosure of
  `‖b*_{i+1}‖² + μ²·‖b*_i‖²`) to be decided on the correct side.
  Indecision (any enclosure straddling its threshold, or any
  norm-enclosure failing strict positivity) falls back to the exact
  integer `d`/`ν` checker (all `d` positive,
  `η.den·(ν[i][j]).natAbs ≤ η.num·d[j+1]` — the integer form of
  `|μ| ≤ η` — and `δ.den·(d[i+2]·d[i] + ν[i+1][i]²) ≥ δ.num·d[i+1]²`),
  which is *mandatory*: completeness of the dispatched reducedness
  clause is structural (the exact checker is complete on every
  candidate) rather than numerical (no precision-tuning regime where
  the dispatch can refuse a reduced candidate).

  Dispatch between the two checkers is by a deterministic input-size
  predictor — a function of the input alone, never of checker
  indecision, so per-input timing stays unimodal across the input
  family. The predictor's role is performance only; both branches are
  sound and complete. The dispatch outcome tally distinguishes three
  modes: *interval-accepted* (enclosure pass decided yes), *exact-primary*
  (predictor routed straight to the exact checker), and *exact-fallback*
  (interval pass was indecisive, exact checker decided). The
  `exact-fallback` count is observable; tracking it lets a measurement
  confirm the enclosure path actually decides whenever the predictor
  said it would.

The checker is generic in the size-reduction bound, matching the
`isLLLReduced`/`short_vector_bound_of_size_bound` layer; the pin lives at the
call site, not inside the mechanism. The single trusted theorem is

```lean
theorem certCheck_sound (B B' U V : Matrix Int n m) (δ η : Rat) :
    certCheck B B' U V δ η = true →
      (∀ v, B.memLattice v ↔ B'.memLattice v) ∧
      B'.independent ∧ isLLLReduced B' δ η
```

The reducedness obligation factors through the shape

```lean
theorem lllReducedInterval_sound (b : Matrix Int n m) (δ η : Rat) :
    lllReducedInterval b δ η = true →
      isLLLReduced b δ η ∧ b.independent
```

which states that enclosure acceptance entails the exact rational
`isLLLReduced` predicate at the requested `(δ, η)` parameters. No
hypothesis on the working precision is needed: soundness is per-input,
not per-precision-regime. The dispatch-side soundness theorem
(`lllReducedCheck_sound`) covers all three modes — interval-accepted,
exact-primary, exact-fallback — by case analysis on the predictor and
the enclosure verdict; it depends on `lllReducedInterval_sound` for the
enclosure branch and on the existing exact-integer soundness for both
exact branches.

No validity hypothesis on `η` is needed here (the bound's `1/2 ≤ η`, `η² < δ`
conditions live on `short_vector_bound_of_size_bound`, not on the checker).
The dispatched `lll` calls `certCheck … (11/20)`; the dispatch's correctness
depends only on `certCheck_sound`, and the checker internals are not relied on
elsewhere.

**Provider hook.** `lll` consults an `opaque @[extern]` hook that supplies a
candidate when an external reducer is registered and signals absence
otherwise (governed by the *untrusted dispatch hooks* clause in
[SPEC/SPEC.md §Project-wide proof policy](https://github.com/kim-em/hex-dev/blob/main/SPEC/SPEC.md#project-wide-proof-policy)). The hook is process-stable (availability is fixed
at first probe and cached), returns only a candidate, and is queried for
availability *before* any input marshalling, so the native path pays at most a
single cached probe. The hook's C body probes for the provider's versioned
public symbol at runtime; the provider is an independent package that this
library neither depends on nor names in its build, and which has no knowledge
of this library. The candidate's shape (dimensions, array lengths) is
validated in Lean before use; a malformed candidate is a rejection.

**Reliability is empirical, soundness is not.** A candidate whose exact
`|μ|` exceeds `11/20` is rejected and the native path runs; the `11/20` bound
carries enough margin over a floating-point reducer's size-reduction
threshold that acceptance is the common case, but correctness never depends on
the reducer's numerical behaviour. The dispatch records an
`absent / provider-error / rejected / accepted` tally for the provider
outcomes and an `interval-accepted / exact-primary / exact-fallback` tally
for the reducedness clause's decision modes; both are diagnostics only,
and acceptance never depends on either.

**Requested parameters carry margin.** The dispatch does not request the
`(δ, 11/20)` it certifies; it asks the external reducer for a strictly
stronger `(δ', η')` with `1/2 < η' < 11/20` and, for every `δ < 1`,
`δ < δ' < 1`. The reducedness clause is decided by the fixed-precision
enclosure pass, which resolves each open inequality only by margin: a
candidate whose `|μ|` or Lovász quantity sat arbitrarily close to the
certified bound would leave the enclosure straddling its threshold and force
the exact fallback. Requesting strictly stronger parameters removes that
possibility — a correctly-functioning reducer lands every size-reduction
inequality a margin `11/20 − η'` clear of the certified bound and every Lovász
inequality a margin `(δ' − δ)·d[i+1]²` clear, so the enclosure decides each one
in decisive territory rather than straddling it.

The concrete margins are the design constants `η' = 107/200` and
`δ' = min(δ + 1/100, (δ + 1)/2)`. The midpoint cap keeps `δ < δ' < 1` across
the whole `δ ≤ 1` surface: for `δ ≤ 49/50` the request is `δ + 1/100`; for
`49/50 < δ < 1` it is the midpoint `(δ + 1)/2`, with margin `(1 − δ)/2` still
positive; only at the boundary `δ = 1` is no strictly stronger request
possible, and there the request equals the certified `δ`. The margins are
deliberately small: the Lovász parameter governs how many swaps the reducer
performs, so a wide `δ` gap would cost reducer work for no soundness benefit,
whereas a narrow gap still gives the enclosure a decisive margin.

These requested parameters are entirely outside the trusted story, exactly as
the reducer's numerical behaviour is: certification runs against the exact
`(δ, 11/20)`, never against `(δ', η')`, so the margins may be retuned — or
ignored by a reducer that cannot honour them — without touching
`certCheck_sound`. The gap buys reliable enclosure decisiveness, not
correctness; it extends the "reliability is empirical, soundness is not"
clause rather than qualifying it.

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

**Lean formalization strategy for termination:** The executable loop
does not use in-place well-founded recursion. The executable layer is
Mathlib-free, so its `decreasing_by` block cannot import the
Mathlib-side swap strict-decrease lemmas (`gramDet_pos`,
`gramDet_adjacentSwap_pivot`, and
`adjacentSwap_gramDetNumerator_dvd`). The proof-free downstream
consumer path also calls `lllUnchecked` from BZ projected-row
construction, where no `bhksLatticeBasis` independence theorem is
available to supply an `(hind : s.b.independent)` argument to every
recursive call.

Instead, termination is implemented by structural recursion on a fuel
argument. `lllAux` is a thin total wrapper around:

    lllLoop s k δ hδ hδ' hk hkn (lllFuel s)

where:

    lllFuel s = (s.potential + 1) * (n + 1)

The `fuel = 0` branch returns the current basis. This is classified
in [the project's design-principles spec](https://github.com/kim-em/hex-dev/blob/main/SPEC/design-principles.md) as
`unreachable-by-pipeline-invariant`: for independent public inputs,
the fuel-sufficiency theorem proves that `lllFuel` is enough for the
loop to reach `k = n` before the fallback branch is taken.

The potential argument above is still the mathematical reason that the
fuel is sufficient. Each loop step either advances `k` with unchanged
potential, or performs a swap that strictly decreases `D`; because
there are at most `n + 1` consecutive advances between swaps and at
most `s.potential` strict positive-integer potential decreases, the
initial fuel bound covers the whole run. This proof lives in the
Mathlib layer, where the swap-decrease and positivity lemmas are
available, rather than in the Mathlib-free executable recursion.

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
