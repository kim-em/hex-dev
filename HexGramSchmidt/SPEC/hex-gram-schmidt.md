# hex-gram-schmidt (Gram-Schmidt orthogonalization, depends on hex-matrix)

Gram-Schmidt orthogonalization for integer and rational matrices.
Provides the GS orthogonal basis, coefficient matrix, Gram determinants,
and update formulas under row operations. Used by hex-lll but logically
independent of LLL.

**Design:**
- Two sub-namespaces: `GramSchmidt.Int` (integer input matrices) and
  `GramSchmidt.Rat` (rational input matrices).
- Functions return matrices, not indexed single-entry functions:
  `basis b` returns a `Matrix Rat n m` (all GS vectors at once),
  `coeffs b` returns a `Matrix Rat n n` (lower-unitriangular).
- `Nat` indices with explicit bounds hypotheses, not `Fin`.
- `basis` and `coeffs` are `noncomputable` (rational division); they
  exist for the proof layer. `gramDet` and `scaledCoeffs` are computable.

**API:**

```lean
namespace Hex.GramSchmidt.Int

/-- The Gram-Schmidt orthogonal basis. Row i is the projection of b.row i
    onto the orthogonal complement of span(b.row 0, ..., b.row (i-1)). -/
noncomputable def basis (b : Matrix Int n m) : Matrix Rat n m

/-- The Gram-Schmidt coefficients. Lower-unitriangular: entry (i,j) is
    ⟨b[i], (basis b)[j]⟩ / ⟨(basis b)[j], (basis b)[j]⟩ for j < i,
    1 on diagonal, 0 above. -/
noncomputable def coeffs (b : Matrix Int n m) : Matrix Rat n n

/-- The k-th Gram determinant: det of the k×k leading Gram submatrix.
    gramDet b 0 = 1 by convention. Returns Nat (always a positive integer
    for independent bases; an internal helper computes the Int determinant
    and the public API wraps via .toNat). -/
def gramDet (b : Matrix Int n m) (k : Nat) (hk : k ≤ n) : Nat

/-- All Gram determinants as a vector.
    Computed incrementally (e.g. one Bareiss-style elimination pass
    over the full Gram matrix that emits each leading-principal
    minor along its diagonal): O(n^3 + n^2 m) total. Recomputing
    `gramDet b k` independently for each k by rebuilding the
    leading k × k Gram matrix and its determinant from scratch is
    forbidden — that body is `O(n^4 + n^3 m)`. -/
def gramDetVec (b : Matrix Int n m) : Vector Nat (n + 1)

/-- Scaled GS coefficients (the ν-values): entry (i,j) = d_{j+1} * μ_{i,j}
    for j < i. Always integers (integrality lemma).

    Computed via a per-row Schur-complement recurrence. For each
    `(i, j)` with `j < i`, define a σ-chain of length `j + 1` with
    one exact integer divide per step:

        σ₀     := ν[i][0] * ν[j+1][0]
        σ_l    := (d_{l+1} * σ_{l-1} + ν[i][l] * ν[j+1][l]) / d_l
                        for 1 ≤ l ≤ j
        ν[i][j] := d_{j+1} * ⟨b_i, b_{j+1}⟩ - σ_j

    where `d_k` is the `k`-th leading-principal-minor determinant
    of the Gram matrix (`d_0 := 1`), stored as
    `scaledCoeffs[k-1][k-1]`. Diagonal entries
    `scaledCoeffs[k][k] = d_{k+1}` are produced by the same
    shape with `i = j + 1 = k`.

    Total: `≈ n^3 / 3` big-int multiplications (the σ-chain
    contributes one `+ 1` multiply per level, summed over
    `(i, j)` to `≈ n^3 / 6`, doubled by the `*` inside the chain)
    plus `n^2 * m` dot-product multiplications for the
    `⟨b_i, b_{j+1}⟩` inner products. This recurrence shape is the
    one used by the verified Isabelle LLL's `dmu_array_row` /
    `sigma_array` (AFP `LLL_Basis_Reduction`, Bottesch et al.);
    the project requires this shape because the comparator runs
    against that implementation.

    **Implementer / prover hint.** The σ-chain is the fraction-free
    Desnanot-Jacobi (Bareiss) update for the bordered Gram minor
    that defines `ν[i][j]`. In the code's index convention (which
    the implementation uses, but the formula above uses the
    shifted Isabelle convention), the equivalent statement is: for
    code slot `(i, j)` with `0 < j ≤ i`,

        σ₀     = ν[i][0] · ν[j][0]
        σ_p    = (d_{p+1} · σ_{p-1} + ν[i][p] · ν[j][p]) / d_p
        ν[i][j] = d_j · ⟨b_i, b_j⟩ − σ_{j-1}

    where `d_p` is stored at slot `(p-1, p-1)` in the result array;
    do not translate this to external Bareiss indexing without
    care. The proof obligation is essentially the standard
    fraction-free Schur-complement determinant identity
    `nextMinor · prevPivot = pivot · currentMinor − leftMinor · topMinor`,
    which HexMatrix already exposes via
    `Matrix.noPivotLoop` / `Matrix.borderedMinor` and the
    `noPivotLoop_full_eq_borderedMinor_at_trailing` bridge.

    **Mathlib-bridge proof layer.** `Matrix.exactDiv` is
    executable and takes no Lean divisibility argument at
    runtime; what needs proof is the *proof-side quotient
    provenance* — any theorem that identifies a `Matrix.exactDiv`
    invocation with the intended quotient or determinant value.
    For the σ-chain on Gram matrices, this provenance is
    Bareiss-Desnanot integrality, which per
    [hex-matrix.md §Mathlib-free vs. Mathlib-bridge proof
    surface](hex-matrix.md) lives exclusively in the
    `*-mathlib` bridge layer.

    Concretely:

    - Any Schur-side characterization that pins
      `getArrayEntry (scaledCoeffRowsSchur b) i j` to a
      bordered-minor determinant, **or to the corresponding
      `Matrix.noPivotLoop` trailing update** (the operational
      shape that avoids spelling `det` but carries the same
      quotient identity), is bridge-layer work. Both formulations
      are equivalently affected: operationally re-deriving the
      Schur ≡ Bareiss step has the same bridge-layer status as
      explicitly rederiving Desnanot-Jacobi.
    - These characterizations take a public quotient-provider API
      as a hypothesis. The API exposes the non-singular
      regular-step quotient data needed by the Schur proofs; the
      bridge layer constructs its instances.
    - The non-singular regular-step branch and Schur-side
      characterizations in the singular column range are
      bridge-layer work. The non-singular branch needs Bareiss
      exact-division divisibility
      (`denom ∣ pivot · entry − row · col`) on Gram-pass
      denominators, supplied by the quotient-provider API. For a
      singular step at column `s`, the Schur-side range is every
      in-bounds cell with `s < j ≤ i`: proving those computed
      Schur values are zero needs the PSD column-zero fact (zero
      Bareiss pivot ⟹ rest-of-column above is zero). The
      recurrence alone does not imply this: symmetric non-Gram
      `[[1,1,0],[1,1,1],[0,1,1]]` has singular step at `s = 1`,
      and the σ-chain already returns `-1` at slot `(2, 2)` while
      the column-major Bareiss kernel returns `0`.
    - The kernels are asymmetric after a singular step. The
      column-major Bareiss kernel writes the singular column,
      then stops; cells in columns `j > s` are reads from the
      initial zero buffer, so their zero characterization is
      Mathlib-free on the column-major side. The Schur kernel has
      no singular stop and writes every cell with `j ≤ i`; a
      post-singular Schur zero for `0 < j ≤ i` must show the
      σ-chain write value is zero. Therefore any theorem equating
      the two kernels' outputs in the singular range is
      bridge-layer work whenever it uses the Schur-side zero,
      even if the column-major zero is proved separately and
      Mathlib-free. The Schur-side facts that remain Mathlib-free
      are structural cell facts: upper-triangle cells are never
      written and remain `0`; column-zero writes equal the Gram
      entry and use no σ-fold; array initialisation,
      out-of-bounds, and frame lemmas do not use PSD or
      Bareiss-divisibility input.
    - The provider type must quantify only over **canonical
      (loop-constructed)** `BareissGramRowInvariant` instances,
      not arbitrary ones. Universal quantification over arbitrary
      `hinv` admits non-canonical coefficient witnesses for which
      the quotient identity fails (counterexample: rows `(1,1),
      (1,0), (-1,-1)` give two valid `hinv` at row 2 step 1
      differing by the kernel vector, yielding numerators
      differing by `1`, not divisible by `prevPivot = 2`). A
      bridge-layer instance constructor derives the canonical
      witness from Bareiss-Desnanot on the PSD Gram minors.
    - Executable kernels (`schurSigma`, `schurScaledCoeffEntry`,
      `scaledCoeffRowsSchur`) and pure cell-stability / row-frame
      lemmas that don't establish a determinant-or-noPivotLoop
      equivalence remain Mathlib-free.

    Two body shapes are forbidden:
    (a) computing each below-diagonal entry independently as a
        `(j+1) × (j+1)` Bareiss determinant — `O(n^5)`;
    (b) column-major Bareiss elimination over the lower
        sub-matrix that, at each pivot step k, updates every
        `(n − k) × (n − k)` cell with a two-product fraction-free
        Schur step (`pivot * A[i][j] − A[i][k] * A[k][j]) / prevPivot`) —
        `≈ 2n^3 / 3` big-int multiplications per `ofBasis`,
        roughly `2×` the per-row recurrence. The constant-factor
        overhead is observable as a `~14%` wall-time gap against
        the verified Isabelle comparator on HexLLL's harsh-cubic
        ladder (per-op cost differs too: full Bareiss tends to
        carry larger intermediate operands). -/
def scaledCoeffs (b : Matrix Int n m) : Matrix Int n n

end Hex.GramSchmidt.Int

namespace Hex.GramSchmidt.Rat

noncomputable def basis (b : Matrix Rat n m) : Matrix Rat n m
noncomputable def coeffs (b : Matrix Rat n m) : Matrix Rat n n
def gramDet (b : Matrix Rat n m) (k : Nat) (hk : k ≤ n) : Rat

end Hex.GramSchmidt.Rat
```

**Key properties** (stated for `GramSchmidt.Int`; `Rat` analogous):
```lean
theorem basis_zero (b : Matrix Int n m) (hn : 0 < n) :
    (basis b).row 0 = (b.row 0).map Int.cast

theorem basis_orthogonal (b : Matrix Int n m)
    (i j : Nat) (hi : i < n) (hj : j < n) (hij : i ≠ j) :
    ((basis b).row i).dotProduct ((basis b).row j) = 0

theorem basis_decomposition (b : Matrix Int n m) (i : Nat) (hi : i < n) :
    (b.row i).map Int.cast =
      (basis b).row i +
      Finset.sum (Finset.range i) fun j =>
        (coeffs b)[i][j] • (basis b).row j

theorem coeffs_diag (b : Matrix Int n m) (i : Nat) (hi : i < n) :
    (coeffs b)[i][i] = 1

theorem coeffs_upper (b : Matrix Int n m)
    (i j : Nat) (hi : i < n) (hj : j < n) (hij : j > i) :
    (coeffs b)[i][j] = 0

theorem basis_span (b : Matrix Int n m) (i : Nat) (hi : i < n) :
    -- span(basis b 0, ..., basis b i) = span(b 0, ..., b i)
    sorry

theorem gramDet_eq_prod_normSq (b : Matrix Int n m)
    (hli : b.independent) (k : Nat) (hk : k ≤ n) :
    (gramDet b k hk : Rat) =
      Finset.prod (Finset.range k) fun j =>
        ((basis b).row j).dotProduct ((basis b).row j)

theorem gramDet_pos (b : Matrix Int n m)
    (hli : b.independent) (k : Nat) (hk : k ≤ n) (hk' : 0 < k) :
    0 < gramDet b k hk

theorem basis_normSq (b : Matrix Int n m)
    (hli : b.independent) (k : Nat) (hk : k < n) :
    ((basis b).row k).dotProduct ((basis b).row k) =
      (gramDet b (k + 1) (by omega) : Rat) / (gramDet b k (by omega) : Rat)

theorem scaledCoeffs_eq (b : Matrix Int n m)
    (i j : Nat) (hi : i < n) (hj : j < i) :
    (scaledCoeffs b)[i][j] =
      gramDet b (j + 1) (by omega) * (coeffs b)[i][j]

theorem normSq_latticeVec_ge_min_basis_normSq
    (b : Matrix Int n m) (hli : b.independent)
    (v : Vector Int m) (hv : b.memLattice v) (hv' : v ≠ 0) :
    ∃ i, i < n ∧
      ((basis b).row i).dotProduct ((basis b).row i) ≤
        (v.dotProduct v : Rat)
```

**Update formulas under row operations:**
- Size reduction (`b_k ← b_k - r * b_j`, `j < k`): GS basis unchanged,
  coefficients update as `coeffs[k][j] ← coeffs[k][j] - r`.
- Swap (`b_k ↔ b_{k-1}`): explicit formulas for new basis, coefficients,
  and Gram determinants (see hex-lll section for the full formulas).

**Integrality of scaledCoeffs.** (Von zur Gathen & Gerhard, Lemma 16.7.)
scaledCoeffs[i][j] = gramDet (j+1) * coeffs[i][j] can be expressed as
a (j+1) × (j+1) determinant: take the Gram matrix G_{j+1} and replace
its last column (inner products with b[j]) by inner products with b[i]:

    scaledCoeffs[i][j] = det | <b[0],b[0]>  ...  <b[0],b[j-1]>   <b[0],b[i]> |
                              | <b[1],b[0]>  ...  <b[1],b[j-1]>   <b[1],b[i]> |
                              |   ...        ...    ...            ...       |
                              | <b[j],b[0]>  ...  <b[j],b[j-1]>   <b[j],b[i]> |

Since all inner products are integers, this determinant is an integer.
(The formula follows from Cramer's rule on G_{j+1} * x = g, where g
is the column of inner products with b[i]: coeffs[i][j] =
det(G_{j+1} with last column replaced) / gramDet (j+1). Multiplying by
gramDet (j+1) gives the integer determinant above.)

**Why divisions are exact under swap.** scaledCoeffs[i][j] =
gramDet (j+1) * coeffs[i][j] and the coeffs values are always
expressible as ratios of integer determinants with denominator
gramDet (j+1). After a swap, the new coeffs values have the same
property with the new gramDet values. The algebraic identities can
also be verified directly by substituting the definitions and using
the fact that Gram determinants of sub-lattices are always integers.

**File organization:**
- `GramSchmidt.lean` — definitions, orthogonality, span, decomposition,
  lower bound lemma
- `GramSchmidtUpdate.lean` — how GS quantities change under size
  reduction (unchanged) and swap (explicit update formulas)
- `GramSchmidtInt.lean` — `scaledCoeffs`, integrality, `gramDetVec`,
  exact division under swap

Mathlib's `gramSchmidt` works over inner product spaces and does not
track coefficients or update formulas, so it cannot be used in the
computational core. The `hex-gram-schmidt-mathlib` bridge proves
that `GramSchmidt.Int.basis` corresponds to Mathlib's `gramSchmidt`.

**Mathlib-free vs. Mathlib-bridge proof surface.** Theorems in
`hex-gram-schmidt` (the Mathlib-free integer/rational GS core) may
state equalities between:

- Hex-local recurrences and their executable implementations
  (e.g. `scaledCoeffRows_diag_eq_gramDetVecEntry` — diagonal writes
  of the shared Bareiss pass agreeing with `gramDetVecEntry`);
- Hex computational outputs and other Hex computational outputs
  (e.g. `scaledCoeffs` and `scaledCoeffMatrix` as packagings of the
  same Bareiss data).

They may **not** state equalities between Hex computational outputs
and the Leibniz `det` of any (sub)matrix. That includes `gramDet`,
`scaledCoeffs`, the executable Bareiss output, the leading
principal minor determinants, and any update formula expressed at
the level of `Hex.det`. Theorems of that shape live in
`hex-gram-schmidt-mathlib`, because their shortest proof goes
through `Matrix.bareiss_eq_det` (see
[hex-matrix.md "Mathlib-free vs. Mathlib-bridge proof surface"](hex-matrix.md)),
which itself lives in `hex-matrix-mathlib`.

Symptom this boundary exists to catch: a Mathlib-free
`HexGramSchmidt/Int.lean` theorem of the form
`<Hex computational output> = Matrix.det <matrix>` that chains
through `Matrix.bareiss_eq_det`. Such a theorem belongs in
`HexGramSchmidtMathlib/Int.lean` (or the analogous bridge file),
not in the Mathlib-free core.

**Proof path governs placement, not just statement.** Theorems
whose *statement* is purely Hex-local but whose only realistic
proof goes through `Matrix.bareiss_eq_det` (directly, or via a
renamed `bareiss`-invariance lemma that secretly re-derives
Desnanot–Jacobi) also belong in `hex-gram-schmidt-mathlib`.
Concretely, `gramDet_sizeReduce`,
`scaledCoeffs_sizeReduce_pivot`, and `gramDet_rowAdd_earlier` state
equalities between Hex computational outputs — Hex-local by
statement — but their natural proofs cross to the bridge. They
live in the bridge layer. See
[hex-matrix.md "Proof path governs placement, not just statement"](hex-matrix.md)
for the analogous rule on the matrix side.

## External comparators

No external comparator is required.

**Justification:** `structural-layer` per
[the benchmarking spec's "Comparator naming" section](https://github.com/kim-em/hex-dev/blob/main/SPEC/benchmarking.md#comparator-naming). HexGramSchmidt is a
structural layer over `HexMatrix`: the integer Gram-Schmidt
construction is implemented via the per-row Schur-complement
recurrence specified for `scaledCoeffs` above, with the diagonal
emitted as `d_{k+1} = scaledCoeffs[k][k]` for `gramDetVec`. The
underlying integer arithmetic and inner-product primitives come
from HexMatrix; HexMatrix's external comparator declaration
(`FLINT fmpz_mat_det`, scoped to the determinant surface) covers
the determinant computation that the recurrence's diagonal
produces.

End-to-end coverage of the integer Gram-Schmidt construction as
it appears in downstream consumers is via HexLLL's `gating`
comparator (the verified Isabelle LLL Haskell extraction), which
exercises `LLLState.ofBasis` — itself a thin wrapper around the
GS construction — under its end-to-end ratio measurement. No
distinct external tool exposes an integer Gram-Schmidt
construction at the level of abstraction HexGramSchmidt operates
on; the within-Lean linkage to HexMatrix and HexLLL covers the
coverage gap.
