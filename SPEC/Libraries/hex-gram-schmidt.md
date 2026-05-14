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
    Computed in a single Bareiss-style integer pass shared across all
    entries, reusing the same elimination scaffolding as `gramDetVec`:
    O(n^3 + n^2 m) total. Computing each below-diagonal entry
    independently as a (j+1) × (j+1) Bareiss determinant is forbidden —
    that body is `O(n^5)`. -/
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
`SPEC/benchmarking.md §"Comparator naming"`. HexGramSchmidt is a
structural layer over `HexMatrix`: the integer Gram-Schmidt
construction is implemented via Bareiss-style fraction-free
elimination on the Gram matrix (`Matrix.bareissNoPivotData`),
which is HexMatrix's own architecturally-named surface and is
covered by HexMatrix's external comparator declaration
(`FLINT fmpz_mat_det`, scoped to the determinant surface).

End-to-end coverage of the integer Gram-Schmidt construction as
it appears in downstream consumers is via HexLLL's `gating`
comparator (the verified Isabelle LLL Haskell extraction), which
exercises `LLLState.ofBasis` — itself a thin wrapper around the
GS construction — under its end-to-end ratio measurement. No
distinct external tool exposes an integer Gram-Schmidt
construction at the level of abstraction HexGramSchmidt operates
on; the within-Lean linkage to HexMatrix and HexLLL covers the
coverage gap.
