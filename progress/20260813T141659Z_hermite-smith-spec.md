# Hermite and Smith normal form SPECs

## Accomplished

Wrote two library SPECs, starting from the two paragraph-length sketches
in `SPEC/future-work.md`:

- `SPEC/Libraries/hex-hermite.md`: Hermite normal form over `Int`. Fixes
  the row-style convention, the `IsHNF` contract, the `extGcd` 2x2
  elimination step with its explicit inverse, the entry-growth analysis
  and the algorithm choice that follows from it (Kannan-Bachem by
  default, Domich-Kannan-Trotter modulo the determinant for square
  nonsingular input), the API (`hnf`, `hnfData`, `latticeCoeffs`,
  `kernelBasis`, `latticeIndex`), the correctness theorems, the
  certificate, the Mathlib layer, conformance, and benchmarking with two
  thresholds written down in advance.
- `SPEC/Libraries/hex-smith.md`: Smith normal form over `Int`. The
  `SmithData` / `IsSNF` contract, the pivot loop with its lexicographic
  termination measure, the diagonal fast path with explicit unimodular
  matrices, the determinantal-divisor route to uniqueness,
  `abelianStructure` / `solveInt` / `invariantFactors`, and the Mathlib
  layer.

Both name their prerequisite changes in other libraries and both record
what is deliberately out of scope.

Updated `SPEC/Libraries/README.md` (descriptions, both dependency lists,
index) and replaced the two `SPEC/future-work.md` sketches with a pointer
plus the two corrections found while writing.

## Findings that changed the design

- **`IsEchelonForm` and `IsRowReduced` do not force the declared pivot to
  be the leading nonzero entry of its row.** Machine-checked
  counterexample: the 1x2 matrix `[[5, 1]]` with `rank = 1`, pivot column
  `1`, and the identity transform satisfies every field of
  `IsRowReduced`. So `IsHNF` has to state the leading-entry condition
  itself, or uniqueness is false. The counterexample is reproduced in the
  hex-hermite SPEC and elaborates against the current tree.
- **`det transform = ±1` is a theorem, not a field.**
  `IsEchelonForm.transform_inv` plus `det_mul` (already Mathlib-free in
  `HexDeterminant/Adjugate.lean`) gives it. The future-work sketch listed
  it as an `IsHNF` field and omitted the leading-entry condition, so its
  clause list was wrong in both directions.
- **`hex-lll` already has the certificate machinery.**
  `Hex.Internal.mulEqCert` (packed product check with `mulEqCert_iff`)
  and `Hex.Matrix.sameLatticeCert` are exactly what a unimodular
  certificate needs. `Hex.Matrix.memLattice` and its transport lemmas
  live in `HexLLL/Lattice.lean` but mention nothing from `hex-lll`. Both
  SPECs ask for those to move to `hex-matrix` so `hex-hermite` does not
  acquire a dependency on `hex-lll` to say "is an integer combination of
  the rows".
- **The Hermite and Smith certificates are complete**, unlike most items
  in `future-work.md`: by uniqueness, an accepted candidate is the
  answer, so no second witness is needed and certified dispatch to an
  external implementation is available in the shape `hex-lll`'s
  `certCheck` already uses.
- **Mathlib has no Hermite normal form for matrices, no invariant
  factors, and no determinantal divisors**, and its
  `Module.Basis.SmithNormalForm` carries no divisibility chain. So the
  Mathlib layer is new content rather than a transport, and the
  executable libraries would be the only source of canonicity.

## Second opinion, and what it changed

Codex (gpt-5.6-sol, read-only, full repo access) reviewed both drafts
adversarially and returned 17 findings. It endorsed the two-library
split, and did not dispute the `IsRowReduced` counterexample, the
`det = ±1` derivation, the `memLattice` / `mulEqCert` relocation, the
Mathlib gaps, or extending `matrix_flint.py`. Eight findings were real
errors and are now fixed:

- **The modular HNF argument was wrong as written.** `d·ℤⁿ ⊆ L` gives
  `L + d·ℤⁿ = L`; it does not license reducing a generator modulo `d`.
  For `A = [2]`, `d = 2`, the row `[2]` reduces to `[0]`. The SPEC now
  states Domich-Kannan-Trotter as the recurrence on `[A; d·I]`, notes
  that a pivot may equal `d` (so entries live in `[0, d]`), and carries
  the counterexample and a conformance case for it.
- **Full column rank, not full row rank**, is the condition for the
  modular path: the row lattice sits in `ℤᵐ` and needs finite index
  there. `latticeIndex` is generalised to `n × m` accordingly.
- **The Smith default was misnamed.** The five-step pivot loop is the
  classical Euclidean algorithm, not Kannan-Bachem, and does not inherit
  its entry bounds. Renamed, bound claim withdrawn, Kannan-Bachem moved
  to an open question with the growth instrumentation as its evidence.
- **The Smith termination measure did not decrease at step 4.** Adding a
  row to the pivot row leaves `|pivot|` fixed and raises the second
  component. Step 4 is now fused with the following elimination, so the
  recursive call happens only after `gcd(p, a) < |p|`.
- **`detDivisor` was circular**: described as the gcd of minors but
  "computed through `snf`", which would put the SNF output inside the
  invariant used to prove it canonical. Now defined by the enumeration
  alone, returning `Nat`, with `D₀ = 1` and `D_k = 0` past the rank.
- **The uniqueness theorem could not prove rank equality**, being stated
  only for `k ≤ S.rank`, which is exactly where the discriminating value
  `k = S.rank + 1` is out of scope. Restated for all `k`.
- **Hermite canonicity is per shape.** `hnf A` keeps its zero rows, so
  `[1]` and `[[1], [0]]` have forms of different types. Added `hnfBasis`
  (the nonzero rows) as the presentation-independent object, and
  qualified the claims about `hnf`.
- **`solveInt` omitted the right-hand-side transform.** From
  `S = U A V`, solving `x A = b` means solving `z S = b V` and returning
  `x = z U`.

Also corrected: the claim that `hex-bareiss` divides with `Int.divExact`
(it uses a proof-free `exactDiv` with `exactDiv_eq_divExact` proved
separately, which is the design to copy, and the primitive should move to
`hex-arith`); the PARI convention conversion (reversal matrices, not "a
transpose and a reverse"); `snfDiagonal` accepting zeros and negatives
without a normalisation phase; and the complexity tables, now labelled
matrix-update counts and parameterised by the pivot-loop repetition
count. Benchmark thresholds are now curves over a named range rather than
single-endpoint ratios.

**Codex resolved the one question this SPEC left open.** The general
rectangular Cauchy-Binet needed for determinantal-divisor invariance is
not derivable from what exists: `Minor.lean` has only `deleteRowCol`,
`CauchyBinet.lean` selects `n` columns from an `n`-row matrix, and
`Submatrix.lean` takes prefixes. Verified directly. So `hex-determinant`
needs selected submatrices by index maps, `k`-subset enumeration, and
Cauchy-Binet for a selected minor, and Smith uniqueness cannot be
scheduled before that lands.

## Current frontier

The SPECs are drafts. Neither library is in `libraries.yml`; each SPEC
carries the `yaml` block it would add, following the `hex-mv-poly`
precedent for a draft SPEC.

## Next step

The sequencing the review argued for, which is now what both SPECs say:

1. Four prerequisite relocations, each independently justified and each
   doable before any Hermite commit: `memLattice` and the certificate
   checkers from `hex-lll` to `hex-matrix`, `mulEqCert` out of
   `Hex.Internal`, `mul_eq_one_comm` into `hex-determinant`, and
   `exactDiv` from `hex-bareiss` into `hex-arith`.
2. Implement and prove Hermite normal form.
3. Add selected submatrices, `k`-subset enumeration, and rectangular
   Cauchy-Binet to `hex-determinant`.
4. Define determinantal divisors and prove the all-`k` characterisation.
5. Implement Smith normal form with transforms.
6. Leave both modular variants (DKT, Iliopoulos) until the native paths
   are complete and the benchmarks say they earn their place.

## Blockers

None.
