# Arm-3 concrete proof DAG (#8417) — `bhksSingleAllOnesPartition ⇒ irreducible`

Goal lemma `latticeArm3_bhksSingleAllOnes_irreducible`:
`core := (normalizeForFactor f).squareFreeCore`, `d := toMonicLiftData core B primeData`,
`p := primeData.p`, `k := d.k`, `r := d.liftedFactors.size`, `n := core.degree?.getD 0`.
```
(hprec : bhksBound core ≤ p^k)          -- PRECISION (was missing → unsound without it)
(hchoose) (hdeg_ne) (core facts) →
bhksSingleAllOnesPartition core d = true → Irreducible (toPolynomial core)
```
**Premise fix (step 0, do first):** add `hprec` to `latticeArm3_...` and to the
unconditional `latticeCoreFactorsWithBound_squareFreeCore_factor_zpolyIrreducible`
(discharge later from `factorFastPrecisionCap` at the `factorLattice` call site via
`bhksBound_le_factorFastPrecisionCap` + `bhksBound core ≤ bhksBound f` monotonicity).

## Proof by contraposition
core reducible → ∃ proper nonempty true-factor support `S` → the indicator+CLD
vector `w_S` is a SHORT lattice vector → the LLL-reduced-within-cut basis has
rank ≥ 2 → `bhksEquivalenceClassIndicators` ≠ single all-ones class → `false`.

## Definitions to add (HexBerlekampZassenhausMathlib/LatticeAdequacy.lean)
- `D1 trueFactorLatticeVector core d S : Fin (r+n) → ℤ` — indicator of `S` in the
  first `r` coords; last `n` coords = `-(aggregateCldTail f p k · / p^?)`… i.e. the
  integer row-combination of `bhksLatticeBasis.basis` selecting rows `i∈S` and
  reducing the CLD tail mod `p^k` via the D-rows. Concretely: `w_S = Σ_{i∈S} row_i
  - Σ_j q_j · row_{r+j}` for integer `q_j` making the tail centred. It lies in
  `latticeSubmodule basis` by construction (integer combo of rows).

## Lemma DAG (leaves → root)

### CLD / number theory (the heart — greenfield)
- `L1 cldQuotientMod_eq_polyDivMod` (EASY-ish): `toPolynomial (cldQuotientMod f g p a)`
  ≡ `toPolynomial ((f·g'/g) numerator divMod g).1 mod p^a`. Bridge executable
  `cldQuotientMod` to Mathlib `Polynomial.divModByMonic`. Uses existing
  `cldQuotientMod_divMod_reconstruction` (Basic.lean:4802).
- `L2 trueFactor_cld_eq_cofactorDeriv` (MED): for `g' | f` in ℤ[x] (true factor),
  `f·(g')'/g' = (f/g')·(g')'` ∈ ℤ[x] (poly, no denominator). Mathlib polynomial algebra.
- `L3 trueFactor_cldCoeff_bound` (MED): `|[x^j]((f/g')·(g')')| ≤ bhksCoeffBound f j`
  — Landau-Mignotte on the cofactor·derivative. Feeds the WITNESS `y` for the
  proven `Hex.BHKS.abs_cldCoeffs_le_bhksCoeffBound` (Basic.lean:5199).
- `L4 trueFactor_cldCoeffs_bounded` (from L1-L3): the executable `cldCoeffs f p k
  (subsetProduct S)` entries are ≤ `bhksCoeffBound f j` at adequate precision.

### Lattice geometry
- `L5 trueFactorVector_mem_lattice` (MED, linear algebra): `w_S ∈ latticeSubmodule
  (bhksLatticeBasis core p k liftedFactors).basis` — integer combo of basis rows.
- `L6 trueFactorVector_norm_sq_le_cut` (from L4): `‖w_S‖² ≤ bhksCutRadiusSq4/4`
  (indicator part ≤ r, CLD tail bounded by L4). Short vector.
- `L7 short_lattice_vectors_in_reducedCut` (HARD, greenfield = Klüners Lemma 1):
  every lattice vector with `‖v‖² ≤ radius` lies in the span of the reduced rows
  passing `bhksWithinGramSchmidtCut`. **No existing HexLLL lemma** — must build
  from `teleBound`/`stepBound` (Reduced.lean:173/134) + Gram-Schmidt theory.
- `L8 reducedCut_rank_ge_two_of_properSubset` (from L5,L6,L7): a proper nonempty
  `S` gives `w_S`, `w_univ` independent in the cut-span → rank ≥ 2.

### Equivalence classes = partition
- `L9 singleAllOnes_iff_cutSpan_rank_one` (MED, ℚ-linear algebra on
  `bhksEquivalenceClassIndicators` / `bhksProjectedRowsAsRatMatrix` rowReduce):
  `bhksSingleAllOnesPartition = true ↔ projected cut-span is the all-ones line`.

### Reducibility → proper support (reuse #8413)
- `L10 reducible_imp_properTrueSupport` (MED, reuse `LiftedFactorSubsetPartition`
  cover/pairwise_disjoint + `liftedFactorSubsetPartition_of_toMonicPrimeData_complete`):
  core reducible → ∃ proper nonempty `S ∈ liftedTrueSupports core d`.
  (This is arm-3a's content, reused.)

### Root
- `latticeArm3`: contrapose; L10 gives proper `S`; L5+L6 make `w_S` short lattice
  vector; L7+L8 give cut-rank ≥ 2; L9 gives `bhksSingleAllOnesPartition = false`.
  Contradiction.

## Execution order (leaves first, provable-now first)
1. Step 0: add `hprec` precision hypothesis (correctness) — DO NOW.
2. L1 (cldQuotientMod bridge) — concrete, uses existing reconstruction.
3. L5 (trueFactorVector_mem_lattice) — concrete linear algebra.
4. L10 (reducible → proper support) — reuse #8413 machinery.
5. L2,L3,L4 (CLD Landau-Mignotte) — the number-theoretic heart.
6. L9 (single-all-ones ↔ rank one) — ℚ linear algebra.
7. L7,L8 (Klüners Lemma 1 + rank) — hardest greenfield LLL.
8. Assemble root.

## Arm-3 proof STRUCTURE landed (top-down, compiling)
`latticeArm3_bhksSingleAllOnes_irreducible` now has the real proof body:
convert to Mathlib `Irreducible (toPolynomial core)` → reduce to
`(normalizedFactors …).card = 1` → split `hge` (≥1, easy UFM) + `hle` (≤1, deep)
→ `hle` contraposes (`2 ≤ card`) to ONE concrete deep lemma
`hfalse : bhksSingleAllOnesPartition core (toMonicLiftData core B primeData) = false`.
Remaining sorries: `hge` (easy), `hfalse` (the L5–L10 geometry), and the final
`card = 1 → Irreducible` (easy UFM). Next: expand `hfalse`.

### `hfalse` expansion plan (≥2 factors ⇒ certificate false)
1. `2 ≤ card` → proper irreducible factor `pg | core`, `0 < deg pg < deg core`.
2. `pg` → proper nonempty true-factor support `S` (partition machinery, L10).
   **BLOCKED on the prime-data premise below unless core is monic.**
3. `S` → short lattice vector `w_S ∈ latticeSubmodule bhksLatticeBasis.basis`
   with `‖w_S‖² ≤ bhksCutRadiusSq4/4` (L5+L6, CLD bound).
4. `w_S`, `w_univ` two independent short vectors → reduced cut rank ≥ 2
   (L7 Klüners Lemma 1, foundations = GramSchmidt.Int.exists_top_index_normSq_le_of_memLattice
   + my `bhksLatticeBasis_lllNative_first_row_short`).
5. cut rank ≥ 2 → `bhksEquivalenceClassIndicators` ≠ single all-ones (L9).

## CRITICAL PREMISE (verify before/within arm-3)
The lattice tier passes `primeData = choosePrimeData? core` (core's mod-p
factorisation) into `toMonicLiftData core B primeData`, whose `henselLiftData`
lifts `primeData.factorsModP` as factors of `(toMonic core).monic`.  These match
only when `core` is MONIC (`toMonic core = core`).  The classical tier instead
uses `toMonicPrimeData? core = choosePrimeData? (toMonic core).monic` — the
consistent choice.  For the SD/cyclotomic showcase inputs `core` is monic, so the
executable is sound there (#guards pass).  For a general non-monic primitive
`core` there is a genuine consistency gap: either (a) prove
`choosePrimeData? core = toMonicPrimeData? core` under the lattice's hypotheses,
(b) add a monic-core hypothesis to `latticeArm3`, or (c) treat this as an
executable bug to fix (lattice should select `toMonicPrimeData?`).  RESOLVE THIS
before completing L10 — it decides whether `latticeArm3` is provable as stated.

## Already proven (this PR)
- Basis independence + LLL first-row-short (the engine for L7).
- Reduction skeleton (arm 1) + top-down structure.

## UPDATE (2am autonomous session): prime-data "bug" is NOT a blocker
Compiled #guard test: `factorLattice` on non-monic reducibles `2x^3+3x^2+3x+1`
and `3x^3+x^2+6x+2` returns the correct 2 factors with correct product. So the
`choosePrimeData? core` + `toMonicLiftData core B primeData` combination is
reconciled (the dilate machinery in the recovery relates monic-core lifted
factors back to core factors). The coordinate is handled; NO executable fix
needed. Proceed with the geometry using the `choosePrimeData?` partition
(`liftedFactorSubsetPartition_of_choosePrimeData`, Basic.lean:20335) or the
toMonicPrimeData? complete version, reconciled via the monic relationship.
Grinding arm-3 `hfalse` geometry top-down, hardest sub-lemma first.
