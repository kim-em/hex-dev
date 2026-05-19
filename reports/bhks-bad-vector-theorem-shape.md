# BHKS bad-vector theorem shape

Scope: shape the next BHKS Lemma 3.2 / Theorem 5.2 theorem statements for
directive #2567 in terms of names that already exist in the repo, so
implementation issues can be sized correctly.

The auditing work on `Polynomial.resultant` (PR #5187) and the executable
`bhksBound` arithmetic packaging (PR #5191) have both landed, so no Mathlib
port is in the critical path. The remaining work is the
`L' \ W` bad-vector lower bound and its arithmetic comparison with the
LLL cut radius.

## 1. Notation mapping

BHKS §3.2 / §5 names on the left; Lean names on the right. "Type" is the
proof-facing type when the project distinguishes one; absent for purely
proof-facing notions.

| BHKS notation | Project name | Type | Location |
|---|---|---|---|
| Input `f` (degree `n`) | `Hex.ZPoly` (executable) / `HexPolyZMathlib.toPolynomial f` (proof) | `Hex.ZPoly` / `Polynomial ℤ` | `HexBerlekampZassenhaus/Basic.lean`, `HexPolyZMathlib/` |
| `deg f` (= `n`) | `bhksDegree f` (proof) / `f.degree?.getD 0` (executable) | `Nat` | `HexBerlekampZassenhausMathlib/BHKSBound.lean:27`, `HexBerlekampZassenhaus/Basic.lean` |
| `‖f‖₂` | `HexPolyZMathlib.l2norm (HexPolyZMathlib.toPolynomial f)` | `ℝ` | `HexPolyZMathlib/Mignotte.lean:31` |
| `r` (number of lifted local factors) | `liftData.liftedFactors.size`, `lattice.factorCount`, `projectedRows.factorCount` | `Nat` | `HexBerlekampZassenhaus/Basic.lean` (`LiftData`, `BhksLatticeBasis`, `BhksProjectedRows`) |
| Lifted factors `g_1, …, g_r ∈ (ℤ/p^a)[x]` | `liftData.liftedFactors : Array ZPoly` (centred-residue lifts kept in `ZPoly`) | `Array Hex.ZPoly` | `HexBerlekampZassenhaus/Basic.lean` (`LiftData`) |
| Prime `p` | `liftData.p` | `Nat` | same |
| Hensel precision `a` | `liftData.k` (kept as `k` in the executable; the bridge files use `a` in stated obligations to match BHKS) | `Nat` | same |
| Per-coordinate precision `ℓ_j` | `bhksCoeffCutThreshold p f j` (single), `bhksCutThresholds f p` (array) | `Nat`, `Array Nat` | `HexBerlekampZassenhaus/Basic.lean:2245`, `:3954` |
| Per-coordinate coefficient bound `B_j = C(n-1, j) · n · ‖f‖₂` | `bhksCoeffBound f j` | `Nat` | `HexBerlekampZassenhaus/Basic.lean:2219` |
| Two-sided centred cut `Ψ^a_b(x)` | `psiCut p a b x` (executable) | `Int` | `HexBerlekampZassenhaus/Basic.lean` |
| CLD invariant `Φ(g) = f · g'/g (mod p^a)` (raw) | `cldQuotientMod f g p a` (private) | `Hex.ZPoly` | `HexBerlekampZassenhaus/Basic.lean:3934` |
| Centred high-bit CLD coefficients `Ψ^a_{ℓ_j}([x^j] Φ(g_i))` | `cldCoeffs f p a g` (per-factor), `lattice.cldRows` (all factors stacked) | `Array Int`, `Array (Array Int)` | `HexBerlekampZassenhaus/Basic.lean:3946`, `:3972` |
| Lattice basis `[ I_r ∣ Ã ; 0 ∣ diag(p^{a−ℓ_j}) ]` (BHKS eq. 5.1) | `bhksLatticeBasis f p a liftedFactors` returning `BhksLatticeBasis` with `basis : Matrix Int (r+n) (r+n)` | `BhksLatticeBasis` | `HexBerlekampZassenhaus/Basic.lean:4012` |
| Projected lattice `L' ⊆ ℤ^r` (BHKS Step 7) | Integer rows: `projectedRows.projectedRows : Array (Array Int)`; as a Mathlib submodule: `BHKS.projectedRowSpanInt projectedRows : Submodule ℤ (Fin r → ℤ)` | `BhksProjectedRows` / `Submodule ℤ (Fin r → ℤ)` | `HexBerlekampZassenhaus/Basic.lean:3981`, `HexBerlekampZassenhausMathlib/Lattice.lean:33` |
| Rational row space of `L'` (RREF stage input) | `BHKS.projectedRowSpaceRat projectedRows : Submodule ℚ (Fin r → ℚ)` | same | `HexBerlekampZassenhausMathlib/Lattice.lean:42` |
| True-factor indicator lattice `W ⊆ ℤ^r` | `BHKS.trueFactorIndicatorLattice trueSupports : Submodule ℤ (Fin r → ℤ)` (where `trueSupports : Set (Set (Fin r))` is the abstract set of true-factor supports over the lifted-factor indices) | `Submodule ℤ (Fin r → ℤ)` | `HexBerlekampZassenhausMathlib/Lattice.lean:80` |
| Indicator vector of a support | `BHKS.indicatorVector S : Fin r → ℤ` | `Fin r → ℤ` | `HexBerlekampZassenhausMathlib/Lattice.lean:52` |
| `W ⊆ L'` (BHKS Lemma 5.7 + projection) | `BHKS.trueFactorIndicatorLattice_le_projectedRowSpan` | theorem | `HexBerlekampZassenhausMathlib/Lattice.lean:282` |
| LLL cut radius `B'` (`B'² = r + n · (r/2)²`) | Stored squared and pre-scaled by four: `bhksCutRadiusSq4 L = 4r + n · r²` (= `projectedRows.cutRadiusSq4`) | `Nat` | `HexBerlekampZassenhaus/Basic.lean:4096`, `:3984` |
| Bad-vector polynomial `H_v` (BHKS Lemma 3.2 construction) | `BHKS.auxiliaryPolynomial input liftData vec : Hex.ZPoly` (vec is the integer projected vector packaged as `Array Int`) | `Hex.ZPoly` | `HexBerlekampZassenhausMathlib/BadVector.lean:298` |
| `H_v` transported to `Polynomial ℤ` (resultant input) | `ExecutableBadVectorWitness.auxiliaryPolynomial W` | `Polynomial ℤ` | `HexBerlekampZassenhausMathlib/BadVector.lean:199` |
| Selected local factor `f_i` and its degree `d` from the bad-vector argument | `W.selectedLiftedFactor`, `W.localFactorDegree` | `Hex.ZPoly`, `Nat` | `HexBerlekampZassenhausMathlib/BadVector.lean:203`, `:184` |
| Integer resultant `Res(f, H_v)` | `Polynomial.resultant W.inputPolynomial W.auxiliaryPolynomial` | `ℤ` | upstream `Mathlib.RingTheory.Polynomial.Resultant.Basic`; bridge in `HexBerlekampZassenhausMathlib/Resultant.lean` |
| Modular divisibility `p^(a·d) ∣ Res(f, H_v)` | `IsBhksBadVectorSetup.resultant_divisible_by_p_pow` (field) | hypothesis | `HexBerlekampZassenhausMathlib/BadVector.lean:398` |
| Hadamard upper bound `|Res(f, H)| ≤ ‖f‖₂^(deg H) · ‖H‖₂^n` | `HexBerlekampZassenhausMathlib.abs_resultant_le_l2norm_pow` and the record-shaped wrapper `BadVectorResultantData.abs_resultant_le_l2norm_pow` | theorem | `HexBerlekampZassenhausMathlib/Resultant.lean:191`, `BadVector.lean:81` |
| Rational coprimality `gcd(f, H_v) = 1` over `ℚ` | `IsBhksBadVectorSetup.coprime_input_aux_over_rat` (field) | hypothesis | `HexBerlekampZassenhausMathlib/BadVector.lean:395` |
| BHKS Theorem 5.2 paper threshold `c · n · (2C)^(n²) · ‖f‖₂^(2n−1) · (log ‖f‖₂)^n` | `bhksPaperThresholdReal f C` | `ℝ` | `HexBerlekampZassenhausMathlib/BHKSBound.lean:167` |
| Mignotte coefficient bound | `Hex.ZPoly.defaultFactorCoeffBound f` | `Nat` | `HexPolyZ/Mignotte.lean` |
| Public fast-path precision cap `max (bhksBound f) (defaultFactorCoeffBound f)` | `Hex.factorFastPrecisionCap f` | `Nat` | `HexBerlekampZassenhaus/Basic.lean` |

The deliberate gap in the table is the *norm lower bound on `v` itself*:
the existing `BadVector.lean` packages the resultant-side contradiction
(modular divisibility lower bound vs Hadamard upper bound), but it does not
yet expose a theorem of the shape

  `v ∈ L' \ W ⟹ ‖v‖₂ ≥ G(a)`

with `G(a) → ∞` as `a → ∞`. That is the BHKS Lemma 3.2 conclusion as
written in the paper, and it is the missing surface between the existing
resultant-bound pair and BHKS Theorem 5.2's separation argument
(`‖v‖₂ > B'` once `a` exceeds the paper threshold).

## 2. Proposed Lean theorem statement

Target theorem. The shape is dictated by directive #2567 step 2 of the D1
pathway in `SPEC/Libraries/hex-berlekamp-zassenhaus.md`:

```lean
namespace HexBerlekampZassenhausMathlib.BHKS

/-- BHKS Lemma 3.2 (bad-vector size lower bound).

For any executable bad-vector setup `h_bad : IsBhksBadVectorSetup W`, the
underlying integer vector `bhksVector` (the witness's projected vector
packaged as `Array Int`) has Euclidean norm bounded below by a function
of `a := W.liftData.k` that grows without bound in `a`.

In the form used by the BHKS Theorem 5.2 cut comparison: there exists a
real lower bound `lower : ℝ` such that `lower ≤ ‖bhksVector‖₂²` and
`lower` is monotone non-decreasing in `a` with `lower ≥ B'^2 + 1` once
`a ≥ paperThreshold W.input C` for any project constant `0 ≤ C ≤ 2`. -/
theorem bhks_bad_vector_norm_sq_lower_bound
    (W : ExecutableBadVectorWitness)
    (h_bad : ExecutableBadVectorWitness.IsBhksBadVectorSetup W)
    (hp : 0 < W.liftData.p) :
    -- TBD: exact functional shape of the lower bound. The driving
    -- inequality is the resultant-side comparison
    -- `(W.liftData.p ^ (W.liftData.k * W.localFactorDegree) : ℝ)`
    -- ≤ `(l2norm W.inputPolynomial) ^ W.auxiliaryPolynomial.natDegree`
    -- × `(l2norm W.auxiliaryPolynomial) ^ W.inputPolynomial.natDegree`
    -- with `l2norm W.auxiliaryPolynomial` controlled by `‖bhksVector‖₂`
    -- through the linear-combination form of
    -- `BHKS.auxiliaryPolynomial`.
    True
```

The exact RHS will be fixed during implementation; the constraints on its
shape are:

1. It must be expressible using existing project names. The current names
   suffice: `IsBhksBadVectorSetup` packages the modular divisibility and
   rational coprimality, `auxiliaryPolynomial` is the linear combination
   construction, `l2norm` is the existing real-valued Euclidean norm.
2. The lower bound's `a`-dependence must dominate `bhksCutRadiusSq4` once
   precision crosses `bhksPaperThresholdReal W.input C` (project constant
   `0 ≤ C ≤ 2`).
3. The conclusion must compose with the existing
   `BHKS.no_projected_not_indicator_of_factorFastPrecisionCap_le`
   contradiction chain in `TerminationBound.lean` without restating the
   resultant inequality.

The implementation likely factors as:

```lean
/-- Auxiliary polynomial norm bound: `‖H_v‖₂` is controlled by `‖v‖₂`
times a `f`-only factor coming from the centred-CLD column bounds
(`bhksCoeffBound`).  The constant `cldColumnNormBound input liftData.p`
packages `Σ_j B_j^2` for the per-coordinate cut-bound `B_j` from
`bhksCoeffBound`. -/
theorem auxiliaryPolynomial_l2norm_sq_le
    (input : Hex.ZPoly) (liftData : Hex.LiftData) (vec : Array Int) :
    (HexPolyZMathlib.l2norm
        (HexPolyZMathlib.toPolynomial
          (BHKS.auxiliaryPolynomial input liftData vec))) ^ 2 ≤
      (∑ i : Fin liftData.liftedFactors.size,
        ((vec.getD i.val 0 : ℝ) ^ 2)) *
      cldColumnNormBound input liftData.p := by
  sorry  -- placeholder: Cauchy–Schwarz over the linear combination
```

`cldColumnNormBound` is the missing helper: `Σ_j (bhksCoeffBound input j)^2`
as a `Nat` (or its `ℝ` cast). Its definition is one line and can be
introduced in the same issue, or pulled in as a tiny preliminary lemma.

```lean
/-- BHKS Lemma 3.2 (norm lower bound).  The integer-resultant divisibility
clause forces `‖v‖₂²` to grow at least like `(p^(k·d) / ‖f‖₂^(deg H_v))^{2/n}`,
in particular the squared norm exceeds the BHKS cut radius squared
`bhksCutRadiusSq4 W.lattice` once `k` reaches the paper threshold. -/
theorem bhks_bad_vector_norm_sq_gt_cutRadiusSq4_of_paperThreshold_le
    (W : ExecutableBadVectorWitness)
    (trueSupports : Set (Set (Fin W.projectedRows.factorCount)))
    {a : Nat} (ha : Hex.factorFastPrecisionCap W.input ≤ a)
    (C : ℝ) (hC_nonneg : 0 ≤ C) (hC : C ≤ 2)
    (h_bad : ExecutableBadVectorWitness.IsBhksBadVectorSetup W)
    (hp : 0 < W.liftData.p)
    (hk : W.liftData.k = a) :
    (W.projectedRows.cutRadiusSq4 : ℝ) <
      ∑ i : Fin W.projectedRows.factorCount,
        ((W.projectedVectorFn h_bad.bhksVector i : ℝ) ^ 2) := by
  sorry
```

This is the canonical "norm grows with `a`" conclusion, in the form that
the LLL-cut radius comparison consumes directly. The `cutRadiusSq4` form
avoids the square root that the executable layer also avoids.

A simpler intermediate target — useful for landing the algebraic core
before the cut-radius comparison — is the real-valued resultant chain
form, where both sides are already real:

```lean
theorem bhks_bad_vector_resultant_lower_bound
    (W : ExecutableBadVectorWitness)
    (h_bad : ExecutableBadVectorWitness.IsBhksBadVectorSetup W)
    (hp : 0 < W.liftData.p) :
    (W.liftData.p ^ (W.liftData.k * W.localFactorDegree) : ℝ) ≤
      (HexPolyZMathlib.l2norm W.inputPolynomial) ^
          W.auxiliaryPolynomial.natDegree *
        (HexPolyZMathlib.l2norm W.auxiliaryPolynomial) ^
          W.inputPolynomial.natDegree := by
  exact (W.badVector_resultant_bounds_of_bhks_bad h_bad hp).1.trans
    (W.badVector_resultant_bounds_of_bhks_bad h_bad hp).2
```

This second statement already follows from existing infrastructure (the
two parts of `badVector_resultant_bounds_of_bhks_bad`) and is small
enough to land as a single review-sized lemma rather than a feature; it
plays the role of "BHKS Lemma 3.2, resultant form" with no new
algebraic obligations.

The remaining work for the norm bound itself is the
`auxiliaryPolynomial_l2norm_sq_le` bound and the algebraic step that turns
the resultant chain into a quadratic lower bound on `‖v‖₂²`.

### Placeholders that remain genuinely missing

- `auxiliaryPolynomial_l2norm_sq_le`: bounds `‖H_v‖₂` in terms of `‖v‖₂`
  and the per-coordinate CLD column bound `bhksCoeffBound`. No
  Mathlib gap; pure inequality work.
- `degree?` versus `Polynomial.natDegree` reconciliation in the
  `H_v.natDegree` form. Existing
  `HexPolyZMathlib.toPolynomial_natDegree`-style lemmas should suffice;
  no API gap.
- A real-valued `Nat.log p` versus `Real.log` reconciliation if the
  proof routes through the paper threshold's `(log ‖f‖₂)^n` factor.
  `BHKSBound.lean` already packages both sides.

No `Polynomial.resultant` Mathlib port is required — that question is
settled by `reports/bhks-resultant-infrastructure.md` (PR #5187).

## 3. Prerequisite split for the next feature issues

Three feature issues, in dependency order. None block on a resultant
audit because that work has merged; the split below is between work that
needs new algebraic infrastructure and work that is bookkeeping over the
existing `BadVector.lean` / `TerminationBound.lean` API.

1. **`bhks_bad_vector_resultant_lower_bound` (lemma).** Compose the
   existing `badVector_resultant_bounds_of_bhks_bad` parts into the
   single chained inequality
   `(p ^ (k * d) : ℝ) ≤ ‖f‖₂^(deg H_v) · ‖H_v‖₂^n`. No new structure,
   ~10-line proof using `le_trans`. Scope: one theorem in
   `BadVector.lean`. **Unblocked.** Suitable for a small review issue.

2. **`auxiliaryPolynomial_l2norm_sq_le` (lemma).** Bound `‖H_v‖₂²` by
   `‖v‖₂² · Σ_j (bhksCoeffBound input j)²`. Pathway: rewrite
   `BHKS.auxiliaryPolynomial input liftData vec` as a coordinate-wise sum,
   apply Cauchy–Schwarz coordinate-wise, sum across `j ∈ {0, …, n−1}`
   using the existing `bhksCoeffBound` columnwise bound. The squared form
   avoids `Real.sqrt`. Scope: one theorem in `BadVector.lean`, plus 1–2
   supporting coefficient-wise lemmas and a `cldColumnNormBound` helper
   definition. **Unblocked.** Suitable for a feature issue independent
   of (1).

3. **`bhks_bad_vector_norm_sq_gt_cutRadiusSq4_of_paperThreshold_le`
   (theorem).** Combine (1) and (2) with the paper-threshold chain in
   `TerminationBound.lean` (`bhksPaperThresholdReal_le_…`) to conclude
   that the squared norm of the bad-vector strictly exceeds
   `cutRadiusSq4`. Pathway: take logs in (1) using (2), expand the
   `bhksCutRadiusSq4` definition, dominate by `bhksPaperThresholdReal`
   under the project `0 ≤ C ≤ 2` constant convention. Scope: one
   theorem, ~50 lines of inequality manipulation; uses the existing
   `bhksPaperThresholdReal_le_factorFastPrecisionCap` adaptor.
   **Blocked on (1) and (2).** Suitable for a feature issue.

Beyond step 3, `factorFast_terminates` (directive #2567's `D1.6`) is a
short combinator pulling the BHKS separation into the existing
`L' = W → some _` recovery chain. That belongs in a separate fourth
issue once steps 1–3 land. It does not require any further BHKS algebra;
it is the case-split on the recovery path.

### Anti-scope

Out of scope for any of the four issues:

- Algorithmic changes to `factorFast`, `factorSlow`, or the combinator.
- Changes to `bhksBound` or `factorFastPrecisionCap`. Both have stable
  forms with `BHKSBound.lean` lemmas pinning their relation to the
  paper threshold.
- Resultant Mathlib ports — already settled.
- The "Group B" cluster (`W ⊆ L'`, equivalence-class identification,
  reconstruction-verifies-`L'=W`). Those are independent of the D1
  pathway and have their own issue threads.
