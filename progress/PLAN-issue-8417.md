# Issue #8417 — verify the lattice tier (van Hoeij / BHKS)

**Branch:** `issue-8417`. **Library:** `HexBerlekampZassenhausMathlib`.
Goal: prove the lattice-tier outputs (`factorLatticeFactorsWithBound`) are
irreducible — the van Hoeij / CLD "lands on minimal subsets" argument.

## Architecture discovered (authoritative)

Computational def `Hex.latticeCoreFactorsWithBound core B primeData`
(`HexBerlekampZassenhaus/Basic.lean:9685`) has **three arms**:

1. `primeData.factorsModP.size ≤ 1` → `some #[core]`.
   **PROVABLE NOW, unconditionally.** core is irreducible mod p ⇒ irreducible
   over ℤ. Reuse `squareFreeCore_irreducible_of_smallModSingletonBranch`
   (`IntReductionMod.lean:3477`). This is genuine method verification.

2. `factorFastCoreWithBound core B pd k fuel = some coreFactors` → those factors.
   **BLOCKED on BHKS count-equality** (the year-blocker, arm-2 form). Already
   isolated by `factorFastCoreWithBound_some_factor_zpolyIrreducible_of_count`
   (`Basic.lean:17243`) / `..._irreducible_of_count` (`Basic.lean:17065`),
   which take `hcount : length = normalizedFactors.card` as a hypothesis.
   `count_le` is proven; `count_ge` needs irreducibility (circular). The CLD
   coverage certificate is the missing piece.

3. `factorFastCoreWithBound = none` ∧ `bhksSingleAllOnesPartition core d = true`
   → `some #[core]`. **BLOCKED on deep van Hoeij `L=W`.** The single all-ones
   equivalence class of the CLD lattice (at cap precision) ⇒ core irreducible.
   This is the CLD adequacy / no-bad-vector theorem. `bhksSingleAllOnesPartition`
   (`Basic.lean:9670`) computes an LLL lattice basis → projected rows →
   equivalence-class indicators → all-ones single-class check.
   Bridge layer is **greenfield** for this (0 refs).

## Classical proof to mirror

`classicalCoreFactorsWithBound_factor_irreducible_of_validBound`
(`IntReductionMod.lean:6902`) — the #8413 capstone. Uses `RecoveredSmartSearch`
coverage + `smartCore_factor_irreducible_of_covers_of_squarefree` + UFD partition.
The lattice tier mirrors this but arms 2/3 need the BHKS coverage the classical
size-ordered search proved but the CLD recovery has not.

## Plan (this session)

- [x] Map architecture.
- [ ] New file `HexBerlekampZassenhausMathlib/LatticeTier.lean` (imports IntReductionMod).
- [ ] Prove arm 1 unconditionally.
- [ ] Reduce arm 2 to the existing `hcount` obligation (hypothesis).
- [ ] Reduce arm 3 to `bhksSingleAllOnesPartition = true → Irreducible core` (hypothesis).
- [ ] Top-level `latticeCoreFactorsWithBound_factor_zpolyIrreducible_of_bhks`:
      arm 1 proven, arms 2/3 threaded as the two clean BHKS hypotheses.
- [ ] (stretch) 3a: prove "no proper nonempty subset represents a proper integer
      factor ⇒ core irreducible" from #8413 partition/`unique_subset` machinery,
      so arm-3 hypothesis becomes the pure Bool⇒no-subset lattice statement.
- [ ] `factorLatticeFactorsWithBound`-level corollary (reassembly wrap).
- [ ] second-opinion; PR (--partial if arms 2/3 remain hypotheses); decompose
      the deep arm-2 (CLD count) and arm-3 (all-ones adequacy) into successor issues.

## FULL arm-3 architecture (Kim: attempt it, use the PROVEN LLL path)

Van Hoeij (Klüners survey, fetched): factor core mod p into r factors, Hensel
lift to p^k. True factors g_i = prod_{j in S_i} f~_j; subsets S_i partition
{1..r}, encoded as 0-1 vectors w_i spanning W ⊆ ℤ^r. Φ(g)=f·g'/g (log deriv),
additive; v∈W ⟺ Φ(g_v)∈ℤ[x] (bounded coeffs, Landau-Mignotte/CLD). Lattice
Λ = [I_r | Ã ; 0 | p^k I_n] (Ã = CLD rows). At precision p^k > c·4^{n²}·‖f‖²^{2n-1}
(Thm 3), LLL-reduced rows within the Gram-Schmidt cut = basis of W. Single
all-ones class ⟺ W=⟨(1..1)⟩ ⟺ s=1 ⟺ core irreducible. NB p.8: irreducible case
NEEDS full precision — no shortcut (kills completeness+uniqueness angle).

Concrete executable defs (HexBerlekampZassenhaus/Basic.lean):
- bhksLatticeBasis f p a lifted : the [I_r|Ã;0|diag(p^(a-l_j))] matrix (4881).
- bhksProjectedRows = LLL-reduce (lll.shortVectorsUnchecked = lllNative.rows!) +
  Gram-Schmidt cut (bhksWithinGramSchmidtCut = Klüners Lemma 1, cut radius
  bhksCutRadiusSq4 = 4r+n·r²) + project to first r coords (bhksProjectIndicator).
- bhksEquivalenceClassIndicators : kernel/equiv-classes of projected rat matrix.
- bhksSingleAllOnesPartition : exactly 1 class, all-ones.

PROVEN LLL TOOLS (HexLLLMathlib/ShortVector.lean) — MUST use these, no re-derive:
- lllNative_first_row_norm_sq_le_unconditional : ‖(lllNative b δ..).row 0‖² ≤
  (1/(δ-1/4))^(n-1) · ‖x‖² for any nonzero x ∈ latticeSubmodule b. (needs hind)
- lllNative_mem_latticeSubmodule_iff : lllNative preserves the lattice.
shortVectorsUnchecked b δ.. = (lllNative b δ..).rows.toArray (Dispatch.lean:64).

Arm-3b lemma chain (build in LatticeTier.lean):
- (3b-i)  cldCoeffs f p a g = coeffs of Φ(g)=f g'/g mod p^a.               [DEEP]
- (3b-ii) v short (within cut) ⟺ v ∈ W (uses LLL bound + CLD Landau-Mignotte
          + precision adequacy p^k=bhksBound big enough).                  [DEEP]
- (3b-iii) bhksEquivalenceClassIndicators = partition into S_i.            [DEEP]
- (3b-iv)  single all-ones class ⟹ no proper nonempty representing subset. [→3b-ii/iii]
- (3a)     no proper nonempty representing subset ⟹ Irreducible core.      [TRACTABLE now]

## Arm 3a plan (do first, reusable tail):
Use liftedFactorSubsetPartition_of_choosePrimeData (Basic.lean:20335) giving
LiftedFactorSubsetPartition core d univ core, whose fields: cover (every idx in
some representing subset of an irred factor | core), pairwise_disjoint,
unique_up_to_associated. Reducible core (squarefree ⟹ card≥2) ⟹ two disjoint
nonempty representing subsets ⟹ one is proper nonempty ⟹ contra
"no proper nonempty representing subset". Needs: representing subset of a
nonconstant factor is nonempty; univ represents core so S=univ ⟹ factor~core.

## Doctrine constraints
- NO axioms, NO native_decide, NO sorry-bashing. Conditional theorems (hypotheses
  isolating the deep content) are the established codebase convention for this exact
  BHKS obligation (`_of_count`), so they are legitimate & mergeable.
- `factor` is NOT yet `factorHybrid`, so this does not touch the `factor_irreducible_of_nonUnit`
  sorry directly; it is standalone lattice-tier substrate for the future swap.
