# Stage-1 findings: viability of option (a) — a core-coordinate forward cut

Investigation for the plan "close `factor_irreducible_of_nonUnit` via a
core-coordinate forward cut". Every claim below is grounded in a named
definition/lemma with `file:line`.

## 1.1 — The executable recovers over the CORE basis (definitive)

`bhksRecoverClassified f d` builds `L := bhksLatticeBasis f d.p d.k d.liftedFactors`
and product-checks `Array.polyProduct candidates == f`
(`HexBerlekampZassenhaus/Basic.lean:6747-6761`). `factorFastCoreWithBound` calls it
with `f = core` (non-monic) and `d = toMonicLiftData core k primeData`
(`factorFastCoreWithBound_unfold`). `bhksLatticeBasis f …` computes
`cldRows := liftedFactors.map (cldCoeffs f …)` and `thresholds := bhksCutThresholds f`
(`Basic.lean:4911-4926`) — i.e. **the CLD coefficients and cut thresholds come from
the non-monic `core`**, with monic Hensel lifts as `liftedFactors`.

The bridge mirror confirms it: `latticeBasisOfLiftData f d := bhksLatticeBasis f d.p d.k d.liftedFactors`
(`Recovery.lean:407`), so `projectedRowsOfLiftData core (toMonicLiftData …)` is the
**core** lattice. Hence the executable-success producers `size_eq_indicators`
(`PartitionRefinement.lean:449`) and `partition_eq_normalizedFactors_card`
(`:480`) are **already over the core basis** — they match the executable's `M`.

**Consequence:** the monic/core mismatch is real (cldCoeffs(core) ≠
cldCoeffs((toMonic core).monic)). But because `hsize`/`hpartition` are already
core-basis, supplying the forward cut **over the core basis** makes the whole count
chain (`count_le` + `count_ge_of_cut` → `count_eq_of_cut` → `irreducible_of_cut`,
`PartitionRefinement.lean:600/631/659/682`) consistent with **no bridge lemma** —
this is exactly what the false `#8287` "monic count = core count" bridge was trying
(and failing) to paper over.

## 1.2 — What a core-coordinate forward cut needs

The forward cut `CutProjectionHypotheses L trueSupports` (`Lattice.lean:1814`) is a
pure lattice-membership claim, basis-agnostic. Its generic producer
`cutProjectionHypotheses_of_shortVectors` (`Lattice.lean:2079`) needs, per support,
a `SupportShortVectorData L S` (`Lattice.lean:402`): a vector in `L`'s lattice whose
first block is the support indicator and with `4·‖v‖² ≤ bhksCutRadiusSq4 L`.

Key point: **`SupportShortVectorData` never references `RecoveredLift.recovered_eq`**
(the `dilate(leadingCoeff f, …)` field that #8288 found type-impossible in the core
coordinate). So **(a) is NOT blocked by #8288** — the cut needs short vectors, not
the dilate-recovery.

The generic shortness scaffolding is reusable for any basis:
- `fourMulNormSq_le_of_proj_col` (`Lattice.lean:~1160`): `4·‖v‖² ≤ bhksCutRadiusSq4 L`
  from "first block = indicator" + per-column tail bound `2·|v_{r+j}| ≤ factorCount`.
- `two_mul_natAbs_sum_psiCut_period_le`: the per-column period/carry bound.

The monic producer `supportShortVectorData_of_recoveredLift`
(`CLDColumnBound.lean:1850`) reduces the per-column bound to
`recoveredLift_aggregate_residue` (`:1478`), whose `hf_lc : leadingCoeff = 1`
is used at **exactly one place** (`:1509-1512`: `centeredLiftPoly(supportProduct) =
factor` via `dilate_one`). That lemma outputs, per column j:
1. `centeredResiduePow(∑_{i∈S} cldQuotientMod core gᵢ).coeff j = phi(core, factor).coeff j`
2. `|phi(core, factor).coeff j| ≤ bhksCoeffBound core j`

## 1.2 — The crux (the genuine difficulty)

In the **core** lattice, `supportProduct` (product of the monic Hensel lifts in S)
is `≡` the **monic correspondent** of the true factor (mod `p^a`), **not** the
primitive integer factor `h | core`. So the core aggregate residue relates to
`phi(core, monicCorrespondent)`, and we need it bounded by `bhksCoeffBound core`.

The clean bound lemma `abs_phi_coeff_le_bhksCoeffBound` (`CLDColumnBound.lean:1091`)
requires its divisor `g` to be **monic AND `g ∣ f` over ℤ** (lines 1092-1093). In
the core coordinate **neither candidate qualifies**: the primitive factor `h | core`
is non-monic; the monic correspondent is monic but does **not** divide `core` over ℤ
(`core = leadingCoeff · ∏ primitive factors`). This is precisely why the monic
coordinate was chosen — it *has* monic integer divisors, so the CLD/Mignotte bound
is clean.

So (a) requires a **new core-coordinate CLD shortness bound**:
`|phi(core, monicCorrespondent).coeff j| ≤ bhksCoeffBound core j` (at precision ≥
`cldCoeffFloor`), with no monic-integer-divisor available. It is **true** (the
executable is verified correct at acceptance precision — run on `(2x+1)(x⁴+1)`,
`(3x+2)(x²+2)`, `(6x²-1)(x+5)`, all correct — so the core cut holds there), but the
existing clean infrastructure does not supply it; it is a Mignotte-type analysis in
the "rational-monic divisor of an integer polynomial" setting.

## Verdict

- **(a) is provable in principle and is NOT blocked by #8288.** The count chain,
  the cut abstraction, and the generic shortness scaffolding are all reusable, and
  `hsize`/`hpartition` are already core-basis.
- **The entire difficulty concentrates in ONE new lemma:** a core-coordinate CLD
  shortness bound for `phi(core, monicCorrespondent)` without a monic integer
  divisor. This re-introduces exactly the analytic difficulty the monic coordinate
  was designed to avoid; difficulty is moderate-to-uncertain.
- **(b) (change the executable to recover over the monic lattice + un-monicize)**
  remains the alternative: it makes the existing clean monic machinery (#8286,
  ★, ★★, keystone) apply directly, trading the new analysis for a localized
  executable change + re-verify (29/29) + re-bench. The un-monicization
  (`primitivePart ∘ dilate`) already exists in the keystone layer.

## UPDATE — BHKS paper alignment overturns the pessimism (option (a) confirmed)

Read BHKS §3-4 (arXiv:math/0409510, extracts in `/tmp/bhks-section3.md`,
`/tmp/bhks-section4.md`) and got a paper-grounded Codex second opinion. Result:
**the executable's core (non-monic) coordinate IS the paper's; the monic machinery
was the deviation.**

- BHKS Φ(g) = `f · g'/g` (the logarithmic derivative times the **original** `f`),
  with `f` **never assumed monic** — non-monic is an advertised advantage ("our 'f
  times g'/g approach' … particularly when f is not monic"). This is exactly the
  executable's `phi(core, g) = core·g'/g`.
- **Lemma 4.1**: for `f, g ∈ ℂ[X]` with `g ∣ f` (NO monic hypothesis on either),
  `|Φ(g).coeff i| ≤ C(n-1,i)·n·M(f)`. This is **exactly** the executable's
  `bhksCoeffBound f j = Nat.choose (n-1) j · n · coeffL2NormBound f`.
- **Corollary 4.2**: for `f ∈ ℤ[X]` (non-monic) and `g` any `ℚ`-factor of `f`,
  `Φ(g) ∈ ℤ[X]_{<n}` with `‖Φ(g)‖₂ ≤ 2^{n-1}·n·‖f‖₂`. Proven via Mahler measure
  (`M(Φ(g)) ≤ deg(g)·M(f)`, `M(AB)=M(A)M(B)`, `M(A') ≤ deg(A)M(A)`).
- The all-coefficients lattice `L` (paper p.5), cut radius `B' = √(r²+B²)`, the LLL
  cut, Lemma 3.2, and the resultant contradiction **all use the original `f`**.
  Codex: "I see no K=Q step that genuinely requires `f` monic." The "monic
  K-factors" are only associate-normalization for the 0/1 support vectors.
- My earlier "supportProduct ≡ monic correspondent ≠ true factor" worry is
  resolved by **scale-invariance**: `Φ(core, c·h) = Φ(core, h)` because
  `(c·h)'/(c·h) = h'/h`. So a monic associate has the same CLD vector. Codex:
  "The gap is not mathematical; it is a Lean obligation to state and use this
  scale-invariance bridge" (valid under the good-prime condition `v ∤ ℓf`, which
  the executable enforces).

So `abs_phi_coeff_le_bhksCoeffBound` (`CLDColumnBound.lean:1091`) carries an
**unnecessary** `hg_monic` hypothesis — it was proven via the monic route
`abs_phi_coeff_le_of_monic_factor`, but BHKS Lemma 4.1's Mahler-measure proof needs
no monic. The corrected verdict: **option (a) is the paper-faithful path, and its
crux is NOT novel research — it is the Lean form of Lemma 4.1 / Cor 4.2 (non-monic
CLD bound) plus a trivial scale-invariance bridge.** Both my analysis and Codex
agree: **(a), paper-grounded.**

### Corrected (a) work-list
1. Non-monic CLD coefficient bound (Lean Lemma 4.1): drop `hg_monic` from
   `abs_phi_coeff_le_bhksCoeffBound`, proving via Mahler measure / Landau (check
   what Mathlib provides: `Polynomial.Monic.mahlerMeasure`, `mahlerMeasure_mul`,
   `mahlerMeasure_derivative_le`). The repo already has
   `mahlerMeasure_le_sqrt_sum_sq_coeff` (per #2564 notes).
2. Scale-invariance bridge: `phi(core, c·h) = phi(core, h)` for `c ≠ 0` const.
3. Core-coordinate `SupportShortVectorData` producer from (1)+(2), feeding the
   basis-agnostic `cutProjectionHypotheses_of_shortVectors` → the generic
   `count_ge_of_cut`/`irreducible_of_cut` chain at `L = bhksLatticeBasis core …`.
4. Assembly: discharge `h_raw` in `factor_entries_irreducible` → close
   `FactorSoundness.lean:18`. (`hsize`/`hpartition` are already core-basis.)

## Recommendation (superseded by the UPDATE above)

The choice is close. (a) keeps the correct, benchmarked executable untouched and
isolates the open work to one contained (if non-trivial) CLD lemma; (b) reuses the
proof but edits working code. I recommend a **time-boxed attempt at the single
core-coordinate CLD shortness lemma**; if it proves out, (a) closes cleanly via the
existing chain; if it proves intractable, pivot to (b) with the monic machinery
already in hand. Either way the count-argument architecture (Stage-0 SPEC note) is
the same and should be recorded now.
