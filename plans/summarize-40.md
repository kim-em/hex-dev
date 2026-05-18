## Current state

The last closed summarize issue is #4864 (thirty-ninth Phase 4/5
checkpoint), which closed at 2026-05-18T00:16:24Z. Since then 18 PRs
have merged
(`git log --since="2026-05-18T00:16:24Z" --oneline | wc -l` = 18,
counting the summarize commit itself; the new PRs are 17), well above
the planner summarize trigger (10+ PRs merged since the last
summarize closed).

Recent landings continue two main threads:

* **BZMathlib A2 abstract-bound `_of_bound` propagation**: PR #4878
  landed the bottom three `_of_bound` siblings of the A2 Mignotte-
  precision recovery chain (#4873). PRs #4888 / #4889 / #4894 / #4899
  propagated `_of_bound` upward through the unscaled / scaled
  recovery-candidate and `representsIntegerFactorAtLift_monic` /
  `_primitive` layers. PRs #4895 (in flight), #4904, #4906 covered
  the Layer 1 utility siblings (`natDegree_toPolynomial_eq_sum_of_represents`
  for monic and `_primitive_pos_lc_core`, and
  `not_represents_empty_of_irreducible_dvd_core` for monic and
  primitive).
* **BZ Mathlib-free Gauss substrate**: PR #4886 landed the
  Mathlib-free `content_mul` / `ZPoly.content_mul` / `ZPoly.modP_mul`
  and `leadingCoeffAdmissible`-conditioned `modP` preservation
  lemmas. PR #4897 then closed #4884 by adding the Mathlib-free Gauss
  reduction-mod-`p` transfer
  `ZPoly.Irreducible_of_modP_irreducible_of_primitive_of_admissible`,
  the substrate that #4885 (small-mod singleton branch composition,
  currently claimed) consumes.
* **Exhaustive search scaled side**: PR #4872 added
  `recombineScaledExhaustive` and structural invariants (#4866);
  PR #4881 added the scaled product lemmas (#4869); PR #4893 routed
  `exhaustiveCoreFactorsWithBound` through
  `recombineScaledExhaustive`; PR #4903 added the scaled-membership
  wrapper (#4875). These collectively close the scaled side of the
  exhaustive-search call surface.
* **HexGramSchmidt adjacent-swap update**: PRs #4871, #4876, #4887,
  #4898 finished the adjacent-swap `scaledCoeffs` update cluster
  (above-prev / above-curr bordered-minor identities, the bridge
  rerouting fix, and the assembled quotient formulas).

## Deliverables

Produce the **fortieth Phase 4/5 checkpoint summary**. The summary
issue (this one) should include:

1. **Header** with the PR count (17 new PRs as of issue creation;
   recompute at execution time excluding the previous summarize PR
   itself), the closing-of-#4864 timestamp (2026-05-18T00:16:24Z),
   and the `coordination orient` snapshot at the time the summarize
   issue is opened (open directives, unclaimed/claimed/blocked
   buckets, open PRs).

2. **Per-theme PR groupings** clustering the merged PRs into
   coherent themes. Expected themes based on the commit log:

   * **BZMathlib A2 `_of_bound` propagation chain**: #4878 (Mignotte-
     precision recovery, three sibling proofs), #4888 (unscaled
     recovery candidates), #4889 (scaled recovery candidates), #4894
     (representsIntegerFactorAtLift_monic), #4899
     (representsIntegerFactorAtLift_primitive), #4904
     (natDegree_toPolynomial_eq_sum_of_represents primitive
     pos_lc_core), #4906 (not_represents_empty for both monic and
     primitive).
   * **BZ Mathlib-free Gauss substrate**: #4886 (`content_mul`,
     `modP_mul`, admissible-`modP` preservation), #4897 (Gauss
     reduction-mod-`p` transfer at ZPoly.Irreducible).
   * **Exhaustive search scaled call site**: #4872
     (`recombineScaledExhaustive` and structural invariants), #4881
     (scaled recombination product lemmas), #4893
     (`exhaustiveCoreFactorsWithBound` switch to scaled call site),
     #4903 (scaled membership wrapper).
   * **BZ Mathlib-free small-mod singleton**: #4877 (small-mod
     singleton Berlekamp irreducibility wrapper v2, re-decomposing
     the originally-scoped #4839 chain).
   * **HexGramSchmidt adjacent-swap update**: #4871 (above-prev
     bordered minor), #4876 (scaledCoeffs_eq case-split bridge
     reroute), #4887 (above-curr bordered minor), #4898 (quotient
     formulas assembled).
   * **Process/docs**: #4868 itself (thirty-ninth checkpoint).

   Include the PR title and a one-clause "why this matters" pointer
   for each entry, grouped under the theme.

3. **Status snapshot** including:

   * libraries.yml `done_through` deltas since #4864 closed (read
     `git log --since="2026-05-18T00:16:24Z" -- libraries.yml`).
     At time of writing no `libraries.yml` commits land in the window
     — the implementation work is still preparing the next
     `done_through` bump.
   * Any in-flight PRs the summarize finds awaiting CI.
   * Any `directive` issues that closed during the window (none
     expected — #2637, #2567, #2564 should all still be open).

4. **HO-1 critical-path commentary**: the BZ Mathlib-free chain
   (capstone #4170, sub-capstone #4825) has multiple sub-streams in
   flight. Identify which sub-chain is currently nearest to closing
   #4825 and what its next blocker is. The candidates are:

   - The small-mod singleton branch (#4885 claimed, #4877 substrate
     landed),
   - The Gauss reduction-mod-`p` chain (#4897 landed, awaiting
     consumers in the executable singleton path),
   - The `henselSubsetCorrespondence_analytic_obligation` chain
     (#4680 / #4821, both blocked on directive #2567), and
   - The exhaustive-arm branch entry (#4880 blocked on #4879,
     unclaimed).

   The progress files in `progress/` for the window are the primary
   source.

5. **`_of_bound` propagation commentary**: the A2 abstract-bound
   propagation is now well above the bottom of the chain. Identify
   what siblings remain to close the entire `_of_bound` propagation
   (the blocked #4902 / #4907 are the immediate next layer; the
   in-flight #4901 / #4895 are still merging).

6. **Carryover items** for the next summarize: the small-mod
   singleton branch composition (#4885 claimed at time of summary
   creation) and the support-containment / partition-cover analytic
   gap chain (#4830 / #4831 / #4832 / #4680 / #4821, transitively
   blocked on directive #2567).

Keep the body to a single GitHub-issue page — under ~3 KB of body
text. Detailed PR-by-PR commentary is fine in the per-theme
groupings; an additional "Concerns" or "Open questions" subsection
is not required unless the worker actively identifies one (audit
findings filed as separate issues per
[Conventions.md §Bench-found, conformance-found, and audit-found
issues](../PLAN/Conventions.md#bench-found-conformance-found-and-audit-found-issues)).

## Library placement

Not applicable — summarize issues produce a GitHub-issue body, not a
Lean code change.

## Context

Read:

- `progress/` files between 2026-05-18T00:16:24Z and now.
- `git log --since="2026-05-18T00:16:24Z" --oneline` and the body of
  any non-trivial merge commit.
- #4864 body and closing comment, as a model for the section
  headings and tone.
- Previous summarize issues (#4766, #4622, #4557, #4512) for tone
  and structure consistency.

## Verification

- Run `coordination orient` and copy the snapshot into the body.
- Confirm the PR count from
  `git log --since="2026-05-18T00:16:24Z" --oneline | wc -l` minus 1
  for the previous summarize commit itself.
- `gh issue view <this issue number>` after publishing to confirm
  formatting renders correctly.

## Out of scope

- Filing follow-up implementation work; that is the next planner's
  job. The summarize body may *note* observed gaps but should not
  file work items.
- Re-litigating closed issues or PRs.
- Auditing benches, conformance, or oracle results — those go
  through the bench-found / conformance-found / audit-found
  workflow, not the summarize workflow.
