# HO-1 Directive Dependency Graph

This report maps the live dependency structure of the HO-1 / directive #2564
support chain so workers can find the real next blocker without re-opening
superseded branches. It is a current-state map, not a proof task: it implements
none of the BHKS API, fast substrate, or public factor capstone.

The binding goal is directive #2564 (van Hoeij CLD rollback) and its five-clause
headline correctness theorem for `Hex.factor`. The directive is OPEN and
`blocked`.

## Live dependency edges

`depends-on:` edges declared in issue bodies, restricted to OPEN issues. Closed
dependencies are dropped (they no longer gate anything).

```
#2564  (directive, blocked)
  ├── depends-on #4818        ← spurious backwards edge (see below)
  └── depends-on #4172        ← spurious backwards edge (see below)

#4818  (blocked)  depends-on #6672
#4172  (blocked)  depends-on #6672          (also lists closed #4825)
#6867  (blocked)  depends-on #6672
#6868  (blocked)  depends-on #6672, #6867
#6246  (blocked)  depends-on #2564

#6672  (capstone, blocked)  depends-on #7804
#7804  (claimed)            no live depends-on   ← active frontier
#7805  (blocked)            depends-on #7804

#7802  (claimed)            depends-on #7788 (CLOSED → effectively unblocked)
#7799  (blocked)            depends-on #7789 (CLOSED), #7802

#6779  (replan, blocked)    depends-on #2564     ← inverted/off-path (see below)
```

## The live blocker chain (what to actually work next)

There are two independent active fronts. Neither has an unsatisfied prerequisite
other than the one named.

### Front A — fast-BHKS substrate (gates the directive capstone)

```
#7804  centered-recovery lift API        [claimed — IN PROGRESS]
  → #7805  unconditional factorFastRaw_irreducible_of_some   [blocked on #7804]
  → #6672  factor_irreducible_of_nonUnit capstone fast disjunct
  → #4818 / #4172  bridge Hex.ZPoly.isIrreducible_iff
  → #2564  directive headline
  ‖ also feeds #6867 (clause 2, primitive) and #6868 (clause 4, non-associated)
```

`#6672` declares `depends-on #7804`, but the substrate it actually consumes is
`#7805`'s unconditional `factorFastRaw_irreducible_of_some`. `#7804` only repairs
the lift API that `#7805` then builds on. So the true order is
**#7804 → #7805 → #6672**, and `#6672` should not be claimed until `#7805`
lands. The slow-trial
(`factorSlowTrialFactorsWithBound_factor_irreducible_of_fast_none`) and
slow-modular (`slowModularRaw_irreducible_of_fast_none`) disjuncts of `#6672`
are already dischargeable unconditionally; only the fast disjunct is gated.

Capstone target, still a sorry:
`HexBerlekampZassenhausMathlib/FactorSoundness.lean:18`
`factor_irreducible_of_nonUnit`.

The conditional producers that exist today (do **not** mistake these for the
substrate `#7805` must deliver):

- `factorFastFactorsWithBound_raw_zpolyIrreducible_of_forwardInputs`
  (`PartitionRefinement.lean:1010`) — threads `ForwardRecoveryInputs`,
  `CutProjectionHypotheses`, `hcore`, partition-count, `reassemblyExpansionComplete`
  as free hypotheses.
- `factorFastCoreWithBound_some_factor_zpolyIrreducible_of_lift`
  (`PartitionRefinement.lean:601`) — conditional on the `_of_lift` package.
- `factorFastFactorsWithBound_raw_zpolyIrreducible_of_cut`
  (`PartitionRefinement.lean:1102`) — the `#7786` deliverable-1 forward wrapper,
  no `ForwardRecoveryInputs`, but still consumes a `cutProjectionHypotheses`
  input that needs a per-support coverage producer.

`#7804`'s job is to supply that coverage producer in the centered/dilated form
the executable recovery actually exposes; `#7805` then routes it through
`..._of_cut` to an unconditional conclusion.

### Front B — Berlekamp per-member irreducibility (Mathlib bridge)

```
#7802  berlekampFactor_factors_irreducible (non-monic generalization)  [claimed — IN PROGRESS]
  → #7799  discharge HexBerlekampMathlib sorry irreducible_of_mem_berlekampFactor
```

`#7802` is **effectively unblocked**: its sole `depends-on #7788` is CLOSED
(landed as `irreducible_of_no_kernelWitnessSplit_squareFree_of_dvd`,
`HexBerlekamp/RabinSoundness.lean:3780`, PR #7794). The remaining work in `#7802`
is the non-monic / associate-transport wrapper plus the `berlekampFactor`-level
producer.

`#7799` then replaces the sorry at `HexBerlekampMathlib/Basic.lean:948`
(`irreducible_of_mem_berlekampFactor`) using `#7802`'s producer and the existing
transport primitive `irreducible_toMathlibPolynomial_of_fpPolyIrreducible`
(landed, PR #7784). Front B supports the Mathlib-side irreducibility surface; it
is not on the directive #2564 critical path but unblocks downstream consumers of
per-factor irreducibility.

## Stale dependency references

1. **#7799 → #7789 (dead edge).** `#7789` is CLOSED and was replaced by `#7802`
   (the original `#7789` body wrongly assumed `berlekampFactor` outputs are
   monic; raw `DensePoly.gcd`/cofactor outputs are non-monic). `#7799` lists
   *both* `depends-on #7789` and `depends-on #7802` and its prose still names
   `#7789` as "the executable producer." The live producer is `#7802`; the
   `#7789` edge is dead. Flagged on the issue.

2. **#2564 → #4172, #2564 → #4818 (spurious backwards edges).** Both are
   *downstream consumers* of the headline theorem (bridge-side
   `isIrreducible_iff` assembly), not prerequisites of the directive. They are
   the only OPEN entries in `#2564`'s `depends-on` list — every other listed dep
   (#5869, #4825, #4819, #4821, #4830, #4831, #4832, #4880, #5214, #5215, #4170,
   #5237, #5905, #5893) is closed. These two edges keep `#2564` artificially
   `blocked`. They were diagnosed on `#2564` on 2026-06-15; this report confirms
   they are still present. The old blocking cycle they were part of
   (`#2564 → #4172/#4818 → #6672 → #6771 → #6779 → #2564`) is now **broken at two
   points**: `#6771` is CLOSED and `#6672` was re-pointed from `#6771` to `#7804`.
   So the only residual artifact is the two backwards edges plus the inverted
   `#6779 → #2564` edge.

3. **#4172 → #4825 (stale closed edge) + stale body map.** `#4172` declares
   `depends-on #4825` and its body says "#4825 remains open," but `#4825` was
   closed as superseded by `#6672` (recorded in `#4818`'s 2026-06-13 history).
   `#4172`'s only live dependency is `#6672`. Low urgency — `#4172` is already
   `blocked` behind `#6672` regardless.

4. **#6779 → #2564 (inverted edge).** `#6779` is `replan` + `blocked`, demoted to
   HO-4 D1 off the correctness critical path (per #7461). Its `depends-on #2564`
   inverts the real direction. It is richly documented already (see "Do not
   reattempt") and is not on any live front; no new comment needed.

## Do not reattempt — diagnosed dead routes

These were each diagnosed with concrete evidence (computation, missing-lemma
shape, refuted fixtures). Do not re-open them as prerequisites.

- **Resultant-on-cut-aux valuation.** `resultant_divisible_by_p_pow` /
  `p^(a·d) ∣ Res(input, aux_cut)` is **false as typed**: `v_p(Res) = 0` for
  genuine bad vectors on the down-scaled CLD aux. It is a bare unproven field
  (`HexBerlekampZassenhausMathlib/BadVector.lean:1038/1300/1499`) with no
  producer; the `auxiliary_selected_congr` syzygy route is unsatisfiable in the
  bad-vector regime. Confirmed dead across the entire
  #6949→#7109→#7116→#7120→#7163→#7175→#7181→#7188→#7232 thread and two second
  opinions. The surviving direction is the van Hoeij CLD rollback = directive
  #2564. (Tracked on #6779, #2564.)

- **`BHKS.ForwardRecoveryInputs` / reverse `L' = W`.** The reverse inclusion
  `projectedRowSpan_eq_trueFactorIndicatorLattice` (the `L' = W` direction) is
  **not** needed for the correctness capstone; fast-core irreducibility rides the
  forward `W ⊆ L'` count bound (#7461 via the now-closed #6771). Fronts A and B
  must use the **forward** route. `#7804` and `#7805` explicitly forbid depending
  on `ForwardRecoveryInputs`.

- **Cap-determinism / no-early-recovery (#7667).** Refuted by checked fixtures
  (#7671), closed superseded. Do not retry the per-precision separation framing.

- **Conditional fast producer as the substrate (#7739 / PR #7746).** `#7739`
  landed only the *conditional*
  `factorFastFactorsWithBound_raw_zpolyIrreducible_of_forwardInputs`; it is not
  the unconditional substrate `#6672` needs. Threading the BHKS package as free
  hypotheses is not a discharge.

- **Per-factor `irreducible_of_no_kernelWitnessSplit_squareFree` (#7783).**
  Impossible as a per-factor application: the Berlekamp loop feeds each factor
  *`f`'s* kernel (`Factor.lean:116`), while that theorem requires the factor's
  *own* kernel (`RabinSoundness.lean`). The divisor-generalized replacement
  `irreducible_of_no_kernelWitnessSplit_squareFree_of_dvd` (#7788, landed) is the
  correct tool — but it requires `Monic g`, which is why `#7802` (non-monic
  generalization) is the live successor, not the closed `#7789`.

- **Old `#7789` name.** `#7789` (monic-assuming per-member Berlekamp capstone) is
  CLOSED. The live replacement is **#7802**. Any issue or comment pointing a
  worker at `#7789` as actionable is stale.

## Verification

- `python3 scripts/check_dag.py` → exit 0.
- Theorem-name cross-checks against the tree (all confirmed present at the cited
  lines): `factor_irreducible_of_nonUnit` (FactorSoundness.lean:18, `sorry`);
  `irreducible_of_no_kernelWitnessSplit_squareFree_of_dvd`
  (RabinSoundness.lean:3780); `factorFastFactorsWithBound_raw_zpolyIrreducible_of_cut`
  (PartitionRefinement.lean:1102); `..._of_forwardInputs` (:1010);
  `factorFastCoreWithBound_some_factor_zpolyIrreducible_of_lift` (:601);
  `irreducible_of_mem_berlekampFactor` (HexBerlekampMathlib/Basic.lean:948,
  `sorry`).
- Issue states confirmed via `gh issue view` on 2026-06-18.
