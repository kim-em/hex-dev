# Issue #8413: the classical recombination search returns irreducible factors

## Accomplished

Validated the premise of #8413 in depth and landed the first foundational
piece of the capstone: **budget monotonicity for the three size-ordered smart
loops** (`HexBerlekampZassenhaus/Basic.lean`, right after the
`scaledRecombinationSmart*_product` mutual block):

- `scaledRecombinationSmartAux_budget_le`
- `scaledRecombinationSmartSizeLoop_budget_le`
- `scaledRecombinationSmartCandLoop_budget_le`

Each states the returned budget `b ≤` the input budget. Proved as one mutual
block by structural recursion on `fuel`, mirroring the existing `_product`
mutual block. `lake build HexBerlekampZassenhaus.Basic` is green with no new
warnings.

## Premise validation (the important part)

The issue frames the work as "mirror the non-smart `RecoveredScaledSearch.covers_of_bound`
proof; plus #8412". Two findings:

1. **Sound, not a scale-vs-dilate trap.** The smart candidate is built with
   `ZPoly.dilate coreLc` (`Basic.lean:7789`), i.e. the *dilate* coordinate where
   the subset↔integer-factor correspondence actually lives
   (`liftedRecoveryCandidate`, `RepresentsIntegerFactorAtLift`). This is exactly
   the coordinate #8412's `subsetsOfSizeWithComplement_liftedFactors_exists_subset_of_matches`
   identifies. So the coverage argument is *not* blocked by the M1/scale
   unsoundness described in the boundary skill.

2. **The issue under-specifies the budget dimension.** Unlike the non-smart
   search (`scaledRecombinationSearchModAux`, no budget), the smart search
   threads a candidate `budget` that can abandon a factorable sub-target. This
   has no analog in `covers_of_bound` and changes the theorem shape.

## The clean theorem shape (resolved)

`classicalCoreFactorsWithBound` (`Basic.lean:8906`) sets
`budgetExhausted := res.isNone && remaining == 0` and returns `none` (declines to
the lattice tier) exactly when `res = none ∧ remaining = 0`. So when it returns
`some cf`, either `res = some factors` or (`res = none` with `remaining ≠ 0`).

Key propagation fact (this is why budget monotonicity is the first piece): once
the running budget reaches `0`, `SizeLoop`/`CandLoop` return `(none, 0)` and this
propagates upward, so **any budget-forced skip of a finer split forces the whole
search to `none`**. Therefore, conditional on the search returning `some result`
(the accepted case), no budget skip happened on the accepted path: every inner
`Aux` that returned `none` did so with budget *remaining*, which — with adequate
fuel — can only be a genuine "no recombination" verdict. Given the true support
`S_cov` of the min index is always a valid divisor split at its own size, the
peeled subset is exactly `S_cov` (never a coarser reducible union), so the
emitted candidate is the irreducible `f_cov`. Coverage then closes exactly as in
the non-smart proof.

So the capstone is the pair, proved by one induction on `fuel` (no budget lower
bound needed, only fuel adequacy):

```
scaledRecombinationSmartAux ... = (res, b) → (hyps + fuel adequacy) →
  (res = none → b = 0)                     -- completeness / trustworthy-none
  ∧ (res = some result → coverage result)  -- every irreducible factor covered
```

## Remaining work (the bulk of the capstone; multi-session)

1. **Step-execution subset identification through the 3 loops**: from a
   `SizeLoop`/`CandLoop` success extract the peeled `T ⊆ J`, `min ∈ T`,
   `cand = liftedRecoveryCandidate core d T`, `cand ∣ target`, and the recursive
   `Aux` on `target / cand` over `J \ T`. Consumes #8412's
   `subsetsOfSizeWithComplement_liftedFactors_exists_subset_of_matches`.
2. **The completeness + coverage mutual induction** (`res=none→b=0` ∧
   `res=some→coverage`), mirroring `covers_of_bound` (Mathlib `Basic.lean:17628`)
   and reusing its substrate verbatim (`cover_at_min`,
   `liftedFactorSubsetPartition_transport`,
   `coverAtMin_representingSubset_subset_of_liftedRecoveryCandidate_dvd_of_bound`,
   `exactQuotient?_liftedRecoveryCandidate_eq_some_of_eq_factor_of_primitive_pos_lc`,
   `representsIntegerFactorAtLift_primitive_of_bound`, etc.), plus the size-ordered
   prefix argument (all splits before size `|S_cov|` miss an element of `S_cov`;
   at size `|S_cov|`, `S_cov` is the unique divisor by containment).
3. **Fuel adequacy discharge**: the wrapper passes
   `fuel = budget + (r+1)(2r+3)` (`Basic.lean:7831`); show it never limits.
4. **Irreducibility wiring at `classicalCoreFactorsWithBound`**: coverage +
   `core` squarefree ⇒ `#result = #normalizedFactors(core)` ⇒ reuse
   `UFDPartition.irreducible_of_partition_card_eq_normalizedFactors_card` (the
   same closer as `exhaustiveCoreFactorsWithBound_factor_irreducible_of_count`).

## Next step

Build piece 1 (step identification) in the Mathlib layer, then piece 2. All
substrate is present; the difficulty is the size-ordered induction over three
mutually-recursive loops with budget threading, not missing math.

## Blockers

None mathematical. The premise is sound. The scope is genuinely larger than
"mirror + #8412": it is ~600–1000 lines of intricate mutual induction plus the
budget/fuel accounting the issue body does not mention.
