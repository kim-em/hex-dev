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

Codex second-opinion (2026-07-01) confirmed: no accepted-path reducible
counterexample under the full invariants (premise sound), and the crux is the
`res = none → b = 0` half — budget monotonicity alone is insufficient; it must be
proved *mutually* with accepted-path coverage. It also flagged that containment
must be over the **remaining** supports of the running `target`, transported per
peel by `liftedFactorSubsetPartition_transport`.

## The fuel-adequacy invariant (resolved: `budget + 2 * J.card ≤ fuel`)

The fuel decrements once per loop step. The apparent worry is that a `CandLoop`
at size `d` must examine all `C(|tail|, d)` splits (exponential) before moving on
— but the **budget** also decrements once per split examined, so the number of
splits any single `CandLoop` examines is `≤ budget`. Crucially `SizeLoop` gives
each size class a *fresh* fuel (its own `fuel` decremented only by the size
index, not by prior `CandLoop` consumption). So the per-size fuel need is
`≤ budget`, and the only extra fuel is the `≤ J.card` size-index overhead plus
`≤ J.card` for the `Aux` recursion frames. The clean, maintained invariant is:

```
budget + 2 * J.card ≤ fuel
```

Maintenance across one peel of `S_cov` (worked out): with fuel consumed
`|S_cov| + p* + 2` and budget consumed `E + p* + 1` (`E` = splits at smaller
sizes, `p*` = position of `S_cov` at its size), the recursion gets
`fuel_rec = fuel - |S_cov| - p* - 2` and `budget_rec = budget - E - p* - 1` over
`J \ S_cov` with `2*(J.card - |S_cov|)` overhead; the inequality reduces to
`|S_cov| + E ≥ 1`, true since `|S_cov| ≥ 1`. The wrapper's
`fuel = budget + (r+1)(2r+3) ≥ budget + 2r = budget + 2 * J.card` (`J = univ`),
so the top call satisfies it; every recursive call preserves it. `omega` closes
each step given `_budget_le` (`b ≤ budget`, landed in #8498) and the per-size
split-count-vs-budget bound.

## Landed so far on this branch

- `scaledRecombinationSmart{Aux,SizeLoop,CandLoop}_budget_le` (returned budget ≤
  input) and `..._budget_zero` (budget 0 ⇒ `(none,0)`) in the executable file.
- `smartAux_none_budget_zero` and `smartAux_covers_of_bound` (Mathlib layer):
  the two headline helper *statements*, compiling with `sorry` bodies. Fuel
  hypothesis `budget + 3 * J.card + 1 ≤ fuel`.

## Fill plan for the two `sorry` helpers (execute in one coherent pass)

Both are proved by a **mutual `fuel`-structural recursion** over the three exec
loops (pattern: the existing `scaledRecombinationSmart*_budget_le` block). Write
a `mutual … end` block of THREE completeness theorems, then a second block of
THREE coverage theorems consuming completeness. Per-loop fuel hypotheses:
`Aux: budget + 3*J.card + 1 ≤ fuel`; `SizeLoop: budget + 2*J.card + sizes.length ≤
fuel`; `CandLoop: budget + 2*J.card ≤ fuel`. These discharge each recursion's
adequacy by `omega` + `_budget_le`.

Loop-level statements carry the `cover_at_min` witness explicitly (`f_cov`,
`S_cov`, `hf_cov_irr`, `hf_cov_dvd_target`, `hS_cov_J`, `hmin_in_S_cov`,
`hS_cov_rep`) plus, for the enumeration:
- CandLoop: `k` (= `S_cov.card - 1`), `hsplits_enum : ∀ split ∈ splits, split ∈
  (subsetsOfSizeWithComplement tail k).map (fun sc => (head :: sc.1, sc.2))`, and
  `hscov_mem : scovSplit ∈ splits` where `scovSplit =
  (liftedSubsetSelectedList d S_cov, liftedSubsetSelectedList d (J \ S_cov))`.
- SizeLoop: `hcontains : (S_cov.card - 1) ∈ sizes` and `hsizes_suffix : sizes` a
  suffix of `List.range (tail.length + 1)`.

Completeness case analysis (`= (none, b) → b = 0`):
- `Aux`: `target=1`→`some`, contradiction; `budget=0`→`(none,0)`, `b=0`;
  `fuel=0`→adequacy `omega` contradiction; `localFactors=[]`→`J` empty (matches),
  so `target=1` by the `hJ_ne` argument from `covers_of_bound` (uses
  `not_represents_empty_of_irreducible_dvd_core_of_primitive_pos_lc_core_of_bound`),
  contradiction; `head::tail`→derive `S_cov` via `cover_at_min`, delegate to
  `SizeLoop` completeness with `hcontains`/`hsizes_suffix`.
- `SizeLoop`: `sizes=[]`→`hcontains` gives `False`; `budget=0`→`(none,0)`;
  `fuel=0`→adequacy `omega`; `d::ds`: if `CandLoop` returns `some`→contradiction
  with `none`; if `(none, cb)`→ when `d = S_cov.card-1` delegate to `CandLoop`
  completeness (gives `cb=0`, then `_budget_zero` ⇒ `b=0`); when `d ≠` recurse
  `SizeLoop` on `ds` (`hcontains` still holds since `d < S_cov.card-1`).
- `CandLoop`: `splits=[]`→`hscov_mem` gives `False`; `budget=0`→`(none,0)`;
  `fuel=0`→adequacy; `split::rest`: if `split = scovSplit`, it records
  (`shouldRecord_liftedRecoveryCandidate_of_eq_factor` via
  `liftedRecoveryCandidate_eq`) and divides
  (`exactQuotient?_liftedRecoveryCandidate_eq_some_of_eq_factor_of_primitive_pos_lc`),
  so `Aux(quotient_Scov)` is called; by `Aux` completeness (recursion) its
  `none` return has budget `0`, then `_budget_zero` ⇒ `b=0`; if `split ≠
  scovSplit`, `split`'s subset `T ≠ S_cov` at the same size `k` does NOT divide
  (containment `S_cov ⊆ T` + `|T| = |S_cov|` ⇒ `T = S_cov`, contra), so `CandLoop`
  recurses on `rest` (`hscov_mem` still holds; drop `split` from `hsplits_enum`).

Coverage (`= (some result, b) → coverage`): structural peel-extraction gives
`result = cand(T) :: sub` with `Aux(quotient) = (some sub, _)`; show `T = S_cov`
(containment `S_cov ⊆ T`; if `|S_cov| < |T|` then `SizeLoop` reached size
`|S_cov|` with `CandLoop` returning `none`, whose `b` is `0` by the completeness
argument above ⇒ propagates ⇒ overall `none`, contra `some`). Then `cand(T) =
f_cov` is irreducible; recurse via `liftedFactorSubsetPartition_transport` +
`LiftedFactorListMatches.sdiff_of_subset` exactly as `covers_of_bound`.

## Remaining work after the two helpers

Recommended order (completeness first, since coverage consumes it):

1. **Fuel-lockstep / reaching lemmas for `CandLoop`/`SizeLoop`**: under
   `budget + 2 * card ≤ fuel`, a `none` return implies the loop exhausted its
   splits/sizes (never fuel-limited) — so a dividing split `S_cov` present in the
   list *was* examined and its recursive `Aux` was invoked. This is the
   combinatorial "reaching" core; budget and fuel decrease in lockstep per
   `CandLoop` step, so `budget ≤ fuel` is preserved and budget-exhaustion (not
   fuel) is the only early termination.
2. **Step-execution subset identification through the 3 loops**: from a
   `SizeLoop`/`CandLoop` success extract the peeled `T ⊆ J`, `min ∈ T`,
   `cand = liftedRecoveryCandidate core d T`, `cand ∣ target`, and the recursive
   `Aux` on `target / cand` over `J \ T`. Consumes #8412's
   `subsetsOfSizeWithComplement_liftedFactors_exists_subset_of_matches`.
3. **The completeness (`res=none→b=0`) mutual induction**, then the coverage
   (`res=some→coverage`) mutual induction consuming completeness, mirroring
   `covers_of_bound` (Mathlib `Basic.lean:17628`) and reusing its substrate
   verbatim (`cover_at_min`, `liftedFactorSubsetPartition_transport`,
   `coverAtMin_representingSubset_subset_of_liftedRecoveryCandidate_dvd_of_bound`,
   `exactQuotient?_liftedRecoveryCandidate_eq_some_of_eq_factor_of_primitive_pos_lc`,
   `representsIntegerFactorAtLift_primitive_of_bound`, ...). The peel `T = S_cov`
   because containment gives `S_cov ⊆ T` and, if `|S_cov| < |T|`, `S_cov`'s
   recursion at its own size returned `none` ⇒ (completeness) budget `0` ⇒
   propagates ⇒ overall `none`, contradicting the accepted `some`.
4. **Fuel adequacy discharge**: the wrapper passes
   `fuel = budget + (r+1)(2r+3)` (`Basic.lean:7831`) ≥ `budget + 2 * r`, so the
   invariant holds at the top.
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
