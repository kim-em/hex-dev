library: HexBerlekampZassenhaus

## Current state

Sub-issue B of #6584. After sub-issue A renames
`factorSlow → factorSlowModular` and makes the public entry points
`Option`-returning, the silent compatibility fallback
`choosePrimeDataFallback` (`HexBerlekampZassenhaus/Basic.lean` lines
~2117–2121, taking `p := 3, factorsModP := #[]`) is no longer
reachable from the public three-tier combinator, but is still
defined and still reachable through the total
`choosePrimeData` wrapper. This sub-issue removes the fallback and
tightens the remaining `choosePrimeData` (total) call sites.

Survey at the time of writing (after #6583, before sub-issue A):
121 `choosePrimeData[^?A-Za-z_]` token matches across both
libraries — most are lemma names like
`*_of_choosePrimeData` (renaming optional) or docstrings. Actual
function-call sites in `HexBerlekampZassenhaus/Basic.lean` are
~12 (lines 6617, 6654, 6779, 7945, 7950, 7978, 13232, 13235,
14371, 14376, 14384, 14389 plus the `def` and two `Nat.Prime` /
`choosePrimeData_eq_of_choosePrimeData?_some` theorem statements at
2141–2143 and 2441) and `HexBerlekampZassenhausMathlib/IntReductionMod.lean`
adds one term-level use at line 282
(`primeData = Hex.choosePrimeData core`).

## Deliverables

Single PR.

1. Remove `choosePrimeDataFallback` from
   `HexBerlekampZassenhaus/Basic.lean` (lines ~2117–2121) and any
   reference to it in proofs (notably the `[hdata,
   choosePrimeDataFallback]` `simpa` at line ~2447).

2. Pick the `choosePrimeData` strategy after a fresh
   call-site survey on the post-A tree:
   - Preferred: remove `choosePrimeData` entirely if all remaining
     callers have (or can obtain locally) a `choosePrimeData? sf =
     some primeData` witness. Migrate each caller to take that
     witness as a hypothesis (or `Option.rec` directly on
     `choosePrimeData? sf`).
   - Alternative: keep `choosePrimeData` but rewire its body to
     `(choosePrimeData? f).get!` or an `Option.get` with a witness
     hypothesis, so the no-admissible-prime branch is no longer
     silent. The PR must explicitly justify why the preferred
     removal was not feasible.

   Identifier names containing `_choosePrimeData` (e.g.
   `factor_small_mod_singleton_branch_entry_irreducible_of_choosePrimeData`)
   may stay; the rename is mechanical and out of scope unless the
   lemma's body changes.

3. Bridge updates in
   `HexBerlekampZassenhausMathlib/Basic.lean`,
   `HexBerlekampZassenhausMathlib/UFDPartition.lean`, and
   `HexBerlekampZassenhausMathlib/IntReductionMod.lean` (the
   `_hselected : primeData = Hex.choosePrimeData core` hypothesis at
   line ~282 likely needs reshape to `choosePrimeData? core = some
   primeData`).

## Library placement

- `HexBerlekampZassenhaus/Basic.lean`
- `HexBerlekampZassenhausMathlib/Basic.lean`
- `HexBerlekampZassenhausMathlib/UFDPartition.lean`
- `HexBerlekampZassenhausMathlib/IntReductionMod.lean`

## Verification

- `lake build HexBerlekampZassenhaus` green.
- `lake build HexBerlekampZassenhausMathlib` green.
- `lake exe hexbz_bench list` and
  `lake exe hexbz_bench verify --filter runFactor` complete within
  budgets.
- No new forbidden tokens (`axiom`, `native_decide`, `TODO`, `FIXME`,
  `sorry`).
- `grep choosePrimeDataFallback` returns nothing.

## Out of scope

- The `factorSlow → factorSlowModular` rename and `Option`-signature
  migration — sub-issue A. This PR builds on top of A's tree.

depends-on: #6584
