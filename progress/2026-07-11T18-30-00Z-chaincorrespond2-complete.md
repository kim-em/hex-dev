# ChainCorrespond tranche 2 — COMPLETE, PR opened

Branch `real-roots-s6-chaincorrespond2`, PR
https://github.com/kim-em/hex-dev/pull/8745 ("feat: the Sturm chain
correspondence theorems"). All four targets sorry-free; `lake build
HexRealRootsMathlib` green (8747 jobs); check_dag exit 0.

## Accomplished

All in `HexRealRootsMathlib/ChainCorrespond.lean`:

- **Target 1** `toPolyℝ_spem`: `spem f g` is a positive real multiple of the
  field remainder (division-relation form).
- **Target 2** `sturmChain_isSturmChain (p) (hp : 1 ≤ (p.degree?).getD 0)
  (hsq : SquareFreeRat p) : Sturm.IsSturmChain (toPolyℝ (primitivePart p))
  ((sturmChain p).toList.map toPolyℝ)`. Route: degree-drop of `spemStep`
  (leading-term cancellation via `Polynomial.degree_sub_lt`) → fuel never
  truncates (`spem_degree`); pure-list `chainList` mirror of the loop; four
  fuel inductions (nonzero, three-term relation, pairwise coprimality via
  Bezout transport, terminal unit via dvd+coprime); `root_flank` via the
  difference-quotient sign argument (`hasDerivAt_iff_tendsto_slope`) with
  derivative key `s₀' = C γ · s₁`, γ = content ratio > 0.
- **Target 3** `sturmCount_eq_card_roots`, `rootCount_eq_card_roots`:
  composed from `sturm_half_open`/`sturm_line` + `sturmVarAt_eq` + new
  `sturmVarPosInf_eq`/`sturmVarNegInf_eq` + root/squarefree transfers.
- **Target 4** `sepPrec_separates'` (SquareFreeRat-facing wrapper).

## SPEC finding (in PR body)

SPEC's `IsSturmChain (toPolyℝ p)` is unsatisfiable: the chain head is
`primitivePart p`. Stated at the primitive part; root sets agree so the
counting consequences match the SPEC verbatim. Counting theorems take
`1 ≤ (p.degree?).getD 0` explicitly (precedent #8738/#8741).

## Current frontier / next step

Tranche 2 done. Next in the SPEC file layout: `Isolations.lean`
(`RealRootIsolation.exists_unique_root`, `RealRootIsolations.isolates`)
consuming `sturmCount_eq_card_roots`, then `Drivers.lean`
(`isolateSturm?_isSome` via `sepPrec_separates'`).

## Gotchas recorded

- `unfold` fails on cross-module private defs (`spemStep`, `spemAux`,
  `sturmChainAux`): expose the body with a `rfl`-typed `have` instead.
  Public theorems cannot mention those private names in their types.
- `Polynomial.natDegree_eq_zero_of_derivative_eq_zero` is deprecated:
  use `Polynomial.derivative_eq_zero` (iff form).
- `rw [mul_neg_one]` can hit an Int-level product inside a cast before the
  ℝ-level one; apply twice or push_cast first.

## Blockers

None.
