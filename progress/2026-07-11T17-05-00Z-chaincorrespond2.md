# ChainCorrespond tranche 2 — spem correspondence + transfers + chain head

Branch `real-roots-s6-chaincorrespond2` (pushed, no PR: targets 1-3 not all
sorry-free). All additions in `HexRealRootsMathlib/ChainCorrespond.lean`.

## Accomplished (all sorry-free, `lake build HexRealRootsMathlib` green, check_dag=0)

- **Target 1 complete.** `toPolyℝ_spem`: for a nonconstant divisor `g`
  (`g.leadingCoeff ≠ 0`, `1 ≤ (g.degree?).getD 0`), the executable
  `spem f g` is a positive real multiple of the field remainder:
  `∃ c > 0, ∃ Q, C c · toPolyℝ f = Q · toPolyℝ g + toPolyℝ (spem f g)`.
  Supporting: `toPolynomial_scale`/`toPolynomial_shift` (generic),
  `toPolyℝ_scale`/`toPolyℝ_shift`/`toPolyℝ_sub`/`leadingCoeff_toPolyℝ`,
  `toPolyℝ_spemStep` (per-step identity), `spemAux_relate` (fuel induction).
- **Target 3 prerequisites** (Codex-flagged): `separable_toPolyℝ`
  (`Squarefree (toPolyℚ p) → (toPolyℝ p).Separable`),
  `roots_toPolyℝ_eq_primitivePart` (nonzero `p` and its primitive part have
  the same real roots).
- **Target 2 partial** (structural fields only): `sturmChainAux_toList_prefix`,
  `sturmChain_toList_eq` (chain = `primitivePart p :: primitivePart p' :: tail`),
  `sturmChain_map_head?` (= `IsSturmChain.head`), `sturmChain_map_ne_nil`
  (= `IsSturmChain.nonempty`).

## Current frontier

`sturmChain_isSturmChain` (target 2) is NOT stated/proved. The four analytic
fields remain: `nonzero_mem`, `consec_coprime`, `interior_alternates`,
`root_flank`, `last_no_root`. Target 3 (`sturmCount_eq_card_roots`,
`rootCount_eq_card_roots`) blocked on target 2. Target 4 (`sepPrec_separates'`)
not attempted.

## Next step

- `interior_alternates`: evaluate the `toPolyℝ_spem` relation for consecutive
  chain elements at a zero of the middle element — `C c · prev = spem` there
  (with `next = −primitivePart(spem prev cur)`, a negative multiple), giving
  the opposite-sign flank. Needs a `toPolyℝ(primitivePart r)` = positive · `toPolyℝ r`
  lemma (mirror of `roots_toPolyℝ_eq_primitivePart`, at the poly not roots level).
- `consec_coprime`/`last_no_root`: the remainder-chain-to-gcd argument; the
  terminal element is a nonzero constant for squarefree `p`
  (`squareFreeRat_iff` + gcd machinery).
- `root_flank`: simple-root sign analysis, reuse `eval_sign_eq_of_no_zero`-style
  neighbourhood reasoning from `SturmTheorem.lean`.

## Blockers / findings

- **SPEC unsoundness (recorded design note confirmed):** the SPEC states
  `IsSturmChain (toPolyℝ p) ...`, but the executable chain's head is
  `primitivePart p`, not `p` (content stripped). `IsSturmChain` must be stated
  at `toPolyℝ (primitivePart p)` (or `p` assumed primitive). `sturmChain_map_head?`
  is stated accordingly.
- Cross-module reference gotcha: `unfold` fails on the private `spemStep`/`sturmChainAux`
  ("Unknown constant"); use a `rfl`-based `have` to expose the body instead. A
  *public* theorem cannot reference these private defs in its TYPE — helpers that
  do must be `private` (public theorems only mention `spem`/`sturmChain`).
