# Mahler separation bound: `sepPrec_separates`

## Accomplished
Proved `HexRealRootsMathlib.sepPrec_separates` (the Mahler root-separation
bound) sorry-free in `HexRealRootsMathlib/Separation.lean`. The target is
stated over `toPolyℂ p` with an explicit `Separable` hypothesis on the
`ℚ`-image (the `SquareFreeRat` bridge is a parallel PR; `squareFreeRat_iff`
discharges it). `lake build HexRealRootsMathlib` is green; `check_dag`
passes; `#print axioms` on the theorem is the standard trio only
(`propext`, `Classical.choice`, `Quot.sound`).

New declarations (all Hex-free except the last, upstreamable to Mathlib):

- `coeff_toPolyℂ`, `natDegree_toPolyℂ`, `leadingCoeff_toPolyℂ`,
  `toPolyℂ_eq_map` — symmetric `toPolyℂ` cast bridges (Codex review ask).
- `norm_pow_sub_pow_le` — divided-difference entry bound
  `‖yⁱ − xⁱ‖ ≤ i·Cⁱ⁻¹·‖y − x‖` via `geom_sum₂_mul`.
- `sqrt_sum_pow_sq_le` — ordinary Vandermonde column L² bound.
- `sqrt_sum_sub_pow_sq_le` — isolating (differenced) column L² bound.
- `sqrt_sum_sq_le` — `√(∑ i²) ≤ (√N)³`.
- `norm_det_vandermonde_le` — Mahler's isolating-column bound (Hadamard on
  the row-reduced Vandermonde; the WLOG `‖z₁‖ ≤ ‖z₂‖` makes the degree-(N−2)
  difference row cancel the excess, hitting the constant `N^{(N+2)/2}`).
- `norm_prod_roots_eq_sq` — off-diagonal root product `= ‖det V‖²` in norm
  (Multiset→Fin glue + `prod_comm'` triangular swap).
- `norm_discr_eq` — `‖disc f‖ = ‖lc‖^{2n−2}·‖det V‖²`.
- `pow_le_two_pow_sepExp` — the closed-form/`ceilLog2Nat` numeric assembly,
  done without real logarithms (square-and-compare against `2^E`).

Inequality proved: the constant-free form
`sep ≥ n^{−(n+2)/2}·|disc|^{1/2}·M^{−(n−1)}` (drops Mahler's `√3`, which the
implemented `sepPrec` also drops), which is exactly what the `+3` margin in
`sepPrec` needs for the strict `/4` bound.

## Current frontier
`sepPrec_separates` complete and merge-ready.

## Next step
Wire it to `Hex.SquareFreeRat` once `squareFreeRat_iff` lands (parallel PR),
then consider hosting the shared proof in `hex-poly-z-mathlib` per SPEC.

## Blockers
None.
