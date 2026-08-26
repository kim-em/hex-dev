# Progress — BHKS psiCut adversarial review

## Accomplished

Reviewed the adversarial claim against BHKS arXiv:math/0409510 §3-4 and the
current executable lattice definitions. The strongest refutation is that
per-factor high-bit cuts are not equal to an aggregate cut, but the discrepancy
is a bounded carry from the discarded low digits. With the existing diagonal
period rows, a true support has a short representative whose CLD coordinate is
the aggregate high part plus this bounded carry.

This attacks the claim that per-factor `psiCut` necessarily discards the
identifying information and cannot be patched except by replacing the lattice
with Prop. 4.4 normalized full residues.

## Current frontier

The proof route should establish the carry lemma explicitly:
`sum_i psiCut(x_i)` differs modulo `p^(a-l)` from
`psiCut(sum_i x_i)` by a carry bounded by `O(|S|)`, then combine it with the
BHKS true-factor coefficient bound. An aggregate-cut proof that asserts
equality, or ignores the carry term, is still wrong.

## Next step

If this becomes an implementation task, formalize the carry bound around
`centeredResiduePow_add_pow_mul_psiCut` / `cldCoeffs` and connect it to the
existing lattice period block and `bhksCutRadiusSq4`.

## Blockers

No code changes were made. The review is paper-and-code analysis only.
