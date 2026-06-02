# BHKS CLD coefficient-bound replan

Issue #6217 replaces the old #5224 target after a counterexample showed that
the executable statement
`abs (cldCoeffs input p k g[j]) <= bhksCoeffBound input j` is false for the
current code.

## Decision

Use the SPEC-preserving executable correction: center the ambient `p^a`
representative before applying the lower `Psi^a_ell` cut.

The counterexample is caused by applying `psiCut` to the nonnegative
`mod p^a` representative emitted by `cldQuotientMod`. A negative exact
coefficient of `Phi(g) = f * g.derivative / g` can therefore appear as
`p^a - c`, and the cut sees a large high-bit value instead of the small
integer coefficient intended by BHKS.

Centering at the ambient precision before the lower cut restores the documented
meaning of `cldCoeffs`:

```text
Psi^a_{ell_j}([x^j] Phi(g_i))
```

where the coefficient is interpreted as the centered representative modulo
`p^a`.

## Rejected alternatives

- Replacing the column bound by `p^(k - ell_j)` is true for the current
  executable but weakens the downstream D1 chain. It would force #5204, #5216,
  and #5237 to carry a precision-dependent column norm instead of the
  BHKS Lemma 5.1 `bhksCoeffBound` norm.
- Adding per-coordinate constraints on `k` conflicts with the single ambient
  precision used by the executable BHKS path.

## Successor work

- #6220 fixes the executable CLD cut semantics and restores the Lemma 5.1
  column-bound bridge.
- #6221 repairs the `BHKS.auxiliaryPolynomial` shape so the bad-vector
  polynomial accounts for the diagonal lattice-row correction coordinates.

Downstream issues #5204, #5512, #5216, and #5237 should consume the restored
`bhksCoeffBound` column bound after #6220, and the corrected auxiliary
polynomial after #6221.
