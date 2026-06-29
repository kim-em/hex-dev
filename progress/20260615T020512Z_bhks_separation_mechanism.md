# Progress — BHKS separation mechanism audit

## Accomplished

Read the latest progress note, the local BHKS bad-vector/resultant scaffolding,
and the BHKS paper sections around Lemma 3.2, Theorem 3.1, Theorem 4.3,
Proposition 4.4, and Theorem 4.6.

Main conclusion: the executable cut auxiliary polynomial is not the object that
carries the resultant divisibility.  The published separation proof assumes a
larger retained subgroup, then uses Lemma 3.2 to modify a retained non-true
element by true-factor generators into a different small element whose uncut
CLD representative has a local divisibility property and no global-factor
divisibility; the resultant contradiction is applied to that uncut
representative.

## Current frontier

The existing abstract bad-vector resultant layer is not intrinsically wrong if
its `H` is interpreted as the uncut BHKS `POL(g) mod p^a` witness produced after
the Lemma 3.2 modification.  It is wrong if instantiated with
`auxiliaryPolynomialWithCorrections`, the scaled high-bit cut polynomial.

## Next step

Refactor the pending reverse-inclusion proof obligations to construct the
Lemma-3.2 modified exponent vector and its uncut CLD polynomial `H`, with the
cut lattice used only to prove the needed coefficient/norm bound on `H`.

## Blockers

No code changes were attempted.  The remaining mathematical obligation is to
bridge from the executable cut coordinates plus diagonal corrections to a bound
on the uncut `H` used in the resultant argument.
