# HexNumberField fixed-field roots

## Accomplished

- Added characteristic-zero Yun decomposition over checked `QAdjoin`
  arithmetic, retaining positive multiplicity indices.
- Added global rational-denominator clearing and the integer norm eliminant
  `Res_y(p(y), F(y,t))` for each square-free component.
- Added checked norm-root isolation and bounded rejection of candidates from
  conjugate embeddings using exact lazy evaluation eliminants and certified
  Horner balls.
- Added semantic duplicate merging, deterministic polynomial/isolation sorting,
  `QAdjoin.roots?`, and its loud total wrapper.
- Added compiled checks for zero and constant inputs, a repeated root, and the
  `T - sqrt(2)` conjugate-impostor case; rebuilt `HexNumberField.Roots` and the
  umbrella target successfully.

## Current frontier

The fixed-field root API is operational. `AlgebraicPoly.roots?` still requires
the deterministic many-coefficient common-field construction specified by the
library contract.

Two completed independent reviews also identified soundness/completeness fixes
needed in the stacked lazy-arithmetic and disambiguation ancestors. Those fixes
will be applied before the roots stack is advanced further.

## Next step

Patch and rebase the reviewed ancestor PRs, then implement the common primitive
field embedding used by `AlgebraicPoly.roots?`.

## Blockers

None.
