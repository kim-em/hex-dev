# Number-field tower rational embedding

## Accomplished

- Added the dependent `NumberTower.Extension` result and the checked
  `ofQAdjoin` smart constructor for one-level extensions of `rat`.
- Normalized negative-leading input presentations by a global sign while
  preserving the chosen isolation, and stored the corresponding positive-
  leading absolute root.
- Constructed the monic rational defining relation, canonical base embedding,
  and generator coordinates without exposing raw tower constructors.
- Added compiled regressions for both `X² - 2` and `2 - X²`, covering tower
  dimension, the generator relation, inversion, and rational embedding.
- Verified `lake build HexNumberFieldTower.Embed` and the full `lake build`.

## Current frontier

The rational one-level constructor and mixed-radix arithmetic are executable.
Generic adjoining still needs the recursive tower factorization and fixed-
embedding factor-selection machinery.

## Next step

Implement the one-level norm/resultant primitives and the checked
factorization result, then build Yun/Trager factorization over a tower.

## Blockers

None.
