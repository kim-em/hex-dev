# Review and revision of the six SPEC/Libraries/ specs

## Accomplished

Interactive session with Kim: reviewed the six planned-library specs
(hex-roots, hex-roots-mathlib, hex-resultant, hex-resultant-mathlib,
hex-number-field, hex-number-field-mathlib) for mathematical errors,
implementer-sufficiency, and language, then rewrote all six plus
README.md, with Kim's approval of the plan and three decisions
(rewrite design-level sections in place; rename `Hex.NumberField` to
`Hex.QAdjoin`; full pass on README.md).

Design-level fixes applied to the specs:

- hex-roots: replaced the unsound "squared Pellet witness" with
  per-term dyadic bounds (`max(|Re|,|Im|)` minorant, `|Re|+|Im|`
  majorant, `181/128 < √2 < 1449/1024`); made clusters edge-connected
  components of grid squares (re-boxing to one square stalled
  refinement); made isolations carry the strong three-radius witness;
  `prec` is now `Int` (Cauchy squares have half-width > 1); drivers
  are fueled and `Option`-valued, with completeness explicitly
  deferred to the companion; `SimpleRoot` is now a `Quot` over
  disc-intersection on isolations refined past `mahlerPrec` (which
  now guarantees radius < sep/4), with `sameRoot : Bool` and no
  in-library `DecidableEq`; dropped the ill-defined round-down
  canonicalisation (`out`) entirely.
- hex-number-field: `AlgebraicNumber` now carries a working
  `RefinedIsolation` representative and uses `BEq`; irreducibility is
  an executable `Hex.ZPoly.isIrreducible : Bool` (a small planned
  addition to hex-berlekamp-zassenhaus) so the Mathlib-free layer can
  construct the proofs it needs; fixed the transposed `commonField`
  resultant, the degree-1 `toQAdjoin` case, and the reducible-`p`
  unsoundness of `toAlgebraicNumber`; added the missing
  hex-matrix/hex-row-reduce dependencies (also in libraries.yml and
  README).
- hex-number-field-mathlib: `AdjoinRoot` now taken over ℚ (was ℤ, an
  order, not the field); Gauss's lemma citation added; the false
  bijectivity statement replaced by injectivity-per-BEq plus range
  characterisation; scope re-stated honestly (Convert/CommonField
  correctness are the substantive obligations).
- hex-resultant(-mathlib): corrected complexity contract (O(min(n,m))
  steps, O(n·m) coefficient ops), removed the impossible
  bench-against-noncomputable-Mathlib plan, documented the `R = ZPoly`
  bivariate instantiation, unified `subresultant`/`resultant` naming,
  fixed the wrong claim that HexRootsMathlib needs
  `disc_ne_zero_of_squarefree`.
- Citation fixes throughout, verified against /home/kim/mathlib4 and
  the v4.32.0-rc1 toolchain: `cbv_decide` does not exist (now
  `decide`); `Dyadic.invAtPrec` and its two lemmas do exist (and
  `divAtPrec` exists, contradicting the old "hypothetical" remark);
  `MinpolyOver` does not exist; `IntermediateField.algebraicClosure`,
  `primPart`, `EuclideanDomain.gcd_eq_zero_iff`,
  `Polynomial.IsPrimitive.Int.irreducible_iff_irreducible_map_cast`
  are the right names; Mahler separation is the 1964 Michigan Math. J.
  paper; Brown is 1978; python-flint class is `fmpz_poly`;
  `0xHEC0FFEE` was not a hex literal.
- Language pass per SPEC/writing-style.md over all seven files: no
  em-dashes, no "bridge"/"core"/"smoke"/"gate", no semicolon run-ons,
  metaphors literalised, conformance/bench paths corrected to the
  `conformance/HexX/` + `bench/HexX/` layout, README dead links now
  point at `HexFoo/SPEC/hex-foo.md`.

Changes are uncommitted (8 files modified), awaiting Kim's review of
the diff.

## Current frontier

The specs are internally consistent and, I believe, implementable.
The known-open design risks are recorded inside the specs themselves:
fuel sufficiency (hex-roots completeness development, deferrable) and
the size of the Rouché-on-circles formalisation.

## Next step

Kim reviews the diff, then commit. When implementation starts,
hex-resultant is the natural first library (smallest, no open
questions); hex-roots next; hex-number-field last (its
`isIrreducible` prerequisite lands in hex-berlekamp-zassenhaus
first).

## Blockers

None. One note outside this change's scope:
`SPEC/lean4-stdlib-inventory.md` predates `Init.Data.Dyadic` and
should be refreshed.
