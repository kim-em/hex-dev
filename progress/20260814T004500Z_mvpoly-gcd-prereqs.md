# HexMvPoly additions for hex-mv-gcd

## Accomplished

Two of the three additions `SPEC/Libraries/hex-mv-gcd.md` asks of
`HexMvPoly` are implemented and proved. Both were checked against the source
rather than the SPEC text, and one SPEC claim did not survive that check.

**The `Lean.Grind` ring tower** (`HexMvPoly/Ring.lean`, new). `NatCast`,
`OfNat`, `SMul Nat`, `IntCast`, `SMul Int`, then
`Lean.Grind.Semiring`, `Lean.Grind.Ring`, and `Lean.Grind.CommRing` on
`MvPoly n R cmp`. This is the addition that matters outside this library:
every `HexResultant` correctness theorem takes `[Lean.Grind.CommRing S]`
(`HexResultant/Subresultant.lean:152` and following), so without it the
subresultant chain computes over multivariate coefficients and none of its
theorems apply. `HexResultant/ExactDiv.lean:255-434` is the `DensePoly`
tower this mirrors.

Almost all of it is packaging: `HexMvPoly/Operations.lean` already proves
`add_zero`, `add_comm`, `add_assoc`, `mul_assoc`, `mul_one`, `one_mul`,
`mul_add`, `add_mul`, `zero_mul`, `mul_zero`, `mul_comm`, and `pow_succ`.
What was missing and is added here: `neg_zero`, `neg_neg`, `neg_add_cancel`,
`pow_zero`, `ofNat_succ`, `ofNat_eq_natCast`, `coeff_ofNat`, `coeff_natCast`.

One trap worth recording. `pow_zero` is not `rfl`: `npowBySq` is defined by
well-founded recursion, so it is `@[irreducible]` and `rfl` does not see
through it. The equation lemma (`simp [npowBySq]`) does.

Unlike `DensePoly`, no separate `natPow` was needed. `MvPoly` already has a
`Pow _ Nat` instance and a proved `pow_succ` for it, so the `Semiring.npow`
field uses the existing operation rather than introducing a second one.

**`mapCoeffs` and its homomorphism laws** (`HexMvPoly/Structural.lean`).
`mapCoeffs φ p` maps `φ` over the backing values and drops the terms it sends
to zero, with `coeff_mapCoeffs`, `mapCoeffs_zero`, `mapCoeffs_one`,
`mapCoeffs_add`, and `mapCoeffs_mul`.

The SPEC claimed hex-mv-poly had no coefficient map at all. That is wrong:
`Structural.bind` takes `f : R → S` alongside the variable map, so
`bind φ X` already is one. The real gaps are cost and laws. `bind` folds
`acc + C (f c) * Mono.prod g m` over the terms, one polynomial addition and
one monomial product each, so a pure coefficient map through it is quadratic
in the term count where a map over the values is linear, and reduction modulo
a prime is on the inner loop of every modular algorithm hex-mv-gcd specifies.
And `bind` carries no homomorphism laws, which is what the certificate needs.

The laws take their hypotheses on `φ` explicitly rather than through a
bundled homomorphism record, because nothing else in this library needs such
a record and a caller can bundle as it likes.

Not proved: `mapCoeffs_bind`, the agreement between `mapCoeffs φ` and
`bind φ X`. `bind` has no coefficient characterisation to prove it against,
so it would mean first proving `coeff_bind`, which is work about `bind`
rather than about this addition.

**`monoContent` came off the list.** `Mono.gcd` already exists and the fold
over `support` is three lines that belong with the content operations in
hex-mv-gcd, not here.

## Current frontier

The arity-preserving recursive view is **not** in this PR. The design is
settled and one SPEC decision is now known to be wrong.

The SPEC proposed a `Without i R cmp` subtype so that "the coefficients do
not involve `xᵢ`" holds in the type. That is the wrong trade: anything
downstream has to compute with those coefficients, so the subtype would need
the entire `HexMvPoly.Ring` tower above rebuilt on it, where plain
`MvPoly n R cmp` coefficients already have it. The view should therefore
return `DensePoly (MvPoly n R cmp)` and carry the invariant as a theorem.

The shape that was drafted (kept at `/tmp/slice-wip.lean`, not committed):

- `setAt i e m` replacing the `xᵢ` exponent, with `degreeOf_setAt`,
  `setAt_degreeOf`, `setAt_setAt`, and `setAt_zero_of_degreeOf_eq_zero`;
- `coeffIn i e p`, the `xᵢ`-degree-`e` slice with the exponent cleared,
  defined as a `foldTerms` in the style of `derivative`;
- `coeff_coeffIn`, characterising it as
  `if degreeOf i m = 0 then coeff (setAt i e m) p else 0`;
- `degreeIn?`, `leadingCoeffIn`, then `coeffsIn` / `ofCoeffsIn` and the
  round trips.

Two things make it larger than it looks, and are why it is not here. The
`coeff_rename` / `coeff_derivative` idiom (an `aux` induction turning the
`addMonomial` fold into a fold of conditional coefficient adds, then a `step`
lemma identifying the selected terms) is reusable but has to be redone for
each operation. And the existing arity-dropping development in
`HexMvPoly/Recursive.lean` is 436 lines with three private fold lemmas and
four round-trip theorems; the arity-preserving one parallels it.

It also deserves a premise check before it is built: `Recursive.lean`
already proves `toUnivariate_coeff`, `ofUnivariate_coeff`, and both round
trips, so the alternative is for hex-mv-gcd to use the arity-dropping view
and pay the reindexing, rather than have hex-mv-poly grow a second
development. That is a SPEC decision, not an implementation one.

## Next step

Decide the view question above, then implement whichever wins. Nothing else
in hex-mv-gcd's milestone 1 is blocked: exact division, the `Div` and
`ExactDivLaws` instances, `monoContent`, `contentIn`, and `primPartIn` all
live in hex-mv-gcd and need only the ring tower landed here.

## Blockers

None. Both landed additions build clean with no new warnings, and
`#print axioms` on `instGrindCommRing`, `mapCoeffs_mul`, and
`coeff_mapCoeffs` reports only `[propext, Classical.choice, Quot.sound]`.
