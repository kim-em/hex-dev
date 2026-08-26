# Finite-field audit: Tier 2, the subfield embeddings, and the transported instances

## Accomplished

Closed the last five workstream items from the finite-field audit plan.

**Conway Tier 2 (W1c).** `HexConway/Compatibility.lean` proves divisor
compatibility for all 52 committed `(p, m, n)` pairs with `m ∣ n`, by
`decide`. The exponents `(p^n - 1)/(p^m - 1)` are far too large for
modular exponentiation in the kernel, so the norm is computed as a
product of Frobenius images: `1 + p^m + ⋯ + p^((k-1)m)` makes each factor
a modular composition rather than a power. `not_compatible_11_4_6` is
committed alongside as the discriminator, so the checker is known not to
be vacuous.

`HexConway/Primitivity.lean` proves primitivity for 37 committed entries.
The bottleneck was primality of the factors of `p^n - 1`, not field
arithmetic: the linear `Nat.Prime` decision procedure needed 13.8 s for
`3221`, and `13^5 - 1` factors through `30941`. `HexArith`'s new
`prime_of_bounded` takes the trial-division bound as data, since
`Nat.sqrt` uses well-founded recursion and so does not kernel-reduce.
That brings both under 1.1 s. `primitiveCheck` validates the digit lists
it is handed, so a caller cannot supply a bogus factorization.

**Subfield embeddings (W1d).** `HexGFqMathlib/Subfield.lean` builds
`conwayEmbed : GFq p m →+* GFq p n` from the Tier 2 facts, with committed
examples for `GF(2^2) ↪ GF(2^6)`, `GF(2^3) ↪ GF(2^6)`, `GF(2^4) ↪
GF(2^8)`, and `GF(13) ↪ GF(13^6)`. Multiplicativity comes from Mathlib's
`Polynomial.eval₂RingHom`, so no `compose_mul` was needed on the
executable side.

**Transported algebra (W2c).** `HexGF2Mathlib/Algebra.lean` supplies
`CommRing (GF2Poly)` and `Field (GF2nPoly f hirr)` via
`CommRing.ofMinimalAxioms` and `Field.ofMinimalAxioms`.
`HexPolyFpMathlib` gains a `scoped` `CommRing (FpPoly p)`; scoped
because the unscoped instance changed `simp` behaviour in an unrelated
`HexBerlekampZassenhausMathlib` proof.

**Grind instances and the file split (W3a/W3c).** `HexGF2/Field.lean`
became `Field/{Word,Poly,Roots,Grind}.lean` to fit the 2000-line
new-file budget, with the `Lean.Grind` structure bundled in `Grind.lean`.

**SPEC reconciliation (W4) and manual sections 5b–5f.** The SPECs now
describe the shipped `SupportedEntry`/`CommittedEntry`/`PackedGF2Entry`
design; the composite `GF2q n ≃+* GaloisField 2 n` is defined; and the
`GFq` power diamond is closed by pinning `npow` to `GFqField.pow`, so
Mathlib's power lemmas apply to `GFq` for the first time.

Landed as PRs 9295 through 9305.

## Current frontier

The plan's in-scope items are all merged. `HexConway` Tier 3
(lexicographic Conway search) remains deliberately out of scope, and both
the SPEC and the manual chapter say so plainly.

## Next step

File Tier 3 search as its own issue. The `HexGFqRing.PolyQuotient`
`abbrev`-versus-wrapper question also wants an issue of its own; it is a
base-layer representation change with repo-wide blast radius.

## Blockers

None.
