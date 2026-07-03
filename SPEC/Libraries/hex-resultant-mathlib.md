# hex-resultant-mathlib (depends on hex-resultant + hex-poly-mathlib + Mathlib)

Mathlib companion for `hex-resultant`. **Scope-limited**: proves only
the "resultant zero iff common root" property, not the equality of
`Hex.DensePoly.resultant` with `Polynomial.resultant`.

## Why scope-limited

The full `Hex.DensePoly.resultant f g = Polynomial.resultant
(toPolynomial f) (toPolynomial g)` would require formalising the
classical correspondence between the subresultant chain and the
Sylvester-matrix determinant, roughly 1500-2000 lines of substantive
computer algebra in Mathlib: pseudo-remainder steps as row operations
on the Sylvester matrix with specific scale factors, subresultants as
leading coefficients of reduced Sylvester submatrices, and the
resultant as a product over the chain with sign corrections.

We don't need it. The downstream consumer
(`hex-number-field-mathlib`'s correctness theorems for
`AlgebraicNumber` arithmetic) only needs the property "the resultant
of two polynomials is zero iff they share a common root in the
algebraic closure". That property suffices for proofs like "`α + c·β`
is a root of `resultant_y(β.p(y), α.p(t − c·y))`", the key ingredient
of `commonField` correctness.

The narrower theorem can be proved by analysing the pseudo-remainder
chain directly, without the Sylvester-determinant connection, in
roughly 600 lines.

## What we cite from Mathlib (no work)

- `Polynomial`, `Polynomial.eval`, polynomial arithmetic.
- `Polynomial.modByMonic` and friends. Mathlib has the monic case of
  polynomial division. We define the non-monic pseudo-remainder on
  top.
- `IsAlgClosed` and polynomial roots over ℂ
  (`Mathlib.FieldTheory.IsAlgClosed.Basic`,
  `Mathlib.Analysis.Complex.Polynomial.Basic`).
- gcd theory over polynomial rings, for the connection "gcd is
  constant iff no common roots" (for example
  `EuclideanDomain.gcd_eq_zero_iff` and the `EuclideanDomain.gcd`
  API for `ℚ[X]`).

## What we explicitly do NOT prove

- `Hex.DensePoly.resultant f g = Polynomial.resultant (toPolynomial f)
  (toPolynomial g)`: full resultant equality. Reserved for a future
  Mathlib contribution formalising the subresultant-Sylvester
  correspondence.
- The root-product formula `Hex.resultant f g = lc(f)^(deg g) · ∏
  g.eval αᵢ`. Requires splitting-field machinery; not needed for our
  use cases.
- Discriminant equality `Hex.disc f = Polynomial.discr (toPolynomial
  f)`. Provable from the full equality but not from the narrow
  property.

## Theorem chain (~600 lines total)

Stated for `f, g : ZPoly` with roots taken in ℂ, which is all the
downstream consumers need. (The chain analysis itself works over any
UFD with roots in the algebraic closure of its fraction field, but we
do not state that generality.)

1. **Pseudo-division correctness on `Polynomial`** (~100 lines).
   Define `Polynomial.pseudoRem (f g : Polynomial R) : Polynomial R`
   for any commutative ring `R`, satisfying
   `lc(g)^(deg f − deg g + 1) · f = q · g + pseudoRem f g`
   for some `q : Polynomial R`, with `deg (pseudoRem f g) < deg g`.
   Mathlib has the monic case, and the non-monic case is a
   straightforward induction.

2. **Subresultant chain construction over `Polynomial`** (~150 lines).
   `F₀ := f`, `F₁ := g`, `F_{k+1} := pseudoRem F_{k-1} F_k` while
   `F_k ≠ 0`. The chain terminates with some `F_N = 0`.

3. **Pseudo-division preserves common roots forward** (~30 lines).
   If `α` is a common root of `F_{k-1}` and `F_k`, then `α` is a
   root of `F_{k+1}`. Evaluate the pseudo-division identity at `α`:
   the left side vanishes, so `F_{k+1}(α) = -q(α) · F_k(α) = 0`.

4. **Pseudo-division preserves common roots backward** (~50 lines).
   If `α` is a root of `F_k` and `F_{k+1}`, then `α` is a root of
   `F_{k-1}`. From the pseudo-division identity,
   `lc(F_k)^d · F_{k-1}(α) = 0`. The leading coefficient `lc(F_k)`
   is a nonzero integer, hence nonzero in ℂ, so `F_{k-1}(α) = 0`.

5. **The chain computes a gcd** (~150 lines).
   The chain ends with `F_N = 0`; the last nonzero element `F_{N-1}`
   is `gcd(f, g)` up to a nonzero rational factor. By induction using
   items 3 and 4, the common complex roots of `f` and `g` are
   precisely the roots of `F_{N-1}`.

6. **The `Hex.resultant` value and the chain** (~50 lines).
   `Hex.DensePoly.resultant f g = 0` iff the chain's last nonzero
   element has positive degree (a non-trivial gcd).

7. **Hex-Mathlib transfer** (~50 lines).
   The chain built from `Hex.DensePoly` values and the chain built
   from `Polynomial` values correspond under the `HexPolyMathlib`
   ring equivalence: the two constructions are structurally identical
   on isomorphic representations, so the transfer is step-by-step.

8. **Final theorem** (~50 lines):

   ```lean
   theorem Hex.DensePoly.resultant_eq_zero_iff_common_root
       (f g : ZPoly) (hf : f ≠ 0) (hg : g ≠ 0) :
       Hex.DensePoly.resultant f g = 0
         ↔ ∃ α : ℂ, (toPolynomial f).aeval α = 0
                  ∧ (toPolynomial g).aeval α = 0
   ```

   Combine items 5, 6, 7. The nonzeroness hypotheses rule out the
   degenerate `resultant 0 g = 0` cases, which have no common-root
   meaning.

## Discriminant non-vanishing corollary

```lean
theorem Hex.DensePoly.disc_ne_zero_of_squarefree (f : ZPoly)
    (hf : Squarefree (toPolynomial f)) :
    Hex.DensePoly.disc f ≠ 0
```

Follows from item 8: `disc f = 0 ↔ resultant f f' = 0 ↔ f, f' share
a common root ↔ f has a multiple root ↔ ¬ Squarefree f`.

Recorded because it is immediate from item 8 and gives consumers of
`Hex.disc` the standard squarefreeness criterion. Note that
`hex-roots-mathlib` does **not** need it: its `mahlerPrec` correctness
argument uses Mathlib's `Polynomial.discr` throughout and never
mentions `Hex.disc`.

## File organisation

```
HexResultantMathlib/
  Basic.lean         : public statements (resultant_eq_zero_iff_common_root,
                       disc_ne_zero_of_squarefree)
  Subresultant.lean  : items 1-7 (the chain analysis)
  Discriminant.lean  : the discriminant corollary
```

`Subresultant.lean` is the substantive file. Items 1-5 mention no
`Hex` type, so that part can be prepared as a Mathlib contribution
(subresultant chain definition plus the common-root property)
independently of the rest of `hex`. The library is verified by
building it. The conformance fixtures live with `hex-resultant`.

## Practical staging

`hex-resultant` (computational) lands first. `hex-resultant-mathlib`
lands later: substantial but bounded at ~600 lines, far more tractable
than the full Sylvester correspondence would be.

## References

- See [hex-resultant.md](hex-resultant.md) for the subresultant
  references (Collins, Brown, Geddes-Czapor-Labahn, von zur Gathen
  and Gerhard).
- For the common-root property specifically: von zur Gathen and
  Gerhard, *Modern Computer Algebra* (3rd ed. 2013), §6 is the
  closest presentation to the one used here.
