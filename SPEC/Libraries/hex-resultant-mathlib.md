# hex-resultant-mathlib (depends on hex-resultant + hex-poly-mathlib + Mathlib)

Mathlib bridge for `hex-resultant`. **Scope-limited**: proves only the
"resultant zero iff common root" property, not the full equivalence
between `Hex.DensePoly.resultant` and `Polynomial.resultant`.

## Why scope-limited

The full `Hex.resultant f g = Polynomial.resultant (toPolynomial f)
(toPolynomial g)` would require formalising the classical "subresultant
chain ↔ Sylvester-matrix determinant" theorem (~1500–2000 lines of
substantive computer-algebra theory in Mathlib): pseudo-remainders ↔
elementary row operations on Sylvester with specific scale factors,
subresultants are leading coefficients of reduced Sylvester
submatrices, resultant = product over the chain with sign corrections.

We don't need it. Downstream consumers (specifically
`hex-number-field-mathlib`'s correctness theorems for
`AlgebraicNumber` arithmetic) only need the **fundamental property**:
"subresultant of two polynomials is zero iff they share a common root
in the algebraic closure". That property suffices for proofs like
"`α + β` is a root of `resultant_y(p_α(y), p_β(t − y))`" (which is the
core ingredient of `commonField` correctness).

The narrower theorem can be proved via subresultant *chain analysis*
without going through the Sylvester-determinant connection at all,
in roughly 600 lines.

## What we cite from Mathlib (no work)

- `Polynomial`, `Polynomial.eval`, polynomial arithmetic.
- `Polynomial.modByMonic` and friends — Mathlib has the monic case of
  polynomial division. We define the non-monic pseudo-remainder on
  top.
- `Polynomial.IsAlgClosed`, `algClosure`, polynomial roots over the
  algebraic closure (`Mathlib.FieldTheory.IsAlgClosed.Basic` and
  related).
- `Polynomial.gcd_eq_zero_iff` and gcd theory over polynomial rings —
  for the connection "gcd is constant iff no common roots".

## What we explicitly do NOT prove

- `Hex.DensePoly.resultant f g = Polynomial.resultant (toPolynomial f)
  (toPolynomial g)` — full resultant equality. Reserved for a future
  Mathlib contribution that formalises the subresultant ↔ Sylvester
  bridge upstream.
- The root-product formula `Hex.resultant f g = lc(f)^(deg g) · ∏
  g.eval αᵢ`. Requires splitting-field machinery; not needed for our
  use cases.
- Discriminant equality `Hex.disc f = Polynomial.discr (toPolynomial
  f)`. Provable from a stronger bridge but not from the narrow
  property. Downstream uses (HexRootsMathlib's Mahler-bound
  development) need `|disc p| ≥ 1` for nonzero squarefree `p`, which
  follows from "disc is a nonzero integer when `p` is squarefree" via
  the common-root path: `disc p = res(p, p') ≠ 0 ↔ p, p' have no
  common roots ↔ p is squarefree`.

## Theorem chain (~600 lines total)

1. **Pseudo-division correctness on `Polynomial`** (~100 lines).
   Define `Polynomial.pseudoRem (f g : Polynomial R) : Polynomial R`
   for any commutative ring `R`, satisfying
   `lc(g)^(deg f − deg g + 1) · f = q · g + pseudoRem f g`
   for some `q : Polynomial R`, with `deg(pseudoRem f g) < deg g`.
   Mathlib has the monic case; non-monic is straightforward induction.

2. **Subresultant chain construction over `Polynomial`** (~150 lines).
   `F₀ := f`, `F₁ := g`, `F_{k+1} := pseudoRem F_{k-1} F_k` while
   `F_k ≠ 0`. The chain terminates with some `F_N = 0`.

3. **Pseudo-division preserves common roots forward** (~30 lines).
   If `α` is a common root of `F_{k-1}` and `F_k`, then `α` is a
   root of `F_{k+1}`. Trivial: evaluate the pseudo-division
   identity at `α`; the LHS vanishes (as `F_{k-1}(α) = 0`), so
   `F_{k+1}(α) = -q(α) · F_k(α) = 0`.

4. **Pseudo-division preserves common roots backward** (~50 lines).
   If `α` is a root of `F_k` and `F_{k+1}` (and `lc(F_k) ≠ 0` as a
   constant in `R`, holding in the algebraic closure), then `α` is a
   root of `F_{k-1}`. From the pseudo-division identity:
   `lc(F_k)^d · F_{k-1}(α) = 0`, hence `F_{k-1}(α) = 0`.

5. **Termination behaviour: the chain computes a gcd** (~150 lines).
   The chain ends with `F_N = 0`; the previous nonzero `F_{N-1}` is
   `gcd(F₀, F₁) = gcd(f, g)` up to a unit (over the fraction field of
   `R`). By induction using lemmas 3 and 4, the common roots of `f`
   and `g` are precisely the roots of `F_{N-1}`.

6. **`Hex.subresultant` value's connection to the chain** (~50 lines).
   Our `Hex.DensePoly.subresultant f g` returns 0 iff
   `deg F_{N-1} ≥ 1` (the chain ends with a non-constant element,
   indicating a non-trivial gcd).

7. **Hex ↔ Mathlib bridge** (~50 lines).
   `Hex.DensePoly.subresultant f g = 0 ↔ Polynomial.subresultant
   (toPolynomial f) (toPolynomial g) = 0` via the `HexPolyMathlib.equiv`
   ring-equiv: structurally identical algorithms on isomorphic
   representations. (Note: the Mathlib-side `subresultant` we define
   in items 1–6 above can also be defined for the Mathlib-free
   `Hex.DensePoly` path; the structural identity is then immediate.)

8. **Final theorem** (~50 lines):

   ```lean
   theorem Hex.DensePoly.subresultant_zero_iff_common_root
       (f g : Hex.DensePoly R) [IsAlgClosed (algClosure R)] :
       Hex.DensePoly.resultant f g = 0
         ↔ ∃ α : algClosure R, (toPolynomial f).eval α = 0
                             ∧ (toPolynomial g).eval α = 0
   ```

   Combine items 5, 6, 7.

## Discriminant non-vanishing corollary

```lean
theorem Hex.DensePoly.disc_ne_zero_of_squarefree (f : ZPoly)
    (hf : Squarefree (toPolynomial f)) :
    Hex.DensePoly.disc f ≠ 0
```

Follows from item 8: `disc f = 0 ↔ resultant(f, f') = 0 ↔ f, f' share
a common root ↔ f has a multiple root ↔ ¬ Squarefree f`.

This is what HexRootsMathlib's `mahlerPrec` correctness (item 4 in
[hex-roots-mathlib.md](hex-roots-mathlib.md)) needs: the bound
`|disc p| ≥ 1` for squarefree integer `p` follows from `disc p ≠ 0`
plus `disc p ∈ ℤ`.

## Layered file organisation

```
HexResultantMathlib/
  Basic.lean         — public statements (Hex.subresultant_zero_iff_common_root,
                       disc_ne_zero_of_squarefree)
  Subresultant.lean  — items 1–6 (the core ~500-line chain analysis)
  Discriminant.lean  — discriminant non-vanishing corollary
  Conformance.lean   — fixture-based sanity checks of the bridge
```

`Subresultant.lean` is the substantive file. It can be designed for
upstream contribution to Mathlib (subresultant chain definition +
common-root property), independent of the rest of `hex`.

## Practical staging

`hex-resultant` (computational, just subresultant) lands first in
Phase 1. `hex-resultant-mathlib` lands in Phase 6 — substantial but
bounded at ~600 lines, more tractable than the full bridge would be.

## References

- See [hex-resultant.md](hex-resultant.md) for the subresultant
  references (Brown, Collins, Geddes-Czapor-Labahn, von zur Gathen
  and Gerhard).
- For the common-root property specifically: any standard text on
  computer algebra. The presentation here is closest to von zur
  Gathen and Gerhard, *Modern Computer Algebra* (3rd ed. 2013), §6.
