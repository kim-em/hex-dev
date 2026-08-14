# hex-mv-gcd: the univariate view decision

## Accomplished

Amended `SPEC/Libraries/hex-mv-gcd.md` to recurse on hex-mv-poly's existing
arity-dropping `toUnivariate` / `ofUnivariate` rather than on a new
arity-preserving view.

The SPEC previously specified a `Without i R cmp` subtype with `coeffsIn`,
`ofCoeffsIn`, `leadingCoeffIn`, and `degreeIn?`, on the argument that a
fixed ambient type avoids `Fin.succAbove` reindexing and per-arity
comparator choices. Reading `HexMvPoly/Recursive.lean` changed the balance:
it is 436 lines with three fold lemmas and four round-trip theorems, all
proved, and the arity-preserving pair would mirror all of it. The
reindexing is bookkeeping inside proofs being written anyway.

Two things the arity drop turns out to buy, which the earlier text missed:

- The whole univariate surface comes from hex-poly on the result.
  `DensePoly.degree?` is the degree in the main variable and already
  distinguishes the zero polynomial from a constant, which is what the
  certificate's degree checks need and what `degreeIn?` was invented for.
  `DensePoly.leadingCoeff` and `DensePoly.coeff k` cover the rest.
- `CoprimeCert` becomes structurally recursive in the arity. The
  active-variable list, the `i ∈ active` check, and the `active.erase i`
  bookkeeping all disappear, because each `split` constructor lands one
  arity down and progress is a property of the result type.

One operation is added that hex-mv-poly does not supply and that belongs
here: `constIn i cmp'`, embedding a polynomial in the remaining variables
back as one constant in the main variable. Content and primitive part are
stated through it, since with the arity drop `contentIn` no longer has the
same type as its input.

Sections rewritten: "The recursive view", "What hex-mv-poly supplies"
(replacing "Additions needed in hex-mv-poly"), content and primitive part,
the modular witness, the certificate type and checker, `LawfulContent`,
route 3's leading-coefficient correction, route 5's coefficient ring, the
complexity table, the kernel closure, the companion's content
correspondence, milestone 1, and the file layout.

## Current frontier

The SPEC now matches what is in the tree. `HexMvPoly` needs nothing
further: the `Lean.Grind.CommRing` tower and `mapCoeffs` landed in #9247,
and those were the only two additions it owed.

## Next step

Milestone 1 of hex-mv-gcd, all of which lives in the new library: `GcdOps`
/ `BezoutOps` / `LawfulGcdOps`, `CoeffHom`, `divMod` and `divExact?`, the
`Dvd` / `Div` / `ExactDivLaws` instances, `constIn`, `monoContent`,
`contentIn`, `primPartIn`, and Gauss's lemma. `HexMvGcd` is still not in
`libraries.yml`; adding it is the first step.

## Blockers

None.
