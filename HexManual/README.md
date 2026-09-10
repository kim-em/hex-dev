# HexManual

The Verso reference manual for the `hex` project. Each per-library
reference chapter lives in `Chapters/`. `HexManual.lean` serves as the table of contents

`lake build HexManual` *typechecks* the manual: it checks every
`{docstring}`, `{ref}`, `#eval`/`leanOutput`, and `#guard` in the
chapters as they elaborate. It does not produce a website.

To view the manual, render it to static HTML with the `hexmanual`
executable:

    lake exe hexmanual --output _out
    python3 -m http.server -d _out/html-multi   # then open localhost:8000

CI publishes the rendered manual to GitHub Pages on every push to `main`
(`.github/workflows/pages.yml`). See [PLAN/Releases.md](../PLAN/Releases.md)
for the full render-and-publish process.

## Direct radical design requirements

The [direct radical SPEC](../HexNumberField/SPEC/hex-number-field.md#direct-certified-radicals-and-cyclotomic-embeddings) specifies
future behavior behind the existing principal `sqrt`/`nthRoot` API. Until it
is implemented, the number-field chapter continues to describe the shipped
solver. Its implementation PR must update that chapter with checked examples
and explanations covering:

- Index zero, index one, zero input, square roots, and negative real odd roots;
  inputs above, below, and on the cut, with the conditional conjugation law.
- Direct `p(X^n)` construction, one selected irreducible factor and embedding,
  and the distinction between principal approximation, certification and
  canonical construction. A small residual does not select the branch.
- Rational/perfect-power and composite-index routes, including reducible
  annihilators, with honest end-to-end costs in degree and coefficient height.
- Rational turns, checked cyclotomic indices, exact order recognition and its
  bounded negative search, principal-turn division, `I.nthRoot 4`, and reuse
  of the same minimal polynomial for coprime powers. Distinguish `unknown`
  from a proved non-root-of-unity result in budgeted interfaces.
- The new canonical normal form, structural equality across constructors,
  conjugation and Repr round trips, migration of old isolation expressions,
  and possible changes to enumeration indices and nearest-root ties.

Do not present proposed identifiers as available APIs. Link performance claims
to phase-separated measurements including input construction and peak memory;
use the [quadratic construction report](../reports/hex-number-field-quadratic.md)
as the fixed baseline for the high-height regression in #10156, including
the remaining trial-factorization allocation costs. The real-algebraic chapter must
retain the nonnegative real square-root contract. Build the affected chapters
with `lake build HexManual` and render the manual when those chapters change.
