# Ordered-extension cases

Source: de Moura and Passmore,
[Computation in Real Closed Infinitesimal and Transcendental Extensions of the Rationals](https://www.cl.cam.ac.uk/~gp351/infinitesimals.pdf).

- `paper/reciprocal` reproduces §4's `1/ε > 10^27` comparison.
- `paper/comparison-rational` specializes the §4 comparison involving π to
  the rational coefficient 3. This tests the same polynomial arithmetic and
  infinitesimal ordering without supplying an analytic π provider.
- `level2` and `level3` instantiate successive infinitesimals as in §3.2.
  They include comparisons of a new infinitesimal with powers of its predecessor.
- The coefficient identity in `Conformance.lean` and the ordinary-kernel
  `InfinitesimalProofs.product_identity` factor the polynomial from Example 3:
  `(εx²−1)(εx³−1)=ε²x⁵−εx³−εx²+1`.

The oracle uses `z3-solver==4.15.4.0`, creating its ordered indeterminates with
`z3.z3rcf.MkInfinitesimal`. An independent exact `Fraction` specialization checks
each sign; Z3 also checks fraction identities. Other cases are synthetic
regressions. `real.jsonl` uses caller-supplied rational subjects; the separate
Mathlib tests prove containment at √2 and provide a Liouville integration fixture.
