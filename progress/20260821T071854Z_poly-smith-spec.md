# Polynomial Smith normal form SPEC (issue #9318)

## Accomplished

- Wrote `SPEC/Libraries/hex-poly-smith.md` for executable Smith normal form
  over `Matrix (DensePoly F) n m` with `F` a field, plus its Mathlib
  companion. Covers the monic contract, the monic-normalising 2x2 elimination
  step with its explicit inverse, the degree termination measure, the diagonal
  fast path, determinantal divisors and uniqueness, certificates, prerequisite
  relocations, complexity, degenerate dimensions, conformance, and benchmarks.
- Drew the comparison against `hex-smith` and `hex-hermite` as an explicit
  transfers/does-not-transfer table rather than prose, and closed the
  Euclidean-domain-class question that `hex-hermite` left open.
- Kept characteristic matrices, invariant factors of `xI - A`, matrix minimal
  polynomials, and rational canonical form out, with a note that the
  application library must not be named `hex-rcf`.
- Updated `SPEC/Libraries/README.md` (library list, Mathlib companion list,
  both dependency lists, the DAG section, the index) and graduated the
  polynomial-Smith item in `SPEC/future-work.md`. Added cross-links from
  `hex-smith.md` and `hex-hermite.md`.
- Corrected `hex-char-poly.md`, whose Cayley-Hamilton prerequisite list says
  the `Lean.Grind.CommRing (Hex.DensePoly R)` instance "does not exist". It
  does: `instGrindCommRingDensePoly` in `HexResultant/ExactDiv.lean`. The
  real problem is that it is not reachable from `hex-poly`, so the fix is a
  relocation and not a new instance. Left a note there against writing a
  second copy.

## Verification performed

Built `HexDeterminant` and `HexResultant` in this worktree (`.lake/packages`
symlinked from the main checkout) and elaborated every Lean block in the new
SPEC with `lake env lean` against `HexPoly`, `HexMatrix`, `HexDeterminant`:

- `SmithData`, `IsSNF`, `diagMatrix`, `elimStep`, the whole API, every
  correctness theorem, `snfCert`, `mulEqCertAt`, `detDivisor_spec`: all
  elaborate, only `sorry` warnings.
- Dropping the `HexResultant` import produces exactly four failures, all
  instance-synthesis failures at `Matrix.det`. That is the evidence behind the
  "move `Lean.Grind.CommRing (DensePoly R)` down to `hex-poly`" prerequisite.
- Confirmed as unknown constants / missing instances: `Hex.DensePoly.monicize`,
  `Hex.Matrix.diagonal`, `Hex.Matrix.diagMatrix`, and
  `DensePoly.DivModLaws F` / `GcdLaws F` for a generic `Lean.Grind.Field F`.
- Checked the `E` / `E⁻¹` formulas numerically over `Rat` on ten inputs
  (generic, coprime, non-monic leading coefficients, `a = 0`, `b = 0`, both
  zero, `a = b`, either side a unit, each side dividing the other): all four
  properties hold in every case.
- Confirmed the non-monic-gcd claims by evaluation:
  `gcd (2x²+2x) (3x+3) = 3x+3`, `gcd (x²-1) (x²+x) = -x-1`, and
  `gcd (x²+x) (x²-1) = x+1`.
- Confirmed `HexDeterminant/CauchyBinet.lean` is stated over
  `[Lean.Grind.CommRing R]`, so the missing selected-minor Cauchy-Binet work
  serves both Smith libraries.
- `git diff --check` passes; every relative link in the touched files resolves.

## Second opinion, and what it changed

Codex reviewed the SPEC and found two real correctness problems plus a
number of overstatements. All were fixed:

- **The termination measure was false.** Step 3 originally applied the `E`
  matrix at every entry. When the pivot already divides the entry, `xgcd`
  can return `s = 0` (verified: `xgcd x (2x) = ⟨2x, 0, 1⟩`), and then `E`
  replaces the pivot row by a multiple of the other row, leaving the pivot
  degree fixed while raising the off-pivot nonzero count. The measure goes
  up. The loop now branches: plain subtraction when the pivot divides,
  `E` only when it does not.
- **`isSNFShape` did not check the rank bounds**, so `snfCert_sound` was
  unprovable: `n = m = 0`, `rank = 1`, `diag = #v[1]` passes every product
  identity. The shape test is now exactly the reflection of the four
  `IsSNF` fields the products do not establish, and it elaborates.
- Rewrote `E` so all four divisions are by the monic `ĝ` rather than by
  the raw `g` (they are equal, since `a/g = u·(a/ĝ)`), which makes the
  earlier claim that every division in the loop is monic actually true.
  Re-verified numerically on thirteen inputs, and verified the diagonal
  sweep's `V`, `V⁻¹`, `L₁`, `L₂` and product identity on five.
- Split the API into form-only (`snf`, `snfRank`, `snfDiagonal`) and
  full-data (`snfData`, `snfDiagonalData`) paths, matching `hex-hermite`
  and the revised `hex-smith`. The old single entry point was justified by
  a false claim that every headline consumer needs the transforms; only
  `solve` does.
- Corrected: the `Lean.Grind.CommRing (DensePoly R)` relocation is a
  couple of hundred lines (the whole `NatCast`/`OfNat`/`NSMul`/`NPow`/
  `IntCast`/`ZSMul`/`Semiring`/`Ring` tower), not two lines, and the four
  measured failures are `Lean.Grind.Ring`, not `CommRing`, because
  `Matrix.det` takes `Ring`. `DivModLaws` has nine fields, not three.
  `BhksCandidates.lean` scales by `leadingCoeff f`, not its inverse, so it
  is not a `monicize` call site. The evaluation checker is not
  unconditionally a factor of `D` cheaper. `solve`'s `vecMul`s cost
  `O(n² + m²)`. The diagonal sweep needs paired row and column swaps and a
  fixed bubble network (justified by the 0/1 principle for distributive
  lattices) rather than "until nothing changes". PARI's polynomial
  `matsnf` is square-only, so sympy is the primary oracle. `Matrix.rank`
  does apply over `Polynomial F`; the reason to pass to `RatFunc` is that
  it computes a different thing there.

## Current frontier

The SPEC is complete and no library source was written, per the issue.

## Next step

Two independent pieces can be scheduled now, both outside this library:

- the four prerequisite relocations (`monicize` and the generic law-package
  instance into `hex-poly`, the commutative-ring instance down from
  `hex-resultant`, `diagMatrix` into `hex-matrix`);
- the selected-minor Cauchy-Binet phase in `hex-determinant`, which
  `hex-smith` also names and which blocks the uniqueness theorem in both.

The executable parts and the certificate can proceed in parallel with the
second.

## Blockers

None. The oracle choice for conformance (sympy at a polynomial domain, or
PARI `matsnf`) is recorded as needing confirmation against the versions CI
installs before the driver is written.
