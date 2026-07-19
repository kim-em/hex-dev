# hex-roots-mathlib (depends on hex-roots + hex-poly-z-mathlib + Mathlib)

Mathlib companion for [hex-roots](../../HexRoots/SPEC/hex-roots.md). Proves **soundness**
of the certified root isolation: every `DyadicRootIsolation` witness
implies a unique simple complex root in its certified region (the
stored square for the Newton-Kantorovich disjunct, the circumscribed
disc for the Pellet disjunct; the region is always contained in the
stored square's disc); every
`DyadicRootCluster` witness implies exactly `k` roots with
multiplicity; refinement preserves roots; `sameRoot` decides whether
two refined isolations isolate the same root; and `mahlerPrec` meets
its separation contract. **Completeness** (every Pellet witness
certifies by `separationDepth`, so `isolate` never returns `none` on
squarefree input) is a separately scoped development, described at
the end. The soundness theorems are stated conditionally on a `some`
result and do not depend on it.

**Scope warning.** This companion is the heaviest of the `-mathlib`
libraries. The two theorems everything rests on, **Pellet's
root-counting test** and the **Mahler separation bound**, do not
exist in Mathlib: no argument principle, Rouché, or residue theorem
is in mainline (checked against the 2026-06-18 revision), the only
open PRs in the area are two stalled new-contributor residue drafts
([#29588](https://github.com/leanprover-community/mathlib4/pull/29588),
[#39232](https://github.com/leanprover-community/mathlib4/pull/39232)),
and the winding-number infrastructure for general contours remains
future work (Patrick Massot, Zulip
[#maths > Multivariate complex analysis][zulip], 2025-12-28; Junyan
Xu's étale-space programme,
[#31925](https://github.com/leanprover-community/mathlib4/pull/31925),
aims there but has not landed).

None of that generality is needed here, and the restricted problem is
bounded. For **polynomials** on **circles**, the hard analytic
ingredients already exist in Mathlib: the circle integral of
`(z − w)⁻¹` inside the disc
(`circleIntegral.integral_sub_inv_of_mem_ball`), the vanishing of the
circle integral of a function holomorphic on a neighbourhood of the
closed disc (`DiffContOnCl.circleIntegral_eq_zero`), the derivative
of a product (`Polynomial.derivative_prod`), and continuity of
parametrised interval integrals
(`intervalIntegral.continuous_parametric_intervalIntegral_of_continuous`).
What remains for us is the polynomial partial-fraction identity,
finite summation, and a homotopy argument, as itemised below.

One deliberate restriction: everything is stated for `Polynomial ℂ`,
never `MeromorphicOn`. Mathlib's `MeromorphicOn` permits the function
value at an isolated point to differ from its analytic germ, and a
Rouché statement phrased over it admits counterexamples through that
decoupling. This is what made LeanEval's `rouche_zero_count_eq` false
as stated (Zulip, Model comparisons for Lean > LeanEval, 2026-05).
Polynomials have no such subtlety, and the polynomial statements
remain worth contributing to Mathlib on their own.

Both developments are organised as self-contained slices with no
`HexRoots` dependence, so each can be contributed to Mathlib as a
separate PR once it has been exercised here.

**Newton-Kantorovich route for atoms.** hex-roots atoms carry the
disjunction `atomWitness = nkWitness ∨ witness _ _ 1` (see
hex-roots.md §Newton-Kantorovich atom witnesses). The `nkWitness`
disjunct admits a soundness proof with no complex analysis at all:
Mehta and Macbeth have formalised the Newton-Kantorovich theorem
over Mathlib from `ContractingWith` (Banach fixed point) in a
self-contained ~250-line file (see References in hex-roots.md; not
in Mathlib mainline as of the revision above), and the
specialisation to polynomials on ℝ² with the sup norm makes the
witness's exact dyadic quantities literal bounds for the theorem's
hypotheses. Porting that file plus the specialisation layer is a
third candidate-contribution slice
(`HexRootsMathlib/Kantorovich.lean`,
`HexRootsMathlib/KantorovichPoly.lean`). If the dual-route
experiment in hex-roots settles on Newton-Kantorovich atoms, the
Rouché-on-circles development below is needed only for `k ≥ 2`
cluster soundness and the Pellet atom disjunct, and drops off the
critical path for `isolate` on squarefree inputs (whose soundness
then rests on `T_0` coverage, a triangle inequality, plus
Newton-Kantorovich and the Mahler separation bound).

[zulip]: https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Multivariate%20complex%20analysis

## What we cite from Mathlib (no work)

The following Mathlib API is used as-is (all names checked against the
Mathlib revision this repository pins):

- `Complex.isAlgClosed` (`Mathlib.Analysis.Complex.Polynomial.Basic`),
  `Polynomial.roots`, `Polynomial.Splits.natDegree_eq_card_roots`
  (`Mathlib.Algebra.Polynomial.Splits`): fundamental theorem of
  algebra; the root multiset of a complex polynomial.
- `Polynomial.rootMultiplicity` and the
  `Polynomial.derivative_rootMultiplicity_*` lemmas
  (`Mathlib.Algebra.Polynomial.FieldDivision`): simple roots are the
  `α` with `p.eval α = 0 ∧ p.derivative.eval α ≠ 0`.
- `Polynomial.Squarefree`,
  `PerfectField.separable_iff_squarefree` (`Mathlib.FieldTheory.Perfect`).
- `Polynomial.newtonMap`,
  `Polynomial.aeval_pow_two_pow_dvd_aeval_iterate_newtonMap`
  (`Mathlib.Dynamics.Newton`): the algebraic side of Newton's method.
- `ContractingWith` and the Banach fixed-point theorem
  (`Mathlib.Topology.MetricSpace.Contracting`): the analytic side of
  Newton convergence.
- `circleIntegral.integral_sub_inv_of_mem_ball`
  (`Mathlib.MeasureTheory.Integral.CircleIntegral`):
  `∮_{|z−c|=R} (z − w)⁻¹ dz = 2πi` for `w` inside the disc.
- `DiffContOnCl.circleIntegral_eq_zero`
  (`Mathlib.Analysis.Complex.CauchyIntegral`): the circle integral of
  a function holomorphic near the closed disc vanishes; applied to
  `(z − α)⁻¹` for roots `α` outside.
- `Polynomial.derivative_prod`
  (`Mathlib.Algebra.Polynomial.Derivative`): for the partial-fraction
  identity.
- `intervalIntegral.continuous_parametric_intervalIntegral_of_continuous`
  (`Mathlib.MeasureTheory.Integral.DominatedConvergence`): for the
  homotopy argument in Rouché.
- `Polynomial.cauchyBound` and `Polynomial.IsRoot.norm_lt_cauchyBound`
  (`Mathlib.Analysis.Polynomial.CauchyBound`): cited by the `cauchy`
  constructor's correctness theorem.
- `Polynomial.discr` and `Polynomial.resultant_deriv`
  (`Mathlib.RingTheory.Polynomial.Resultant.Basic`): the polynomial
  discriminant and `resultant(f, f') = ±lc · discr`.
- `Polynomial.resultant`, `Polynomial.resultant_eq_prod_roots_sub`
  (same file): the Sylvester-matrix toolkit.
- `Polynomial.mahlerMeasure` and its lemmas in
  `Mathlib.Analysis.Polynomial.MahlerMeasure`:
  `mahlerMeasure_mul`, `mahlerMeasure_eq_leadingCoeff_mul_prod_roots`,
  `mahlerMeasure_le_sqrt_natDegree_add_one_mul_supNorm` (Landau).
- `one_le_mahlerMeasure_of_ne_zero`
  (`Mathlib.NumberTheory.MahlerMeasure`) for nonzero integer
  polynomials.
- `Polynomial.supNorm` (`Mathlib.Analysis.Polynomial.Norm`).
- `Dyadic.invAtPrec_mul_le_one` and
  `Dyadic.one_lt_invAtPrec_add_inc_mul` (Lean standard library,
  `Init.Data.Dyadic.Inv`): the rounding-error bounds for the Newton
  step's reciprocal.

## Discriminant / separation development

The smaller of the two new developments, and the one needed first:
`mahlerPrec`'s contract rests on the Mahler separation bound.

### Theorem chain

1. **Discriminant nonvanishing.** A positive-degree separable polynomial
   has nonzero discriminant, and an integer polynomial whose rational cast is
   separable satisfies `1 ≤ |discr f|`. The rational-cast condition is the
   roots-facing squarefreeness notion; squarefreeness in `ℤ[x]` would also
   constrain the content. Lives in `HexPolyZMathlib/Discriminant.lean`.

2. **Discriminant root-product formula:**
   `discr f = lc(f)^{2n−2} · ∏_{i<j}(αᵢ − αⱼ)²` over the splitting
   field. Mathlib has the resultant version
   (`resultant_eq_prod_roots_sub`); we derive the discriminant version
   through `resultant_deriv`. Lives in
   `HexPolyZMathlib/Discriminant.lean`.

3. **Mahler separation bound:**
   ```
   ∀ i ≠ j, |αᵢ − αⱼ| ≥ √3 · n^{−(n+2)/2} · |disc p|^{1/2} · M(p)^{−(n−1)}
   ```
   for squarefree `p ∈ ℤ[x]` of degree `n ≥ 2`. The proof bounds the
   Vandermonde determinant of the roots two ways: its square is
   `disc p / lc(p)^{2n−2}` by item 2, and Hadamard's inequality bounds
   it above column-by-column, with one column rescaled to expose the
   factor `|αᵢ − αⱼ|`. Mahler's original argument is exactly this;
   Mignotte and Ştefănescu, ch. 4, give a self-contained version
   suitable for direct formalisation. (A naive bound on the individual
   factors `|αᵢ − αⱼ| ≤ 2·M(p)` does *not* reach the stated constant;
   Hadamard is essential.) The Hex-independent column estimates and
   discriminant/Vandermonde identity live in
   `HexPolyZMathlib/MahlerSeparation.lean`; companion-specific executable
   exponent arithmetic stays with the relevant roots library.

4. **`mahlerPrec` correctness:** the computational
   `Hex.mahlerPrec p : Nat` (defined in `HexRoots/MahlerPrec.lean`)
   satisfies the companion theorem
   ```
   mahlerPrec_separates
       (hsep : ((toPolynomial p).map (Int.castRingHom ℚ)).Separable)
       (hr₁ : (toPolyℂ p).IsRoot z₁)
       (hr₂ : (toPolyℂ p).IsRoot z₂)
       (hne : z₁ ≠ z₂) :
     2^{−mahlerPrec p} · 1449/1024 < ‖z₁ - z₂‖ / 4
   ```
   Thus it gives the advertised `sep(p) / 4` bound uniformly over distinct
   roots. The rational separability hypothesis is the squarefreeness notion
   used here; integral-polynomial `Squarefree` would incorrectly reject
   nonprimitive polynomials with simple rational roots. The left side bounds the
   circumscribed-disc radius at that precision from above. Combines
   item 3 with Landau's
   `mahlerMeasure_le_sqrt_natDegree_add_one_mul_supNorm` to remove
   `M(p)` in favour of the integer `‖p‖∞`. Lives in
   `HexRootsMathlib/MahlerPrec.lean`.

## Rouché-on-circles development

The harder of the two developments. It supplies the semantics of the
Pellet witnesses.

### Theorem chain

5. **Partial fractions for `p'/p`**: for `0 ≠ p : ℂ[X]` and `z` off
   the roots,
   ```
   p'(z) / p(z) = Σ_{α ∈ p.roots} (z − α)⁻¹
   ```
   summing over the root multiset (so an m-fold root contributes m
   terms). From the factorisation of `p` over ℂ and
   `Polynomial.derivative_prod`, plus circle-integrability of each
   summand. Lives in `HexRootsMathlib/CircleIntegralLemmas.lean`.

6. **Argument principle for polynomials on circles:**
   ```
   (1/2πi) · ∮_{|z−c|=r} (p'(z) / p(z)) dz = (Polynomial.roots p).countP (· ∈ ball c r)
   ```
   for `p ≠ 0` with no zeros on `|z−c| = r`; the count is with
   multiplicity, since `Polynomial.roots` is a multiset. By item 5
   and linearity of the circle integral over the finite sum: each
   root inside contributes `2πi`
   (`circleIntegral.integral_sub_inv_of_mem_ball`), each root outside
   contributes `0` (`DiffContOnCl.circleIntegral_eq_zero`, as
   `(z − α)⁻¹` is then holomorphic near the closed disc). No winding
   numbers and no meromorphic API. Lives in
   `HexRootsMathlib/ArgumentPrinciple.lean`.

7. **Rouché for polynomials on circles**, classical form (`|f − g| <
   |g|` on the circle implies `f` and `g` have the same number of
   zeros inside) and symmetric form (`|f − g| < |f| + |g|` likewise).
   Proof by homotopy: `h_t := g + t·(f − g)` has no zero on the
   circle for `t ∈ [0, 1]`, its root count is given by item 6, the
   count varies continuously in `t`
   (`continuous_parametric_intervalIntegral_of_continuous`), and an
   integer-valued continuous function on `[0, 1]` is constant. Lives
   in `HexRootsMathlib/Rouche.lean`.

8. **Pellet (BSSY Theorem 1):**
   ```
   |c_k|·r^k > Σ_{i ≠ k} |c_i|·r^i   ⇒   p has exactly k roots in D(0, r)
   ```
   where `cᵢ = p.coeff i` and the count is with multiplicity. Proved
   by applying Rouché to `p` and the monomial `c_k · z^k`. Lives in
   `HexRootsMathlib/Pellet.lean`.

The computational library never states this inequality directly: its
witness compares dyadic bounds (`lo`, `hi`, and the rational `√2`
bounds; see [hex-roots.md](../../HexRoots/SPEC/hex-roots.md)). The one-directional lemma
"the dyadic-bound witness implies the exact Pellet inequality" lives
in `HexRootsMathlib/Geometry.lean`, so the analytic development above
stays in the standard form (the form worth contributing to Mathlib)
while the computational library stays decidable. The converse
direction, that a sufficiently isolating disc makes the witness hold
despite the factor-2 slack, belongs to the completeness development
below.

## Correspondence theorems

These files connect the `HexRoots` data structures to the two
developments above.

- `HexRootsMathlib/Basic.lean`: exact `Dyadic → ℝ` and
  `GaussDyadic → ℂ` casts and their algebra/order correspondence.
- `HexRootsMathlib/Geometry.lean`: `lo(c) ≤ |c| ≤ hi(c)`, the
  `181/128 < √2 < 1449/1024` bounds, and the Mathlib geometry of a
  `DyadicSquare`: its complex centre, real half-width, closed sup-norm
  square, and open/closed circumscribed discs. Simp lemmas
  `DyadicSquare.center_eq`, `DyadicSquare.disc_eq`. The later Pellet
  correspondence in this module proves "witness implies Pellet".
- `HexRootsMathlib/Taylor.lean`: the shared exact-coefficient bridge
  ```lean
  theorem taylor_coeff (p : ZPoly) (z : GaussDyadic) (k : Nat) :
      toComplex ((taylor p z).getD k (0, 0)) =
        ((toPolyℂ p).comp (X + C (toComplex z))).coeff k
  ```
  including the out-of-bounds case. Its proof consumes the executable
  `taylor_getD` characterization rather than unfolding the in-place folds.
- `HexRootsMathlib/HasOnlySimpleRoots.lean`:
  for `p ≠ 0`, `Hex.HasOnlySimpleRoots p` is equivalent to separability of
  `(toPolynomial p).map (Int.castRingHom ℚ)`. Connects
  the executable test (the `ℚ[x]` gcd of `p` and `p'` is constant)
  with Mathlib's rational-polynomial separability API. This is deliberately
  not integral-polynomial `Squarefree`, which is sensitive to nonunit content.
- `HexRootsMathlib/MahlerPrec.lean`: item 4 above.
- `HexRootsMathlib/SimpleRoot.lean`: the semantics of root identity.
  ```lean
  /-- The unique root inside a refined isolation's certified region
      (the stored square for the Newton-Kantorovich disjunct, the
      circumscribed disc for the Pellet disjunct). The quotient
      argument below needs only that each root lies in its own
      isolation's disc, which both disjuncts give. -/
  def RefinedIsolation.root (i : RefinedIsolation p) : ℂ

  theorem intersects_iff_root_eq
      (hsep : (HexPolyZMathlib.toPolyℚ p).Separable)
      (i₁ i₂ : RefinedIsolation p) :
      Intersects i₁ i₂ ↔ i₁.root = i₂.root
  ```
  A local atom witness makes its selected root simple but does not imply
  global separability, so the separation premise is necessary. Successful
  nonzero `isolate` input obtains it from `HasOnlySimpleRoots`; the companion
  also exposes `intersects_iff_root_eq_of_simple` with those hypotheses.
  Under the same premise, `Intersects` restricted to `RefinedIsolation p` is
  an equivalence relation; `Hex.rootOf` is well-defined by `Quot.lift`; and
  `sameRoot i₁ i₂ = true ↔ SimpleRoot.mk i₁ = SimpleRoot.mk i₂`, so the
  Boolean test used by the Mathlib-free layer decides equality in the
  quotient. The `< sep/4` radius bound from item 4 makes the conditional
  `intersects_iff_root_eq` theorem true.
- `HexRootsMathlib/Cauchy.lean`: `Component.cauchy`
  correctness. The starting closed square contains all of `Polynomial.roots p`
  by `Polynomial.IsRoot.norm_lt_cauchyBound`: the executable maximum bounds
  every non-leading coefficient, its ceiling division bounds Mathlib's
  Cauchy bound, and `ceilLog2` rounds that integer bound up to the square's
  power-of-two half-width. The degree-`n`
  witness holds at the base, doubled, and quadrupled radii because the
  leading-term inequality `|aₙ|·Rⁿ > Σ_{i<n}|aᵢ|·Rⁱ` only improves as
  `R` grows past the Cauchy bound.
- `HexRootsMathlib/Newton.lean`: `newton1?` and `refineTo?`
  soundness. When they return `some iso'`, `iso'` isolates the same
  root and `iso'.square.prec > iso.square.prec`
  (`sameRoot`-preservation is the statement the threading pattern in
  hex-roots.md relies on). Uses `Polynomial.newtonMap`,
  `aeval_pow_two_pow_dvd_aeval_iterate_newtonMap`, and the
  `Dyadic.invAtPrec` error bounds.
- `HexRootsMathlib/RootFree.lean`: elementary `T₀` soundness. The exact
  accumulator inequality and the Taylor coefficient bridge imply, by the
  finite triangle inequality, that a successful `rootFree` test excludes
  roots from the open disc of radius `radiusHi`. This contains both the
  represented closed square and its true closed circumscribed disc because
  `√2 < 1449/1024`.
- `HexRootsMathlib/Bisection.lean`: elementary subdivision coverage. The four
  closed children cover the parent, and every child containing a root survives
  the `rootFree` filter. They are not pairwise disjoint, since adjacent
  children share boundary segments. Completing `Component.refine1`
  preservation additionally requires
  a characterization that `glue` preserves membership (equivalently, that
  flattening its output permutes its input). Once that bridge is available, a
  `T_0`-discarded child's disc
  contains no root, so every root covered by the parent lies in some
  retained child; when `certify?` returns a cluster, its disc
  contains exactly `k` roots with multiplicity (Pellet, item 8); when
  it returns an atom, the certified region contains exactly one
  simple root (Newton-Kantorovich or Pellet at `k = 1`); and the
  coverage guard makes an accepted speculative-Newton region contain
  exactly the roots of the base region.
- `HexRootsMathlib/Driver.lean` and `HexRootsMathlib/Isolate.lean`: driver
  soundness. Retained squares cover every root, output discs are pairwise
  disjoint, and each certificate has its asserted multiplicity count. Thus
  the general driver's certificate counts sum to the polynomial degree; when
  `isolate` successfully extracts only atoms, their distinct semantic roots
  enumerate the root finset exactly.
  ```lean
  theorem isolateAll_count (p : ZPoly)
      (h : 0 < p.degree?.getD 0) {target strategy result}
      (hr : isolateAll? p target #[Component.cauchy p h] strategy = some result) :
      ∑ i : Fin result.size, Certified.count result[i] = (toPolyℂ p).natDegree

  theorem isolate_sound (p : ZPoly) (h : Hex.HasOnlySimpleRoots p)
      (atom_prec : Int) (strategy : AtomStrategy) {atoms}
      (ha : isolate p h atom_prec strategy = some atoms) :
      (atoms.toList.map (·.root)).toFinset = (toPolyℂ p).roots.toFinset ∧
      ∀ a ∈ atoms, atom_prec ≤ a.square.prec
  ```
  (`HasOnlySimpleRoots p` does *not* rule out `p = 0` (the
  executable gcd of `0` and `0` is `0`, of size `0 ≤ 1`), but
  `isolate 0 _ _ = none` by definition, so the `ha` hypothesis
  supplies nonzeroness; a nonzero constant returns `some #[]` and
  both sides are empty. The rational-separability correspondence in
  `HasOnlySimpleRoots.lean` carries a `p ≠ 0` hypothesis for the same reason.)
- `HexRootsMathlib/Refinement.lean`: a successful
  `DyadicRootIsolation.refineTo?` call preserves the raw atom's semantic root.
  The refined-level wrapper preserves `RefinedIsolation.root` unconditionally
  by exposing the successful underlying raw refinement call; the packaged
  quotient equality remains available to Mathlib-free callers.

## Completeness development (separately scoped)

Soundness above never claims the drivers succeed. Completeness does,
and it is the analytically hardest part:

9. **Pellet converse with margin**: if the disc is
   `(ρ₁, ρ₂)`-isolating with a wide enough ratio, then the
   dyadic-bound witness holds. Without Graeffe iteration the required
   ratio is *linear in `deg p`* (each remote root contributes to the
   higher Taylor coefficients; the relevant bound is
   `(1 + ρ/d)^{n−1} − 1`), times a fixed factor absorbing the
   factor-2 witness slack. This is what `separationDepth`'s
   `ceilLog2 (deg p)` term supplies.
10. **Newton success**: on a sufficiently refined atom the speculative
    Newton step recertifies (via `ContractingWith` on the Newton map).
11. **Certification by separation depth**: for squarefree `p`, at
    depth `≥ separationDepth p` every rootless component has vanished
    (all its squares `T_0`-certify), every surviving component passes
    `certify?` with `k = 1` (items 9 and 10 supply the two
    certification paths), and the certified discs are pairwise
    disjoint (radius below `sep/4`). Hence
    `isolate p h atom_prec ≠ none`. This is the theorem that retires
    the drivers' `none` branch; it never mentions the recursion
    structure, only depths and witnesses.

Items 9-11 can be deferred: every theorem in this library is usable
without them, and the conformance suite checks empirically that `none`
does not occur on the committed fixtures. They are listed here so the
scope is honest; nothing else in the plan silently depends on them.

## File organisation

```
Shared discriminant / separation development (candidate Mathlib contribution):
  HexPolyZMathlib/Squarefree.lean
  HexPolyZMathlib/Discriminant.lean
  HexPolyZMathlib/Hadamard.lean
  HexPolyZMathlib/MahlerSeparation.lean

Executable complex-root specialization:
  HexRootsMathlib/MahlerPrec.lean

Rouché-on-circles development (candidate Mathlib contribution;
the hardest slice):
  HexRootsMathlib/CircleIntegralLemmas.lean
  HexRootsMathlib/ArgumentPrinciple.lean
  HexRootsMathlib/Rouche.lean
  HexRootsMathlib/Pellet.lean

Newton-Kantorovich development (candidate Mathlib contribution;
port of Mehta-Macbeth, see the intro):
  HexRootsMathlib/Kantorovich.lean
  HexRootsMathlib/KantorovichPoly.lean

Correspondence theorems (depend on hex-roots data structures):
  HexRootsMathlib/Basic.lean
  HexRootsMathlib/Geometry.lean
  HexRootsMathlib/Taylor.lean
  HexRootsMathlib/HasOnlySimpleRoots.lean
  HexRootsMathlib/MahlerPrec.lean
  HexRootsMathlib/SimpleRoot.lean
  HexRootsMathlib/Cauchy.lean
  HexRootsMathlib/Newton.lean
  HexRootsMathlib/Bisection.lean
  HexRootsMathlib/IsolateAll.lean

Completeness development (deferrable; see above):
  HexRootsMathlib/Completeness/…
```

The candidate contributions have no `HexRoots` dependence and can
be split out or sent to Mathlib if they grow. The library is verified
by building it. Conformance fixtures live with `hex-roots`.

`Kantorovich.lean` is the attributed Mathlib-only Mehta--Macbeth core: it
derives a quantitative contraction theorem from `ContractingWith`, proves the
general Newton--Kantorovich result, and obtains the finite-dimensional form by
showing the approximate inverse is surjective and hence injective in equal
dimensions. Polynomial and executable-witness specialization belongs in
`KantorovichPoly.lean`, not in the generic module.

## References

See [hex-roots.md](../../HexRoots/SPEC/hex-roots.md) for the BSSY, Pellet, Mahler, and
Mignotte references. In addition:

- Becker, Sagraloff, Sharma, Yap, JSC 2018, §2: the exact form of the
  Pellet inequality and its derivation from Rouché.
- Mignotte, Ştefănescu. *Polynomials: An Algorithmic Approach.*
  Springer, 1999. Chapter 4 has a self-contained proof of the Mahler
  separation bound (via Hadamard's inequality) suitable for direct
  formalisation.
- Yap. *Fundamental Problems of Algorithmic Algebra.* Oxford, 2000.
  §6.6 derives the same bound via Liouville-style estimates, an
  alternative if the Hadamard route stalls.
