# hex-roots-mathlib (depends on hex-roots + hex-poly-z-mathlib + Mathlib)

Proves correctness of the certified complex root isolation in
[hex-roots](hex-roots.md): every `DyadicRootIsolation` certifies a
unique simple complex root in its disc; every `DyadicRootCluster`
certifies exactly `k` roots; refinement preserves roots; `isolate`
under `Hex.HasOnlySimpleRoots` returns the full set of roots; and the
`mahlerPrec` separation bound is correct.

**Scope warning.** This bridge library is significantly heavier than
typical `-mathlib` companions. The two foundational theorems we need —
**Pellet's inclusion test** and the **Mahler separation bound** —
neither exist in Mathlib at the time of writing. The first is genuinely
hard to land because Mathlib lacks general-contour winding-number
infrastructure (Patrick Massot, Zulip
[#maths > Multivariate complex analysis][zulip],
2025-12-28); we sidestep that by restricting to *circular* contours,
which is all our algorithm needs. The second is well-supported by
Mathlib's existing Mahler measure / discriminant / resultant API but
the standalone separation theorem hasn't been assembled yet.

The library is organised so that both developments are
**self-contained slices upstreamable to Mathlib** as separate PRs once
they've been battle-tested here.

[zulip]: https://leanprover.zulipchat.com/#narrow/stream/116395-maths/topic/Multivariate%20complex%20analysis

## What we cite from Mathlib (no work)

The following Mathlib API is used throughout. Library work is glue, not
re-derivation:

- `Complex.isAlgClosed` (`Mathlib.Analysis.Complex.Polynomial.Basic`),
  `Polynomial.roots`, `Polynomial.Splits.natDegree_eq_card_roots` —
  fundamental theorem of algebra; root multiset for `ℂ[X]`.
- `Polynomial.rootMultiplicity` and the
  `Polynomial.derivative_rootMultiplicity_*` family — characterisation
  of simple roots via `p.eval α = 0 ∧ p.derivative.eval α ≠ 0`.
- `Polynomial.Squarefree`,
  `PerfectField.separable_iff_squarefree` (in `Mathlib.FieldTheory.Perfect`).
- `Polynomial.newtonMap`,
  `Polynomial.aeval_pow_two_pow_dvd_aeval_iterate_newtonMap`
  (`Mathlib.Dynamics.Newton`) — algebraic side of Newton's method.
- `ContractingWith` and the Banach fixed-point theorem
  (`Mathlib.Topology.MetricSpace.Contracting`) — analytic side of
  Newton convergence.
- `Mathlib.Analysis.Complex.CauchyIntegral` — Cauchy integral formula
  on circles, the substrate for our argument-principle development.
- `Polynomial.cauchyBound` and `IsRoot.norm_lt_cauchyBound`
  (`Mathlib.Analysis.Polynomial.CauchyBound`) — cited by the
  `cauchy` constructor's correctness theorem.
- `Polynomial.discr` and `Polynomial.resultant_deriv`
  (`Mathlib.RingTheory.Polynomial.Resultant.Basic`) — discriminant
  and the `resultant(f, f') = ±lc · discr` relation.
- `Polynomial.resultant`, `Polynomial.resultant_eq_prod_roots_sub`
  (same file) — the full Sylvester-matrix toolkit.
- `Polynomial.mahlerMeasure` and the suite in
  `Mathlib.Analysis.Polynomial.MahlerMeasure`:
  `mahlerMeasure_mul`, `mahlerMeasure_eq_leadingCoeff_mul_prod_roots`,
  `mahlerMeasure_le_sqrt_natDegree_add_one_mul_supNorm` (Landau).
- `one_le_mahlerMeasure_of_ne_zero` (`Mathlib.NumberTheory.MahlerMeasure`)
  for nonzero integer polynomials.
- `Polynomial.supNorm` (`Mathlib.Analysis.Polynomial.Norm`).

## Discriminant / separation development

This is the smaller of the two new analytic developments, and the
one needed *first* — `isolate`'s termination story leans on
`mahlerPrec`'s correctness, which leans on the Mahler separation
bound.

### Theorem chain

1. **`Polynomial.discr ≠ 0 ↔ Squarefree`** for `ℤ[x]` (and char-zero
   more generally). Bridge via the existing chain
   `separable_iff_squarefree` ↔ `IsCoprime f f'` ↔ `resultant ≠ 0` ↔
   `discr ≠ 0`. Mostly assembly from existing Mathlib pieces. Lives in
   `HexRootsMathlib/DiscriminantSquarefree.lean`.

2. **Discriminant root-product formula:**
   `discr f = lc(f)^{2n−2} · ∏_{i<j}(αᵢ − αⱼ)²` over the splitting
   field. Mathlib has the resultant version
   (`resultant_eq_prod_roots_sub`); we derive the discriminant version
   on top using `resultant_deriv`. Lives in
   `HexRootsMathlib/DiscriminantRootProduct.lean`.

3. **Mahler/Mignotte separation bound:**
   ```
   ∀ i ≠ j, |αᵢ − αⱼ| ≥ √3 · n^{−(n+2)/2} · |disc p|^{1/2} · M(p)^{−(n−1)}
   ```
   for squarefree `p ∈ ℤ[x]`. Standard textbook proof: take logs of the
   root-product formula (item 2), bound each `|αᵢ − αⱼ| ≤ 2 · M(p)` for
   pairs not equal to `(i, j)`, use `|disc p| ≥ 1`. Lives in
   `HexRootsMathlib/MahlerSeparation.lean`.

4. **`mahlerPrec` correctness:** the computational
   `Hex.mahlerPrec p : Nat` (defined in `HexRoots/MahlerPrec.lean`)
   satisfies
   ```
   2^{-mahlerPrec p} ≤ (min_{i ≠ j} |αᵢ − αⱼ|) / 2
   ```
   for squarefree `p`. Combines item 3 with Landau's
   `mahlerMeasure_le_sqrt_natDegree_add_one_mul_supNorm` to eliminate
   `M(p)` in favour of the integer `‖p‖∞`, then takes `−log₂` of the
   resulting bound. Lives in `HexRootsMathlib/MahlerPrec.lean`.

## Analytic core (Rouché-on-circles)

The harder of the two developments. Used to prove the semantics of
`DyadicRootIsolation` and `DyadicRootCluster`.

### Theorem chain

5. **Circle-integral lemmas** — logarithmic-derivative identities,
   no-roots-on-boundary preservation, `(z − α)⁻¹` residue
   computations on circles. The load-bearing intermediate layer; the
   argument-principle proof becomes intractable without first
   factoring this out. Lives in
   `HexRootsMathlib/CircleIntegralLemmas.lean`.

6. **Argument principle on circles:**
   ```
   (1/2πi) · ∮_{|z−c|=r} (p'(z) / p(z)) dz = (Polynomial.roots p).countP (· ∈ ball c r)
   ```
   for `p` analytic with no zeros on `|z−c| = r`. Built from Mathlib's
   `circleIntegral` and Cauchy integral formula in
   `Mathlib.Analysis.Complex.CauchyIntegral`. Lives in
   `HexRootsMathlib/ArgumentPrinciple.lean`.

7. **Rouché on circles** — both classical (`|f − g| < |g|` on the
   circle implies `f`, `g` have the same number of zeros inside) and
   symmetric (`|f − g| < |f| + |g|` ditto) forms. Derived from item 6.
   Lives in `HexRootsMathlib/Rouche.lean`.

8. **Pellet (BSSY Theorem 1):**
   ```
   |c_k|·r^k > Σ_{i ≠ k} |c_i|·r^i ⇒ p has exactly k roots in D(0, r)
   ```
   where `cᵢ = p.coeff i`. Proved by Rouché-comparing `p` against the
   monomial `c_k · z^k`. Lives in `HexRootsMathlib/Pellet.lean`.

The squared-form Pellet inequality used in `HexRoots/Pellet.lean` is
equivalent to the standard form in item 8, via the elementary
`a > 0 ∧ b > 0 → (a > b ↔ a² > b²)`. We prove this equivalence in the
bridge file `HexRootsMathlib/Geometry.lean` so that the analytic core
can stay in the standard form (more upstream-friendly) while the
computational library uses the squared form (decidable in dyadics).

## Bridge proper

These files use both `HexRoots` data structures and the analytic /
discriminant cores above.

- `HexRootsMathlib/Basic.lean` — definitional bridge: a `DyadicSquare`
  determines a centre `c : ℂ` and a radius `r : ℝ`, and a
  circumscribed disc `Metric.ball c (r·√2)`. Core simp lemmas
  (`DyadicSquare.center_eq`, `DyadicSquare.disc_eq`).
- `HexRootsMathlib/Geometry.lean` — the squared-radius bridge:
  `circumscribed_radius_squared : (r · Real.sqrt 2)² = 2 · r²`, plus
  the `T_k` squared-form ↔ standard-form equivalence.
- `HexRootsMathlib/HasOnlySimpleRoots.lean`:
  `Hex.HasOnlySimpleRoots p ↔ Squarefree (toPolynomial p)`. Combines
  the `HexRoots`-side gcd-based decision procedure with Mathlib's
  `separable_iff_squarefree`.
- `HexRootsMathlib/MahlerPrec.lean` — item 4 above.
- `HexRootsMathlib/Cauchy.lean` —
  `DyadicRootCluster.cauchy` correctness: the cluster contains all
  `Polynomial.roots p` and the strong `T_k` witness holds at radii
  `r`, `2r`, `4r`. Uses `Polynomial.cauchyBound` for containment, and
  the elementary observation that the leading-term inequality
  `|aₙ|·Rⁿ > Σ_{i<n}|aᵢ|·Rⁱ` only strengthens for `R > Cauchy bound`.
- `HexRootsMathlib/Newton.lean` —
  `DyadicRootIsolation.refine?` correctness: when it returns
  `some iso'`, `iso'` certifies the same simple root and `iso'.prec >
  iso.prec`. Bridges to `Polynomial.newtonMap` and
  `aeval_pow_two_pow_dvd_aeval_iterate_newtonMap`; also requires a
  small bound on the `Dyadic.invAtPrec` rounding error, supplied by
  `Dyadic.invAtPrec_mul_le_one` and `Dyadic.one_lt_invAtPrec_add_inc_mul`
  in the Lean stdlib.
- `HexRootsMathlib/Bisection.lean` —
  `DyadicRootCluster.refine1?` correctness: when it returns
  `some children`, the multiset of root counts in the children's
  discs (with multiplicity) equals the parent cluster's `k`. Uses
  Pellet (item 8) and a finite case analysis over the 4-square
  partition + edge-connected-components glue.
- `HexRootsMathlib/IsolateAll.lean` —
  `isolateAll?` and `isolate` correctness theorems:
  ```lean
  theorem isolateAll?_eq_some_iff (p : ZPoly) (target : Nat) :
      ∃ result, isolateAll? target [DyadicRootCluster.cauchy p] = some result ∧
        (result.toList.bind (·.roots) : Multiset ℂ) = (toPolynomial p).roots

  theorem isolate_eq_some (p : ZPoly) (h : Hex.HasOnlySimpleRoots p) (atom_prec : Nat) :
      ∃ atoms, isolate p h atom_prec = some atoms ∧
        (atoms.map (·.root) : Finset ℂ) = (toPolynomial p).roots.toFinset ∧
        ∀ a ∈ atoms, a.square.prec ≥ atom_prec
  ```
- `HexRootsMathlib/Conformance.lean` — the standard conformance
  module, asserting Mathlib-side properties on a small set of
  committed fixtures.

## Layered file organisation

```
Discriminant / separation core (upstreamable):
  HexRootsMathlib/DiscriminantSquarefree.lean
  HexRootsMathlib/DiscriminantRootProduct.lean
  HexRootsMathlib/MahlerSeparation.lean

Analytic core (upstreamable, but depends on serious circle-integral
work and is the harder of the two):
  HexRootsMathlib/CircleIntegralLemmas.lean
  HexRootsMathlib/ArgumentPrinciple.lean
  HexRootsMathlib/Rouche.lean
  HexRootsMathlib/Pellet.lean

Bridge (depends on hex-roots data structures):
  HexRootsMathlib/Basic.lean
  HexRootsMathlib/Geometry.lean
  HexRootsMathlib/HasOnlySimpleRoots.lean
  HexRootsMathlib/MahlerPrec.lean
  HexRootsMathlib/Cauchy.lean
  HexRootsMathlib/Newton.lean
  HexRootsMathlib/Bisection.lean
  HexRootsMathlib/IsolateAll.lean
  HexRootsMathlib/Conformance.lean
```

The two cores have no `HexRoots`-dependence and may be split into their
own libraries (or upstreamed to Mathlib) if they grow. The bridge
files depend on `HexRoots`'s data definitions and on whichever core
theorems they need.

## References

See [hex-roots.md](hex-roots.md) for the BSSY paper, Pellet, Mahler,
and Mignotte references. The discriminant and Mahler-measure
infrastructure cited above is documented in:

- Becker, Sagraloff, Sharma, Yap, JSC 2018 — same as before; §2 has
  the exact form of the Pellet inequality and its derivation from
  Rouché.
- Mignotte, Štefănescu. *Polynomials: An Algorithmic Approach.*
  Springer, 1999. Chapter 4 has a clean self-contained proof of the
  Mahler/Mignotte separation bound suitable for direct
  formalisation.
- Yap. *Fundamental Problems of Algorithmic Algebra.* Oxford, 2000.
  §6.6 gives an alternative derivation via Liouville-style estimates.
