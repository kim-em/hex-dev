# BHKS Resultant And Hadamard Infrastructure Review

## Scope

This review fixes the current resultant/Hadamard infrastructure surface for the
BHKS D1 route in `SPEC/Libraries/hex-berlekamp-zassenhaus.md`. It is a
Mathlib-bridge audit only: no executable factoring API, Lean source, SPEC file,
workflow, or BHKS proof obligation is changed here.

Related local files:

- `HexBerlekampZassenhausMathlib/Resultant.lean`
- `HexBerlekampZassenhausMathlib/BadVector.lean`
- `HexBerlekampZassenhausMathlib/TerminationBound.lean`
- `reports/bhks-resultant-infrastructure.md`

## Mathlib4 Resultant Surface

Mathlib4 already exposes the required resultant definition and Sylvester matrix
in `Mathlib.RingTheory.Polynomial.Resultant.Basic`:

```text
Polynomial.sylvester
Polynomial.resultant
Polynomial.resultant_map_map
Polynomial.resultant_ne_zero
Polynomial.resultant_eq_zero_iff
Polynomial.isUnit_resultant_iff_isCoprime
Polynomial.exists_mul_add_mul_eq_C_resultant
```

The relevant upstream shapes are:

```text
Polynomial.sylvester
    (f g : Polynomial R) (m n : Nat) :
    Matrix (Fin (m + n)) (Fin (m + n)) R

Polynomial.resultant
    (f g : Polynomial R) (m : Nat := f.natDegree)
      (n : Nat := g.natDegree) : R

Polynomial.resultant_ne_zero
    [IsDomain R] (f g : Polynomial R) (H : IsCoprime f g) :
    Polynomial.resultant f g != 0

Polynomial.resultant_eq_zero_iff
    [Field K] {f g : Polynomial K} :
    Polynomial.resultant f g = 0 <->
      (f != 0 or g != 0) and not IsCoprime f g
```

Conclusion: no Mathlib3 resultant port is needed for BHKS D1.

## Local Hadamard And Resultant Bridge

`HexBerlekampZassenhausMathlib/Resultant.lean` already packages the upstream
Mathlib API in the integer-polynomial forms needed for the BHKS bad-vector
argument.

Available local determinant/resultant bounds:

```text
HexBerlekampZassenhausMathlib.abs_det_le_row_l2norm_prod
    {N : Nat} (A : Matrix (Fin N) (Fin N) Int) :
    |((A.det : Int) : Real)| <=
      product of row Euclidean norms

HexBerlekampZassenhausMathlib.abs_resultant_le_sylvester_row_l2norm_prod
    (f g : Polynomial Int) :
    |((Polynomial.resultant f g : Int) : Real)| <=
      product of Sylvester-row Euclidean norms

HexBerlekampZassenhausMathlib.abs_resultant_le_l2norm_pow
    (f g : Polynomial Int) :
    |((Polynomial.resultant f g : Int) : Real)| <=
      (HexPolyZMathlib.l2norm f) ^ g.natDegree *
        (HexPolyZMathlib.l2norm g) ^ f.natDegree
```

Available local coprimality/resultant-zero bridges:

```text
HexBerlekampZassenhausMathlib.int_resultant_ne_zero_of_coprime
    (f g : Polynomial Int) (h : IsCoprime f g) :
    Polynomial.resultant f g != 0

HexBerlekampZassenhausMathlib.resultant_map_intCast_rat
    (f g : Polynomial Int) :
    Polynomial.resultant
        (f.map (Int.castRingHom Rat)) (g.map (Int.castRingHom Rat)) =
      ((Polynomial.resultant f g : Int) : Rat)

HexBerlekampZassenhausMathlib.int_resultant_eq_zero_iff_not_coprime_over_rat
    (f g : Polynomial Int) :
    Polynomial.resultant f g = 0 <->
      ((f.map (Int.castRingHom Rat) != 0 or
          g.map (Int.castRingHom Rat) != 0) and
        not IsCoprime
          (f.map (Int.castRingHom Rat))
          (g.map (Int.castRingHom Rat)))

HexBerlekampZassenhausMathlib.int_resultant_ne_zero_of_coprime_over_rat
    (f g : Polynomial Int)
    (hcoprime :
      IsCoprime
        (f.map (Int.castRingHom Rat))
        (g.map (Int.castRingHom Rat))) :
    Polynomial.resultant f g != 0
```

These declarations cover the SPEC's requested surface:

- definition of `Polynomial.resultant`;
- Sylvester-matrix determinant interpretation;
- nonzero-resultant/coprimality criterion, with the BHKS-useful transported
  `Rat` form;
- Hadamard-style bound
  `|Res(f, g)| <= ||f||_2 ^ deg(g) * ||g||_2 ^ deg(f)`.

## Existing Bad-Vector Packaging

`HexBerlekampZassenhausMathlib/BadVector.lean` builds on the bridge above.
The most useful already-available abstraction is:

```text
structure BadVectorResultantData where
  f : Polynomial Int
  H : Polynomial Int
  p : Nat
  a : Nat
  d : Nat
  p_pos : 0 < p
  d_pos : 0 < d
  coprime_over_rat :
    IsCoprime
      (f.map (Int.castRingHom Rat))
      (H.map (Int.castRingHom Rat))
  resultant_divisible :
    ((p ^ (a * d) : Nat) : Int) divides Polynomial.resultant f H
```

Its main theorem shape is:

```text
BadVectorResultantData.badVector_resultant_bounds
    (f H : Polynomial Int) (p a d : Nat)
    (hp : 0 < p) (hd : 0 < d)
    (hcoprime :
      IsCoprime
        (f.map (Int.castRingHom Rat))
        (H.map (Int.castRingHom Rat)))
    (hdiv :
      ((p ^ (a * d) : Nat) : Int) divides
        Polynomial.resultant f H) :
    (p ^ (a * d) : Real) <=
      |((Polynomial.resultant f H : Int) : Real)| and
    |((Polynomial.resultant f H : Int) : Real)| <=
      (HexPolyZMathlib.l2norm f) ^ H.natDegree *
        (HexPolyZMathlib.l2norm H) ^ f.natDegree
```

There are also executable-witness wrappers around
`ExecutableBadVectorWitness`, so later work should not reopen the raw resultant
API. The intended boundary is: prove the BHKS Lemma 3.2 algebraic clauses for
the concrete auxiliary polynomial and hand them to the existing resultant
comparison package.

## Recommended Local Theorem Shapes

Later D1 work should consume the current infrastructure through the following
local theorem shapes.

### Nonzero/Divisibility/Resultant Criterion

For the abstract bad-vector layer, keep using `BadVectorResultantData` and the
existing `badVector_resultant_bounds` theorem. It has the right granularity:
coprimality over `Rat`, divisibility by the modular power, and the Hadamard
upper bound are all explicit and reusable.

For the executable BHKS witness layer, the missing proof should instantiate
the existing bridge with a theorem close to:

```text
theorem ExecutableBadVectorWitness.projectedBadVectorSetupBridge_of_bhks_data
    (W : ExecutableBadVectorWitness)
    (trueSupports : Set (Set (Fin W.projectedRows.factorCount))) :
    ExecutableBadVectorWitness.ProjectedBadVectorSetupBridge W trueSupports
```

The theorem should prove, from the actual CLD/Hensel/lattice construction,
the three currently abstract BHKS Lemma 3.2 clauses:

- the canonical auxiliary polynomial attached to a projected vector in
  `L' \ W`;
- rational coprimality of the input and auxiliary polynomials;
- divisibility of the integer resultant by
  `p ^ (k * selectedLocalFactorDegree)`.

### Norm Bound

For the pure polynomial resultant bound, later proofs should use:

```text
HexBerlekampZassenhausMathlib.abs_resultant_le_l2norm_pow
```

For the BHKS bad-vector contradiction, later proofs should use the bad-vector
wrapper rather than reproving Hadamard:

```text
BadVectorResultantData.no_badVector_of_l2norm_upper_lt_divisor_params
```

or the executable witness wrapper when the data is already in
`ExecutableBadVectorWitness` form.

### Transported `Hex.ZPoly` Form

The existing executable wrappers transport `Hex.ZPoly` to `Polynomial Int` via
`HexPolyZMathlib.toPolynomial`. That is the right boundary for D1. A separate
`Hex.ZPoly` resultant theorem should only be added if a later proof repeatedly
has to state the same transport boilerplate. If added, it should be a wrapper,
not a second resultant theory:

```text
theorem Hex.ZPoly.bhks_resultant_bounds
    (input H : Hex.ZPoly) (p k d : Nat)
    (hp : 0 < p) (hd : 0 < d)
    (hcoprime :
      IsCoprime
        ((HexPolyZMathlib.toPolynomial input).map (Int.castRingHom Rat))
        ((HexPolyZMathlib.toPolynomial H).map (Int.castRingHom Rat)))
    (hdiv :
      ((p ^ (k * d) : Nat) : Int) divides
        Polynomial.resultant
          (HexPolyZMathlib.toPolynomial input)
          (HexPolyZMathlib.toPolynomial H)) :
    ...
```

## Missing Infrastructure

No Mathlib resultant port, Sylvester matrix definition, or Hadamard determinant
bound is missing for the D1 route.

The remaining missing infrastructure is above the resultant layer:

- construction of the concrete BHKS Lemma 3.2 bad-vector setup from the
  executable CLD/Hensel/lattice data;
- proof that the auxiliary polynomial built by
  `BHKS.auxiliaryPolynomial` has the needed coprimality and modular
  divisibility properties;
- connection from the resultant lower/upper comparison to the cap-level
  `L' = W` separation theorem and finally to `factorFast_terminates`.

## Follow-Up Issue Titles

Recommended narrow follow-ups:

1. `BHKS D1: instantiate projected bad-vector resultant setup from executable CLD data`
   - Target: `HexBerlekampZassenhausMathlib/BadVector.lean`
   - Depends on: existing resultant bridge and lattice witness definitions.
   - Deliverable: prove the concrete `ProjectedBadVectorSetupBridge` instance
     or split its three algebraic fields into named lemmas.

2. `BHKS D1: prove auxiliary polynomial coprimality and resultant divisibility`
   - Target: `HexBerlekampZassenhausMathlib/BadVector.lean`
   - Depends on: the selected local-factor setup from the previous issue.
   - Deliverable: discharge the two algebraic fields that currently remain
     abstract in the bad-vector setup.

3. `BHKS D1: connect resultant bad-vector contradiction to cap separation`
   - Target: `HexBerlekampZassenhausMathlib/TerminationBound.lean`
   - Depends on: the concrete bad-vector setup bridge.
   - Deliverable: feed the existing resultant contradiction into the
     executable-cap separation hypotheses without restating resultant lemmas.

4. `BHKS D1: assemble factorFast termination from cap separation and recovery`
   - Target: `HexBerlekampZassenhausMathlib/Recovery.lean` or a small new
     imported helper under `HexBerlekampZassenhausMathlib/`
   - Depends on: cap separation, existing `bhksBound` dominance lemmas, and the
     recovery certificate path.
   - Deliverable: the leaf theorem `factorFast_terminates`.

## Probe Commands

The audit used local `#check` probes through Lake:

```sh
lake env lean <process-substitution-file>
```

The successful checked declarations included:

```text
Polynomial.resultant
Polynomial.sylvester
Polynomial.resultant_ne_zero
Polynomial.resultant_eq_zero_iff
Polynomial.resultant_map_map
HexBerlekampZassenhausMathlib.abs_det_le_row_l2norm_prod
HexBerlekampZassenhausMathlib.abs_resultant_le_l2norm_pow
HexBerlekampZassenhausMathlib.int_resultant_eq_zero_iff_not_coprime_over_rat
HexBerlekampZassenhausMathlib.BadVectorResultantData.badVector_resultant_bounds
HexBerlekampZassenhausMathlib.ExecutableBadVectorWitness.badVector_resultant_bounds
HexBerlekampZassenhausMathlib.ExecutableBadVectorWitness.resultant_divisible_by_p_pow_of_bhks_bad
```
