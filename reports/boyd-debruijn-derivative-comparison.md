# Boyd/de Bruijn-Springer Derivative Comparison

## Source Route

The non-circular route for the Robinson-form derivative chain should use the
de Bruijn-Springer critical-point product comparison, preferably through the
weak log-majorization/root-product formulation rather than through one-root
Schur endpoint monotonicity.

Primary source:

- N. G. de Bruijn and T. A. Springer, "On the zeros of a polynomial and of its
  derivative II", Proceedings of the Section of Sciences of the Koninklijke
  Nederlandse Akademie van Wetenschappen te Amsterdam 50(5), 264-270, 1947.
  The Eindhoven portal records the article metadata and published PDF:
  <https://research.tue.nl/en/publications/on-the-zeros-of-a-polynomial-and-of-its-derivative-ii>

Readable later formulation:

- G. Schmeisser, "Majorization of the Critical Points of a Polynomial by Its
  Zeros", Computational Methods and Function Theory 3(1), 95-103, 2003.
  Its proof cites de Bruijn-Springer and states the product inequality in a
  form directly aligned with Mahler root products.

Schmeisser's Lemma 9 gives, for a polynomial with zeros `z_ν` and derivative
zeros `ζ_ν`, the product comparison

```text
∏_{|ζ_ν| ≥ r} |ζ_ν| / r ≤ ∏_{|z_ν| ≥ r} |z_ν| / r
```

for every `r > 0`. With `r = 1`, this is exactly the derivative root-product
comparison needed downstream:

```lean
theorem prod_max_one_norm_roots_derivative_le_natDegree_mul_prod_max_one_norm_roots
    (p : ℂ[X]) :
    (p.derivative.roots.map (fun β => max (1 : ℝ) ‖β‖)).prod ≤
      (p.roots.map (fun α => max (1 : ℝ) ‖α‖)).prod
```

The theorem name currently used by #5506 includes `natDegree_mul`, but the
right-hand side has no extra `natDegree` factor; the degree factor enters only
when translating this root-product statement into Mahler measure:

```lean
theorem mahlerMeasure_derivative_le_natDegree_mul_mahlerMeasure
    (p : ℂ[X]) :
    p.derivative.mahlerMeasure ≤ p.natDegree * p.mahlerMeasure
```

because `p.derivative.leadingCoeff = p.leadingCoeff * p.natDegree` when
`0 < p.natDegree`.

## Lean Shape

The implementation issue should not try to prove a monotonicity statement for
`derivativeMahlerAlongLinearFactor` along `schurRootPath`; the committed
counterexample script shows that the direct and scaled one-step endpoint
comparisons are false in the needed generality.

The best local theorem target is a root-product/log-majorization theorem over
the roots of `p.derivative`, independent of Robinson form:

```lean
theorem prod_max_one_norm_roots_derivative_le_prod_max_one_norm_roots
    (p : ℂ[X]) :
    (p.derivative.roots.map (fun β => max (1 : ℝ) ‖β‖)).prod ≤
      (p.roots.map (fun α => max (1 : ℝ) ‖α‖)).prod
```

An equivalent logarithmic formulation is also acceptable and may be easier to
compose with existing local reducers:

```lean
theorem sum_log_max_one_norm_roots_derivative_le_sum_log_max_one_norm_roots
    (p : ℂ[X]) :
    (p.derivative.roots.map fun β => Real.log (max (1 : ℝ) ‖β‖)).sum ≤
      (p.roots.map fun α => Real.log (max (1 : ℝ) ‖α‖)).sum
```

`prod_max_one_norm_roots_derivative_le_of_sum_log_le` already converts the
logarithmic version to the root-product version.

## Implementation Notes

The source theorem is stronger than the Robinson endpoint comparison: it
directly controls derivative roots by original roots. This means #5506 can
derive both requested results without reflecting roots one at a time.

For the Mahler inequality, use the same leading-coefficient calculation already
present in `prod_max_one_norm_roots_derivative_le_of_mahlerMeasure_derivative_le`,
but in the forward direction:

1. Split `p.natDegree = 0`, where `p.derivative = 0`.
2. For positive degree, rewrite both Mahler measures with
   `mahlerMeasure_eq_leadingCoeff_mul_prod_roots`.
3. Rewrite `p.derivative.leadingCoeff` as
   `p.leadingCoeff * (p.natDegree : ℂ)`.
4. Multiply the root-product theorem by
   `(p.natDegree : ℝ) * ‖p.leadingCoeff‖`.

The Jensen helper `Polynomial.mahlerMeasure_le_circleAverage_norm` remains a
valid analytic ingredient, but it is not the shortest path to #5506 once the
de Bruijn-Springer product comparison is used directly.
