# Schmeisser/de Bruijn-Springer Lean Plan

## Target

The downstream theorem needed in `HexPolyZMathlib/RobinsonForm.lean` is:

```lean
theorem Polynomial.prod_max_one_norm_roots_derivative_le_prod_max_one_norm_roots
    (p : ℂ[X]) :
    (p.derivative.roots.map (fun β => max (1 : ℝ) ‖β‖)).prod ≤
      (p.roots.map (fun α => max (1 : ℝ) ‖α‖)).prod
```

The existing reducer
`prod_max_one_norm_roots_derivative_le_of_schmeisser_radius_one` shows that it
is enough to prove the `r = 1` filtered product inequality:

```lean
((p.derivative.roots.filter fun β => 1 ≤ ‖β‖).map fun β => ‖β‖).prod ≤
  ((p.roots.filter fun α => 1 ≤ ‖α‖).map fun α => ‖α‖).prod
```

## Source Shape

Schmeisser's Lemma 9 is the right source theorem.  In the paper's notation,
for the binomial-normalized Hadamard composition

```text
f(z) = sum a_nu z^nu
g(z) = sum choose n nu * b_nu * z^nu
h(z) = sum a_nu * b_nu * z^nu
```

if all zeros of `g` lie in the closed unit disk, then for every `r > 0`:

```text
prod_{|zeta| >= r} |zeta| / r <= prod_{|z| >= r} |z| / r
```

where `zeta` ranges over roots of `h` and `z` ranges over roots of `f`, with
multiplicity.  Schmeisser proves this from de Bruijn-Springer's composition
polynomial theorem, then derives the critical-point result by taking
`g(z) = n z (z + 1)^(n - 1)`, so `h = z * f.derivative`.

This route avoids the one-root Schur endpoint monotonicity shortcut.  The local
counterexample script already documents why that shortcut is not a valid source
theorem.

## Lean Decomposition

### 1. General Schmeisser Composition API

Natural statement:

```lean
noncomputable def Polynomial.schmeisserComposition
    (n : ℕ) (f g : ℂ[X]) : ℂ[X] := ...

theorem Polynomial.roots_filter_norm_product_le_of_schmeisserComposition
    {n : ℕ} {f g h : ℂ[X]} {r : ℝ}
    (hr : 0 < r)
    (hfg_degree : f.natDegree ≤ n ∧ g.natDegree ≤ n)
    (hh_coeff :
      ∀ k ≤ n,
        h.coeff k = f.coeff k * (g.coeff k / (Nat.choose n k : ℂ)))
    (hg_roots : ∀ z ∈ g.roots, ‖z‖ ≤ 1) :
    ((h.roots.filter fun ζ => r ≤ ‖ζ‖).map fun ζ => ‖ζ‖ / r).prod ≤
      ((f.roots.filter fun z => r ≤ ‖z‖).map fun z => ‖z‖ / r).prod
```

Classification: hard analysis/polynomial root theorem.  This is the de
Bruijn-Springer/Schmeisser core and should be isolated from local adapters.

Likely imports: `Mathlib.Analysis.Complex.Polynomial.GaussLucas`,
`Mathlib.Algebra.Polynomial.Splits`, existing Mahler/root-product imports,
plus whatever Mathlib develops for composition polynomials.

Notes:

- A coefficient-level statement is probably easier than introducing a permanent
  public definition if the theorem is only used once.
- The theorem should use `Polynomial.roots` multisets directly so multiplicities
  match the downstream reducer.
- The zero-at-origin extension in Schmeisser's Remark 2 matters for
  `g(z) = n z (z + 1)^(n - 1)` and for `z * f.derivative`.

### 2. Derivative as Schmeisser Composition

Natural statement:

```lean
theorem Polynomial.schmeisserComposition_derivative
    (p : ℂ[X]) :
    Polynomial.schmeisserComposition p.natDegree p
      ((p.natDegree : ℂ[X]) * X * (X + 1) ^ (p.natDegree - 1)) =
      X * p.derivative
```

or, without a definition:

```lean
theorem Polynomial.coeff_X_mul_derivative_eq_schmeisser_coeff
    (p : ℂ[X]) (k : ℕ) :
    (X * p.derivative).coeff k =
      p.coeff k * ((p.natDegree : ℂ) * k / (Nat.choose p.natDegree k : ℂ))
```

after choosing the exact `g` coefficient normalization.

Classification: algebraic polynomial API glue.

Likely imports: `Mathlib.Algebra.Polynomial.Derivative`, already available
through current imports.

Notes:

- This cluster should settle the exact coefficient normalization before the
  analytic theorem is attempted.
- Edge cases `p.natDegree = 0` and `k = 0` should be explicit, because
  `X * p.derivative` has an added zero root only when the derivative is nonzero.

### 3. Unit-Disk Roots of the Derivative Kernel

Natural statement:

```lean
theorem Polynomial.roots_derivative_kernel_norm_le_one (n : ℕ) :
    ∀ z ∈ (((n : ℂ[X]) * X * (X + 1) ^ (n - 1)).roots), ‖z‖ ≤ 1
```

Classification: algebraic root API glue.

Likely imports: `Mathlib.Algebra.Polynomial.Splits`.

Notes:

- The roots are `0` and `-1`, with multiplicity, so this should be much smaller
  than the Schmeisser core.
- Handle `n = 0` and `n = 1` without relying on informal degree conventions.

### 4. Remove the Extra `X` Root

Natural statement:

```lean
theorem Polynomial.roots_filter_norm_product_derivative_le_of_X_mul_derivative
    (p : ℂ[X])
    (h :
      (((X * p.derivative).roots.filter fun β => 1 ≤ ‖β‖).map fun β => ‖β‖).prod ≤
        ((p.roots.filter fun α => 1 ≤ ‖α‖).map fun α => ‖α‖).prod) :
    ((p.derivative.roots.filter fun β => 1 ≤ ‖β‖).map fun β => ‖β‖).prod ≤
      ((p.roots.filter fun α => 1 ≤ ‖α‖).map fun α => ‖α‖).prod
```

Classification: purely algebraic/multiset glue.

Likely imports: current `RobinsonForm.lean` imports are enough.

Notes:

- The extra root from `X` has norm `0`, so it is removed by the `1 ≤ ‖β‖`
  filter.
- The proof should be by cases on `p.derivative = 0`, then `roots_mul` and a
  small multiset filter/map normalization.

### 5. Final Local Assembly

Natural statement:

```lean
theorem Polynomial.schmeisser_radius_one_derivative
    (p : ℂ[X]) :
    ((p.derivative.roots.filter fun β => 1 ≤ ‖β‖).map fun β => ‖β‖).prod ≤
      ((p.roots.filter fun α => 1 ≤ ‖α‖).map fun α => ‖α‖).prod
```

Classification: assembly theorem.

Likely imports: the helper module containing clusters 1-4.

Proof outline:

1. Apply the general Schmeisser composition theorem to `f = p`,
   `g = (p.natDegree : ℂ[X]) * X * (X + 1) ^ (p.natDegree - 1)`,
   `h = X * p.derivative`, and `r = 1`.
2. Discharge `g`'s root bound with `roots_derivative_kernel_norm_le_one`.
3. Rewrite the composition output with the derivative coefficient theorem.
4. Remove the extra `X` root.
5. Feed the result to
   `prod_max_one_norm_roots_derivative_le_of_schmeisser_radius_one`.

## Explicit Non-Route

Do not try to prove this by reflecting one exterior root at a time through
`schurRootPath` monotonicity.  The desired global product comparison is a
majorization theorem, and the repository already has
`mahler_schur_counterexample.py` documenting the false one-root monotonicity
shape.  Any follow-up issue should cite Schmeisser Lemma 9 or
de Bruijn-Springer composition polynomials as the source theorem instead.
