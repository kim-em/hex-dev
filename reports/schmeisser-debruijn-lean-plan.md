# Schmeisser/de Bruijn-Springer Lean Plan

## Target

Parent issue #5525 needs the `r = 1` filtered product inequality

```lean
theorem Polynomial.roots_filter_norm_product_derivative_le_roots
    (p : ℂ[X]) :
    ((p.derivative.roots.filter fun β => 1 ≤ ‖β‖).map fun β => ‖β‖).prod ≤
      ((p.roots.filter fun α => 1 ≤ ‖α‖).map fun α => ‖α‖).prod
```

This is the exact hypothesis consumed by
`Polynomial.prod_max_one_norm_roots_derivative_le_of_schmeisser_radius_one`
in `HexPolyZMathlib/RobinsonForm.lean`.

The source route is Schmeisser's Corollary 3 and Lemma 9 in
"Majorization of the Critical Points of a Polynomial by Its Zeros".  Lemma 9 is
the product estimate for the Schur-Szego composition of two degree-`n`
polynomials; Corollary 3 specializes the composition kernel
`g(z) = n z (z + 1)^(n - 1)`, whose normalized Hadamard product with `f` is
`z * f.derivative`.  Setting `r = 1` and deleting the extra root at zero gives
the theorem above.

## Source Decomposition

### 1. Schur-Szego Composition

Define the binomial-normalized Hadamard product used by Schmeisser:

```lean
noncomputable def Polynomial.schurSzegoComp (n : ℕ) (f g : ℂ[X]) : ℂ[X] :=
  ∑ k ∈ Finset.range (n + 1),
    C (f.coeff k * g.coeff k / (Nat.choose n k : ℂ)) * X ^ k
```

The useful form should be guarded by degree/normalization hypotheses rather
than by a custom coefficient sequence:

```lean
theorem Polynomial.schurSzegoComp_coeff
    (n k : ℕ) (hk : k ≤ n) (f g : ℂ[X]) :
    (Polynomial.schurSzegoComp n f g).coeff k =
      f.coeff k * g.coeff k / (Nat.choose n k : ℂ)

theorem Polynomial.schurSzegoComp_coeff_of_lt
    (n k : ℕ) (hk : n < k) (f g : ℂ[X]) :
    (Polynomial.schurSzegoComp n f g).coeff k = 0
```

Category: algebraic coefficient glue.

Likely imports: `Mathlib.Algebra.BigOperators.Finprod`, existing polynomial
coefficient imports already available through `HexPolyZMathlib.Basic`.

### 2. Derivative Kernel Algebra

For the special kernel `g_n = (n : ℂ[X]) * X * (X + 1) ^ (n - 1)`, prove its
normalized coefficients are `k`.

```lean
def Polynomial.schmeisserDerivativeKernel (n : ℕ) : ℂ[X] :=
  (C (n : ℂ)) * X * (X + 1) ^ (n - 1)

theorem Polynomial.coeff_schmeisserDerivativeKernel
    {n k : ℕ} (hk : k ≤ n) :
    (Polynomial.schmeisserDerivativeKernel n).coeff k =
      (Nat.choose n k : ℂ) * k
```

Then identify the composition output:

```lean
theorem Polynomial.schurSzegoComp_derivativeKernel_eq_X_mul_derivative
    (p : ℂ[X]) :
    Polynomial.schurSzegoComp p.natDegree p
      (Polynomial.schmeisserDerivativeKernel p.natDegree) =
        X * p.derivative
```

The proof is coefficientwise using `Polynomial.coeff_derivative`, the two
`schurSzegoComp` coefficient lemmas, and the fact that
`p.coeff k = 0` for `p.natDegree < k`.

Category: algebraic coefficient glue.

Likely imports: `Mathlib.Algebra.Polynomial.Derivative` via existing imports.

### 3. Kernel Roots Are in the Closed Unit Disk

The source theorem only needs the kernel's roots in the closed unit disk:

```lean
theorem Polynomial.roots_schmeisserDerivativeKernel_norm_le_one
    (n : ℕ) :
    ∀ z ∈ (Polynomial.schmeisserDerivativeKernel n).roots, ‖z‖ ≤ 1
```

For `n = 0`, the kernel is zero and `roots_zero` makes the goal trivial.  For
`n = 1`, the kernel is `X`.  For `2 ≤ n`, use `roots_C_mul`,
`roots_mul`, `roots_X`, and `roots_pow`/`roots_X_add_C`: the only roots are
`0` and `-1`.

Category: polynomial root API glue.

Likely imports: `Mathlib.Algebra.Polynomial.Splits` and the already imported
root lemmas in `Mathlib.Algebra.Polynomial.Roots`.

### 4. General Schmeisser Composition API

The hard analytic statement should be formalized once, not hidden inside the
derivative theorem:

```lean
theorem Polynomial.schurSzegoComp_roots_filter_norm_product_le
    (n : ℕ) (f g : ℂ[X])
    (hg : ∀ z ∈ g.roots, ‖z‖ ≤ 1) :
    (((Polynomial.schurSzegoComp n f g).roots.filter fun ζ => 1 ≤ ‖ζ‖).map fun ζ => ‖ζ‖).prod ≤
      ((f.roots.filter fun z => 1 ≤ ‖z‖).map fun z => ‖z‖).prod
```

This is the Lean-facing form of Schmeisser Lemma 9 with `r = 1`.  The source
proof cites de Bruijn-Springer, "On the zeros of composition-polynomials",
Theorem 7.  A direct formalization can avoid sorted roots entirely by working
with filtered multisets and products.

Category: analytic/source theorem.  This is the substantial missing result.

Likely imports: root API plus whatever analytic infrastructure is needed for
the de Bruijn-Springer composition theorem.

### 5. Remove the Extra `X` Root

Schmeisser's derivative specialization gives a product comparison for
`X * p.derivative`.  The local bridge back to `p.derivative` is purely
multiset-level:

```lean
theorem Polynomial.roots_filter_norm_product_derivative_le_of_X_mul_derivative
    (p : ℂ[X])
    (h :
      (((X * p.derivative).roots.filter fun β => 1 ≤ ‖β‖).map fun β => ‖β‖).prod ≤
        ((p.roots.filter fun α => 1 ≤ ‖α‖).map fun α => ‖α‖).prod) :
    ((p.derivative.roots.filter fun β => 1 ≤ ‖β‖).map fun β => ‖β‖).prod ≤
      ((p.roots.filter fun α => 1 ≤ ‖α‖).map fun α => ‖α‖).prod
```

When `p.derivative = 0`, the left product is empty.  Otherwise,
`roots_mul` and `roots_X` identify `(X * p.derivative).roots` with
`{0} + p.derivative.roots`; the filter `1 ≤ ‖β‖` removes the extra zero.

Category: polynomial root API glue.

Likely imports: current `HexPolyZMathlib/RobinsonForm.lean` imports are enough.

### 6. Final Assembly

The report target follows by applying the hard Schur-Szego product theorem to
`f = p`, `g = schmeisserDerivativeKernel p.natDegree`, rewriting the output as
`X * p.derivative`, and deleting the extra zero root:

```lean
theorem Polynomial.roots_filter_norm_product_derivative_le_roots
    (p : ℂ[X]) :
    ((p.derivative.roots.filter fun β => 1 ≤ ‖β‖).map fun β => ‖β‖).prod ≤
      ((p.roots.filter fun α => 1 ≤ ‖α‖).map fun α => ‖α‖).prod
```

Then downstream code should expose:

```lean
theorem Polynomial.prod_max_one_norm_roots_derivative_le_prod_max_one_norm_roots
    (p : ℂ[X]) :
    (p.derivative.roots.map fun β => max (1 : ℝ) ‖β‖).prod ≤
      (p.roots.map fun α => max (1 : ℝ) ‖α‖).prod :=
  Polynomial.prod_max_one_norm_roots_derivative_le_of_schmeisser_radius_one p
    (Polynomial.roots_filter_norm_product_derivative_le_roots p)
```

## Route Explicitly Ruled Out

Do not try to prove the derivative product comparison by reflecting one exterior
root at a time and proving endpoint monotonicity for
`Polynomial.derivativeMahlerAlongLinearFactor`.  The repository contains
`scripts/oracle/mahler_schur_counterexample.py`, which checks the concrete
counterexample

```text
f = 2 X^3 + 2 X^2 - 3 X - 4,  alpha = -2
```

For this example the direct and scaled one-root endpoint inequalities both
fail.  The valid source route is the global de Bruijn-Springer/Schmeisser
composition theorem, not one-root Schur endpoint monotonicity.

## First Follow-Up Work Items

1. Prove the `X * p.derivative` root-removal lemma in
   `HexPolyZMathlib/RobinsonForm.lean`.  This is independent of the hard
   Schur-Szego theorem.
2. Prove the derivative-kernel algebra and root-location lemmas in a small
   local section or helper module.  This is independent of the hard theorem and
   gives the exact specialization target.
3. Formalize the `r = 1` Schur-Szego filtered product theorem.  This is the
   hard source-theorem issue and should depend on the kernel algebra only for
   final derivative assembly, not for the theorem itself.
