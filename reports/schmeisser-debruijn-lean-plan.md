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
`Polynomial.prod_max_one_norm_roots_derivative_le_of_schmeisser_radius_one`
shows that it is enough to prove the `r = 1` filtered product inequality:

```lean
theorem Polynomial.roots_filter_norm_product_derivative_le_roots
    (p : ℂ[X]) :
    ((p.derivative.roots.filter fun β => 1 ≤ ‖β‖).map fun β => ‖β‖).prod ≤
      ((p.roots.filter fun α => 1 ≤ ‖α‖).map fun α => ‖α‖).prod
```

Schmeisser's Corollary 3 and Lemma 9 in "Majorization of the Critical Points
of a Polynomial by Its Zeros" give the right source route.  Lemma 9 is a
product estimate for the Schur-Szego composition of two degree-`n`
polynomials; Corollary 3 specializes the composition kernel to
`g(z) = n z (z + 1)^(n - 1)`, whose normalized Hadamard product with `f` is
`z * f.derivative`.  Setting `r = 1` and deleting the extra root at zero gives
the theorem above.

## Source Shape

In Schmeisser's notation, for the binomial-normalized Hadamard composition

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
polynomial theorem.

For Lean, the useful form should use `Polynomial.roots` multisets directly so
multiplicities match the downstream reducer.  A coefficient-level statement is
probably easier than committing to a permanent public composition definition:

```lean
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

Classification: hard analysis/polynomial root theorem.  This is the
de Bruijn-Springer/Schmeisser core and should be isolated from local derivative
adapters.

Likely imports: `Mathlib.Analysis.Complex.Polynomial.GaussLucas`,
`Mathlib.Algebra.Polynomial.Splits`, existing Mahler/root-product imports, plus
whatever Mathlib develops for composition polynomials.

## Local Algebraic Decomposition

### 1. Optional Schur-Szego Composition Definition

If a reusable definition is helpful, define the binomial-normalized Hadamard
product used by Schmeisser:

```lean
noncomputable def Polynomial.schurSzegoComp (n : ℕ) (f g : ℂ[X]) : ℂ[X] :=
  ∑ k ∈ Finset.range (n + 1),
    C (f.coeff k * g.coeff k / (Nat.choose n k : ℂ)) * X ^ k
```

The basic coefficient API should be:

```lean
theorem Polynomial.schurSzegoComp_coeff
    (n k : ℕ) (hk : k ≤ n) (f g : ℂ[X]) :
    (Polynomial.schurSzegoComp n f g).coeff k =
      f.coeff k * g.coeff k / (Nat.choose n k : ℂ)

theorem Polynomial.schurSzegoComp_coeff_of_lt
    (n k : ℕ) (hk : n < k) (f g : ℂ[X]) :
    (Polynomial.schurSzegoComp n f g).coeff k = 0
```

Classification: algebraic coefficient glue.

### 2. Derivative Kernel Algebra

The special kernel is

```lean
def Polynomial.schmeisserDerivativeKernel (n : ℕ) : ℂ[X] :=
  C (n : ℂ) * X * (X + 1) ^ (n - 1)
```

Its coefficients normalize to the derivative coefficients:

```lean
theorem Polynomial.coeff_X_mul_derivative_eq_schmeisser_coeff
    (p : ℂ[X]) {n k : ℕ} (hk : k ≤ n) :
    (X * p.derivative).coeff k =
      p.coeff k * (Polynomial.schmeisserDerivativeKernel n).coeff k /
        (Nat.choose n k : ℂ)
```

If the explicit composition definition is introduced, this coefficient lemma
can be packaged as:

```lean
theorem Polynomial.schurSzegoComp_derivativeKernel_eq_X_mul_derivative
    (p : ℂ[X]) :
    Polynomial.schurSzegoComp p.natDegree p
      (Polynomial.schmeisserDerivativeKernel p.natDegree) =
        X * p.derivative
```

Classification: algebraic polynomial API glue.

Likely imports: `Mathlib.Algebra.Polynomial.Derivative`, already available
through current imports.

### 3. Unit-Disk Roots of the Derivative Kernel

The source theorem only needs the kernel's roots in the closed unit disk:

```lean
theorem Polynomial.roots_derivative_kernel_norm_le_one (n : ℕ) :
    ∀ z ∈ (Polynomial.schmeisserDerivativeKernel n).roots, ‖z‖ ≤ 1
```

For `n = 0`, the kernel is zero and `roots_zero` makes the goal trivial.  For
`n = 1`, the kernel is `X`.  For `2 ≤ n`, use `roots_C_mul`, `roots_mul`,
`roots_X`, and `roots_pow`/`roots_X_add_C`: the only roots are `0` and `-1`.

Classification: polynomial root API glue.

Likely imports: `Mathlib.Algebra.Polynomial.Splits` and the already imported
root lemmas in `Mathlib.Algebra.Polynomial.Roots`.

### 4. Remove the Extra `X` Root

Schmeisser's derivative specialization gives a product comparison for
`X * p.derivative`.  The bridge back to `p.derivative` is purely multiset-level:

```lean
theorem Polynomial.roots_filter_norm_product_derivative_le_of_X_mul_derivative
    (p : ℂ[X])
    (h :
      (((X * p.derivative).roots.filter fun β => 1 ≤ ‖β‖).map fun β => ‖β‖).prod ≤
        ((p.roots.filter fun α => 1 ≤ ‖α‖).map fun α => ‖α‖).prod) :
    ((p.derivative.roots.filter fun β => 1 ≤ ‖β‖).map fun β => ‖β‖).prod ≤
      ((p.roots.filter fun α => 1 ≤ ‖α‖).map fun α => ‖α‖).prod
```

When `p.derivative = 0`, the left product is empty.  Otherwise, `roots_mul` and
`roots_X` identify `(X * p.derivative).roots` with
`{0} + p.derivative.roots`; the filter `1 ≤ ‖β‖` removes the extra zero.

Classification: polynomial root API glue.

## Final Assembly

The report target follows by applying the hard Schur-Szego product theorem to
`f = p`, `g = schmeisserDerivativeKernel p.natDegree`,
`h = X * p.derivative`, and `r = 1`; discharging the kernel root bound;
rewriting the composition output with the derivative coefficient theorem; and
deleting the extra zero root:

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
f = 2 X^3 + 2 X^2 - 3 X - 4, alpha = -2
```

For this example the direct and scaled one-root endpoint inequalities both
fail.  The valid source route is the global de Bruijn-Springer/Schmeisser
composition theorem, not one-root Schur endpoint monotonicity.

## Follow-Up Work

1. Keep the derivative-kernel coefficient, kernel-root, and extra-`X`
   adapters as local API around `HexPolyZMathlib/RobinsonForm.lean` unless a
   reusable Schur-Szego module is introduced.
2. Formalize the `r = 1` Schur-Szego filtered product theorem.  This is the
   hard source-theorem issue and should depend on the local algebra only for
   final derivative assembly, not for the theorem itself.
3. Assemble
   `Polynomial.roots_filter_norm_product_derivative_le_roots` from the
   source theorem and feed it to the existing max-one-norm reducer.
