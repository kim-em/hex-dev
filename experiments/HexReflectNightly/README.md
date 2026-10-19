# HexReflect nightly validation

Build the production reflection sources and their existing core, scope and
residue conformance suites with the Lean nightly that provides guarded
polynomial expansion:

```sh
cd experiments/HexReflectNightly
lake update
lake exe cache get Mathlib.Algebra.Field.ZMod Mathlib.LinearAlgebra.Matrix.Notation Mathlib.RingTheory.MvPolynomial.Basic Mathlib.Algebra.Polynomial.Coeff
lake build
```

The package reads Hex source files from the monorepo and pins Mathlib's
matching nightly-testing revision. It does not copy or replace library code.
The core sources remain Mathlib-free; Mathlib is used by the bridge libraries
and their conformance tests. This package does not change the monorepo's
release toolchain or validate its other libraries.
