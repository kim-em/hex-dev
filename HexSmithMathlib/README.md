# hex-smith-mathlib

Part of [`hex`](https://github.com/kim-em/hex-dev), a computer algebra library
for Lean 4. `hex-smith-mathlib` is the correspondence-only Mathlib bridge for
[`hex-smith`](https://github.com/leanprover/hex-smith). It transports the
verified executable result into Mathlib's Smith-basis and quotient-module
interfaces without recomputing Smith normal form.

# Quickstart

Add to your `lakefile.toml`:

```toml
[[require]]
name = "hex-smith-mathlib"
git = "https://github.com/leanprover/hex-smith-mathlib.git"
rev = "main"
```

```lean
import HexSmithMathlib

open Hex HexSmithMathlib

#check @smithNormalForm
#check @smithNormalForm_chain
#check @quotientEquiv
```

# Functionality

- `ambientBasis` realizes the executable right transform as a Mathlib basis;
- `relationBasis` realizes the independent transformed presentation rows;
- `smithNormalForm` constructs `Module.Basis.SmithNormalForm` from those
  bases and the executable invariant factors;
- `smithNormalForm_chain` supplies the canonical divisibility order not
  stored by Mathlib's simultaneous-basis structure;
- `quotientEquiv` decomposes the presented quotient into its free coordinates
  and cyclic invariant-factor quotients.

# Verification

This package owns no executable surface. Every declaration is a proof or a
noncomputable equivalence built from `hex-smith` output, so executable
conformance and performance evidence remain owned by the Mathlib-free package.
`smithNormalForm_a` identifies Mathlib's coefficients with the executable
invariant factors; `ker_presentationMap` and `presentationMap_surjective`
establish the quotient decomposition without duplicating the computation.

# Contributing

Development happens in the [`hex-dev`](https://github.com/kim-em/hex-dev)
monorepo, not in the published mirror. Contributions are welcome as pull
requests to the monorepo.
