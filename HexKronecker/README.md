# HexKronecker

Deterministic polynomial identity checks over integer expression trees, sparse
term lists, and rectangular polynomial matrices. The computational library has
no Mathlib dependency.

```lean
import HexKronecker
open Hex.Kronecker

def square : Expr := .pow (.add (.atom 0) (.atom 1)) 2

def expansion : Expr :=
  .add (.add (.pow (.atom 0) 2)
    (.mul (.int 2) (.mul (.atom 0) (.atom 1)))) (.pow (.atom 1) 2)

#guard checkExprEq {} 2 square expansion
```

Run `sizeExprEq`, `sizeTermsEq`, or `sizeMulTerms` first for structured validation
and size diagnostics. `Budget` limits the dense degree box and all packed
operands and intermediates independently. A Boolean check returns `false` for
malformed input, an exceeded budget, or unequal packed integers.

Matrix checks use `MulMode.plain` by default. `signedPacked` uses the existing
signed dot-product packing and budgets its larger outer operands separately.

The three `Mod` checks require canonical residue inputs and a canonical integer
quotient witnessing `L - R = p * Q`. They certify formal polynomial identities
in characteristic `p`. They do not certify additional identities of polynomial
functions on a finite field.

See the [SPEC](SPEC/hex-kronecker.md) for the complete contract and
[HexKroneckerMathlib](../HexKroneckerMathlib/README.md) for soundness and tactics.
