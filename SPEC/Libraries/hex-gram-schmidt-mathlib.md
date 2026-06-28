# hex-gram-schmidt-mathlib (depends on hex-gram-schmidt + Mathlib)

Proves that `GramSchmidt.Int.basis` corresponds to Mathlib's
`gramSchmidt`. Mathlib's version works over inner product spaces and
returns a family of vectors; ours returns a `Matrix Rat n m`. The
bridge proves they agree on each row.
