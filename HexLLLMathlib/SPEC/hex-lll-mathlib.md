# hex-lll-mathlib (depends on hex-lll + Mathlib)

Connects hex-lll to Mathlib's linear algebra:
- Lattice corresponds to a `Submodule ℤ`
- Short vector bound holds with respect to Mathlib's `norm`

## Headline correctness theorem

`lll_first_row_norm_sq_le`: the Euclidean short-vector bound for
the public `lll`, stated with Mathlib's `EuclideanSpace` norm and `Submodule ℤ`
membership. For any nonzero lattice vector `x`,

    ‖row 0 of (lll b δ …)‖² ≤ (1/(δ − 121/400))^(n-1) · ‖x‖² .

It needs no reducedness hypothesis on the output (the `lll` post-condition is
discharged internally); it is built from the conditional bridge lemma
`reduced_first_row_norm_sq_le`, the same bound for a basis already known to be
`(δ, 11/20)`-reduced.

The theorem holds regardless of which path the dispatched `lll` took (native
or certified external), since both establish the `(δ, 11/20)`-reduced and
same-lattice post-condition that the bound consumes. The native entry
`lllNative` carries the corresponding classical statement at the tighter
constant `1/(δ − 1/4)`.
