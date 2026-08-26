# Hex interval algebraic integration

`hex-interval-algebraic` is a planned Mathlib-facing integration library. It
registers interval providers backed by the certified real and complex
polynomial root-isolation libraries without adding those dependencies to
`hex-interval` or `hex-interval-mathlib`.

Its initial provider contract, supported coefficient fragment, solver
precedence, and acceptance programs are specified in
[the interval SPEC](../../HexInterval/SPEC/hex-interval.md#specialized-algebraic-solvers-before-generic-propagation).
