module

public import HexHensel.Basic
public import HexHensel.Linear
public import HexHensel.Multifactor
public import HexHensel.Quadratic
public import HexHensel.QuadraticMultifactor

public section

/-!
The `HexHensel` library provides the executable conversion and lifting layers
shared by later Hensel algorithms, starting with conversions between `ZPoly`
and `FpPoly p`, coefficientwise reduction modulo powers of `p`, the iterative
`henselLift` wrapper for lifting from modulus `p` to `p^k`, and the linear and
quadratic single-step updates from modulus `p^k` to `p^(k+1)` and from `m` to
`m^2`, plus the ordered multifactor lift API (linear and quadratic doubling)
used by factorization pipelines.
-/
