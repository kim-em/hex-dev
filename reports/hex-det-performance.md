# HexDet Performance Report

`HexDet` owns the determinant dispatch entry point `Hex.Det.det`. It adds no
determinant algorithm, so its Phase-4 surface is the choice between the arms it
interprets and the cost of interpreting them: fraction-free Bareiss from
`HexBareiss` against Berkowitz from `HexCharPoly` on identical inputs, and
dispatch against the arm its recipe selects.

Internal adjacent-arm comparisons determine selection. The external comparators
registered in `libraries.yml` are informational: FLINT's `fmpz_mat.det()`,
`fmpq_mat.det()` and `nmod_mat.det()` via python-flint, and SymPy's
`Matrix.det(method="berkowitz")` over exact polynomial domains, all of which
choose their own algorithm and carry their own process overhead. They cross-check
every dispatch answer in the conformance oracles rather than setting a cutoff.
The dispatch-overhead and route-agreement surfaces have comparator-absence class
`no-comparable-surface-in-named-comparator`: neither python-flint nor SymPy
exposes arm selection or a fallback route as a callable operation.

## Policy status: unmeasured

Every carrier's post-small selection is unconditional in this version, so there
is no crossover constant, coefficient-size region, tie rule, fuel setting or seed
to record. The initial availability rules are labelled **unmeasured**, exactly as
`HexDet/SPEC/hex-det.md` requires:

| Carrier | Selection above `n ≤ 2` | Status |
|---|---|---|
| `Int` | Bareiss at every `n > 2` | unmeasured; modular selection needs `hex-modular-matrix` |
| `Rat`, `ZMod64 p` | Bareiss at every `n > 2` | unmeasured; elimination needs a determinant-specific `HexRowReduce` operation |
| `DensePoly R`, `MvPoly k R cmp` | Bareiss at every `n > 2` | unmeasured |
| remaining commutative rings | Berkowitz | not a crossover: the carrier has no exact quotient |

The measurements below do not change any of these. They record what the two
available arms cost relative to one another, so the first crossover measurement
has a baseline to extend.

## Bench targets

Scientific registrations, one per Phase-4 input family:

- `Hex.DetBench.runDetInt`: `n * n * n` (`integer`)
- `Hex.DetBench.runDetRat`: `n * n * n` (`field`)
- `Hex.DetBench.runDetPoly`: `n * n * n * n` (`dense-poly`)
- `Hex.DetBench.runDetMv`: `n * n * n * n` (`mv-poly`)
- `Hex.DetBench.runBerkowitzInt`: `n * n * n * n` (the compared arm)

Adjacent-arm fixed registrations: `runBareissInt{6,10,16,24}` against
`runBerkowitzInt{…}`, `runBareissPoly{4,6,8}` against `runBerkowitzPoly{…}`,
and `runDetInt{6,10,16,24}` against `runBareissInt{…}` for the `dispatch`
family. `runRouteAgreement` is the Mathlib-free canary that checks routes and
bounded fixture outputs; it runs in CI under `lake exe hexdet_bench verify`.

## Host context

Source revision `9154473b5`. Host `chungus2`, AMD EPYC 9455 48-Core Processor, Linux 6.12.100
(NixOS), Lean 4.34.0-rc2. The host is shared and was under ordinary load
(1-minute load average between 6 and 10 across the session). Each measurement was
pinned to one automatically selected CPU via
`taskset -c $(python3 scripts/bench/idle_core.py)`, which prevents two Hex
measurements from choosing the same logical CPU; it is placement, not isolation,
and the selected CPU was not required to be idle. Every completed run is
retained. Absolute wall-clock values are host-specific observations.

## Scaling

Command: `lake exe hexdet_bench run <target>`.

| Target | Parameters | Per-call | Verdict |
|---|---|---|---|
| `runDetInt` | 8, 12, 16 | 3.817 µs, 10.496 µs, 26.754 µs | consistent (cMin=6.075, cMax=7.456) |
| `runDetRat` | 6, 9, 12 | 33.078 µs, 110.938 µs, 257.885 µs | consistent (cMin=149.239, cMax=153.141) |
| `runDetPoly` | 4, 6, 8 | 7.770 µs, 33.655 µs, 115.964 µs | consistent (cMin=25.969, cMax=30.355) |
| `runDetMv` | 3, 4, 6 | 27.512 µs, 88.016 µs, 487.930 µs | consistent (cMin=339.658, cMax=376.489) |
| `runBerkowitzInt` | 6, 9, 12 | 6.542 µs, 25.243 µs, 69.797 µs | consistent (cMin=3.366, cMax=5.048) |

The two polynomial families were first declared `n^3`, counting ring operations,
and measured inconclusive: fraction-free elimination on linear entries reaches
degree `O(n)`, so one dense product costs `O(n)` coefficient operations rather
than constant time. The declared models are `n^4` for that reason, and both are
consistent at that model.

## Bareiss versus Berkowitz

Command:
`lake exe hexdet_bench compare <bareiss> <berkowitz> <berkowitz> <bareiss>`,
so the two arms are adjacent and the pair orientation alternates `AB`/`BA`
within each run. Both arms returned the same observed hash at every rung
(`agreement: all functions agree on output`). Medians of five repeats.

Integer entries (tridiagonal fixture, deterministic salt 71):

| n | Bareiss (AB) | Berkowitz (AB) | Berkowitz (BA) | Bareiss (BA) | Berkowitz / Bareiss |
|---:|---:|---:|---:|---:|---:|
| 6 | 1.931 µs | 6.979 µs | 6.980 µs | 1.926 µs | 3.61x, 3.62x |
| 10 | 5.795 µs | 37.196 µs | 37.447 µs | 5.800 µs | 6.42x, 6.46x |
| 16 | 25.416 µs | 218.075 µs | 210.604 µs | 25.392 µs | 8.58x, 8.29x |
| 24 | 87.772 µs | 1.129 ms | 1.140 ms | 87.402 µs | 12.87x, 12.99x |

Dense integer polynomial entries (linear entries, same fixture):

| n | Bareiss (AB) | Berkowitz (AB) | Berkowitz (BA) | Bareiss (BA) | Berkowitz / Bareiss |
|---:|---:|---:|---:|---:|---:|
| 4 | 7.933 µs | 13.673 µs | 13.574 µs | 8.877 µs | 1.72x, 1.71x |
| 6 | 34.262 µs | 63.556 µs | 63.296 µs | 34.016 µs | 1.86x, 1.85x |
| 8 | 116.194 µs | 212.846 µs | 213.278 µs | 117.008 µs | 1.83x, 1.84x |

Bareiss is ahead of Berkowitz at every measured dimension on both carriers, and
its lead widens with dimension over `Int`, which is what the declared `n^3`
against `n^4` models predict. Over dense polynomials the ratio is far smaller
and flat near 1.85x: Berkowitz performs no division, while Bareiss pays for exact
polynomial division by nonconstant pivots, and that cost grows alongside the
operation-count advantage.

These numbers do not move any policy. Both orientations agree to within 4% at
every rung, so no comparison here is inconclusive and no rerun was needed. What
they establish is that the shipped Bareiss selection is not contradicted by
evidence on the carriers where both arms are available; a carrier without an
exact quotient still has only Berkowitz.

## Dispatch overhead

Command: `lake exe hexdet_bench compare runBareissInt<n> runDetInt<n> runDetInt<n> runBareissInt<n>`.
Both arms agreed on output at every rung.

| n | selected arm directly | through dispatch (AB) | through dispatch (BA) | dispatch / direct |
|---:|---:|---:|---:|---:|
| 6 | 1.956 µs | 2.504 µs | 2.511 µs | 1.28x, 1.28x |
| 10 | 5.869 µs | 7.263 µs | 7.264 µs | 1.24x, 1.24x |
| 16 | 25.419 µs | 29.222 µs | 29.185 µs | 1.15x, 1.15x |
| 24 | 87.579 µs | 95.355 µs | 94.634 µs | 1.09x, 1.08x |

Interpreting a recipe costs one size test plus, for the integer recipe, one
`O(n^2)` pass carrying the entries through the representation maps. The maps are
the identity at `Int`, so that pass performs no arithmetic, but it does rebuild
the matrix buffer. Against the cubic elimination the cost decays as expected,
from 28% at `n = 6` to 8% at `n = 24`. A caller that wants the arm without the
entry point can still call `Hex.Matrix.bareiss` directly; dispatch exists to
choose, not to be the cheapest path to a fixed arm.

## Conformance cross-checks

`lake exe hexdet_emit_fixtures | python3 scripts/oracle/matrix_flint.py` checked
14 dispatch determinants against python-flint 0.9.0: eight integer cases through
`fmpz_mat.det()`, three rational cases through `fmpq_mat.det()` and three
prime-residue cases through `nmod_mat.det()`, at dimensions 4, 6 and 8 in dense,
singular, triangular, zero-leading-pivot, unimodular and wide-coefficient shapes.

`lake exe hexdet_emit_carrier_fixtures | python3 scripts/oracle/matrix_carriers.py`
checked 20 dispatch determinants against SymPy 1.14.0 over identical exact
polynomial domains: dense polynomials over `ZZ`, `QQ` and `GF(101)`, and
two-variable polynomials over `ZZ` and `QQ`, each in nonconstant, row-swapped,
singular and triangular shapes.

Both streams passed with zero failures.
