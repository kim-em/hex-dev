# Algebraic-coefficient `rcf` examples

The source of the complete demonstration is
`conformance/HexRCF/RealCoefficientTactic.lean`. Its single module runs the
existing rational solver, a universal inequality with `Real.sqrt 2`, an
existential interval with `Real.sqrt 2`, Mathlib's cubic real root, Hex's
selected cubic `RealAlgebraicNumber`, a value computed by addition in
`QAdjoin`, a user-defined alias of that value, and false/unsupported cases.
All successful calls use `rcf` on the user's statement and finish with its
checked certificate path. The false and unsupported cases are wrapped in
`fail_if_success`.

On the shared host `chungus2`, a clean compilation of this module on 2026-09-25
took 91.89 seconds wall time, pinned to logical CPU 24. Lake reported 83 seconds
for the module itself. The three load averages at completion were 48.90,
33.13 and 36.87. This is one retained observation, not a scaling result or
a Phase-4 measurement.

To reproduce the end-to-end module timing after the dependencies have been
built, remove only `.lake/build/lib/lean/HexRCF/RealCoefficientTactic.olean`,
select a CPU with `python3 scripts/bench/idle_core.py`, and run
`taskset -c "$cpu" lake build HexRCF.RealCoefficientTactic`. The measured wall
time includes Lake startup, elaboration, certificate search, kernel replay and
writing the module artifacts. It excludes rebuilding dependencies.

An independent numerical check gives `sqrt 2 ≈ 1.41421356237`, the real
cubic root of two `≈ 1.25992104989`, and the fixed-field shift
`≈ 2.25992104989`. The existential example has the rational witness `17/12`:
its square is `289/144 > 2`, and `17/12 < 3/2`. The false universal statement
already fails at `x = 0`.
