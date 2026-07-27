# Berlekamp cached-GCD suffix profile (#8901)

## Result

The exact executable fast path improves the production-shaped SD4
witness-splitting median from 311.323 to 281.829 microseconds (**1.105x**).
SD3 improves by 1.052x and phi15 is unchanged. The production-shaped degree
6--24 split grid remains within 0.7% of the reference implementation, below
the issue's self-imposed 2% regression limit.

The production change is therefore retained. It reuses the remainder already
computed by the constant guard only when `2 ≤ f.size` and
`f.size < witness.size`. In that branch it resumes the original `gcdAux`
execution after its first two Euclidean steps, with the original remaining
fuel. Every other case uses `splitFactorAt` unchanged.

## Exact-output boundary

Calling `DensePoly.gcd f ((witness % f) - C c)` afresh is not equivalent to
the reference call: an equal-degree recursive child can return a different
associate. The implementation instead proves a generic two-step executable
identity beside `DensePoly.gcd`, then proves the constant-shift size and
remainder identities needed to instantiate it over `F_p`.

The original `kernelWitnessSplitAux` remains the reference implementation. A
parallel cached aux is proved equal to it by fuel induction. Consequently the
selected constant, exact factor coefficients, cofactor, factor multiset, and
depth-first stored order are all unchanged. Conformance pins both sides of the
conditional: the reachable equal-degree fallback that previously changed
`[1, 2]` to its associate `[4, 3]`, and a strictly larger `x³` witness that
executes the cached suffix. The complete ordered fallback output remains
`[[4, 2, 1], [1, 2], [3, 3]]`.

Parent-to-child remainder propagation is not included. The proven suffix is
local to one modulus and one reference GCD execution; substituting a chained
parent remainder would require a separate exact-representative argument and
additional recursive state. The same-factor suffix captures the measured SD4
win without changing the recursion API.

## Method

Both direct split callbacks mirror production's `f.size ≤ 2` leaf stop. They
start from the same precomputed fixed-space witnesses and differ only in the
candidate primitive:

- `reference` calls `splitFactorAt`;
- `cached` calls the exported production `splitFactorCached`, so its guard and
  fuel cannot drift from the implementation being measured.

Direct split times are medians of 101 compiled single-call samples. The
instrumented callbacks independently median the total split, guard reduction,
constant sweep, candidate/GCD, cofactor, and residual phases. The candidate/GCD
timer brackets the complete production candidate primitive, including its
constant subtraction. Dynamic work is checked on every sample: exact stored
factor-list checksum, factors visited, witnesses tried, constants, GCD calls,
successful splits, and ordered factor/cofactor degree pairs must agree before
any timing is printed.

The run was pinned to CPU 0. The identical-work reduction columns are a noise
control: they agree within 3.4% on the sub-microsecond grid reductions and
within 0.7% on phi15, SD3, and SD4. The SD4 GCD change is 13.8%, well beyond
that control delta.

## Measurements

Times are microseconds. `C/G` is both constants reached and GCD calls. The
checksum covers the exact stored factor list, not only its product or degrees.

| input | reference | cached | speedup | reduction ref/cached | GCD ref/cached | W | C/G | checksum | ordered degree pairs |
|---|---:|---:|---:|---:|---:|---:|---:|---:|---|
| d6 | 22.714 | 22.784 | 0.997x | 0.830 / 0.812 | 18.559 / 18.565 | 10 | 20 | 12943647002262511265 | `1x5;...;1x1` |
| d8 | 46.950 | 47.060 | 0.998x | 1.103 / 1.122 | 40.752 / 40.988 | 14 | 39 | 6283357429794540400 | `1x7;...;1x1` |
| d10 | 70.115 | 69.704 | 1.006x | 1.450 / 1.422 | 60.743 / 60.780 | 18 | 54 | 3998298845998779095 | `1x9;...;1x1` |
| d12 | 106.728 | 106.889 | 0.998x | 1.742 / 1.756 | 94.692 / 94.804 | 22 | 77 | 9665217755214970018 | `1x11;...;1x1` |
| d14 | 157.264 | 156.563 | 1.004x | 2.012 / 2.042 | 140.823 / 141.816 | 26 | 108 | 13989755340198403017 | `1x13;...;1x1` |
| d16 | 204.154 | 205.565 | 0.993x | 2.277 / 2.353 | 186.150 / 185.289 | 30 | 135 | 6549080309686313432 | `1x15;...;1x1` |
| d18 | 275.930 | 276.211 | 0.999x | 2.634 / 2.626 | 253.292 / 252.881 | 34 | 170 | 10732870400768916419 | `1x17;...;1x1` |
| d20 | 362.579 | 363.300 | 0.998x | 2.967 / 2.953 | 336.055 / 335.378 | 38 | 213 | 9198051421308553282 | `1x19;...;1x1` |
| d22 | 450.669 | 450.279 | 1.001x | 3.225 / 3.214 | 419.865 / 418.813 | 42 | 252 | 16564237336527959161 | `1x21;...;1x1` |
| d24 | 579.751 | 581.664 | 0.997x | 3.454 / 3.526 | 544.181 / 542.637 | 46 | 315 | 7097026405575266044 | `1x23;...;1x1` |
| phi15 | 9.884 | 9.935 | 0.995x | 1.622 / 1.632 | 6.690 / 6.791 | 6 | 3 | 8928916402575020184 | `4x4` |
| SD3 | 45.788 | 43.534 | 1.052x | 12.740 / 12.700 | 29.514 / 27.470 | 22 | 12 | 8608999440975272704 | `2x6;2x4;2x2` |
| SD4 | 311.323 | 281.829 | 1.105x | 101.634 / 101.566 | 196.951 / 169.710 | 78 | 42 | 12724129247731263996 | `2x14;2x12;2x10;2x8;2x6;2x4;2x2` |

For every row, the cached checksum equals the displayed reference checksum,
and factors visited, witnesses tried, constants, GCD calls, successful splits,
and ordered degree pairs agree exactly. All emitted phase and factor timing
fields are in `reports/bench-results/berlekamp-cached-gcd-profile.csv`.

A second complete pinned run reproduced SD4 at 1.105x and SD3 at 1.047x,
left phi15 unchanged, and kept every grid row within 0.5%. Its direct medians,
noise controls, and checksums are in
`reports/bench-results/berlekamp-cached-gcd-profile-repeat.csv`. Absolute times
rose under concurrent host load, but the matched A/B ratios remained stable.

## Environment

- source base: `dc008bc675d4`, plus the #8901 working-tree change;
- Lean: `leanprover/lean4:v4.32.0-rc1`;
- host: `chungus2`;
- CPU: AMD EPYC 9455 48-Core Processor, 96 logical CPUs;
- OS: Linux 6.12.95, x86-64;
- commands: `lake build hex_recursive_relift_spike`, then
  `taskset -c 0 env RELIFT_PROFILE=berlekamp
  .lake/build/bin/hex_recursive_relift_spike`.
