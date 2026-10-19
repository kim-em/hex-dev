# Faster compiled Schreier-Sims in HexPermGroup

Two changes to the compiled construction. The timings below are exploratory
observations, not measurements under the paired protocol of
`SPEC/benchmarking.md`: the best of five runs of each case in one compiled
executable on 2026-10-06, on a shared 96-core machine with a load average of
about 8 to 20, with the generators of
`reports/bench-results/perm-group-mathlib-free.json` and the Rubik's cube face
turns:

- `Group.ofGenerators` keeps the chain built by extension as the suffix, instead
  of constructing each level's suffix a second time.
- Orbits store their inverse representatives and which representatives are the
  identity, and compiled sifting and Schreier generators use them, so no sift
  inverts a permutation and single-point levels cost one lookup.

| group | degree | `ofGenerators` before | after | `Kernel.certify` before | after | GAP `Size` |
|---|---|---|---|---|---|---|
| M11 | 11 | 0.57 ms | 0.17 ms | 0.93 ms | 0.72 ms | 0.13 ms |
| M24 | 24 | 7.1 ms | 0.81 ms | 8.4 ms | 4.4 ms | 0.43 ms |
| J2 | 100 | 51 ms | 3.0 ms | 49 ms | 13 ms | 0.44 ms |
| HS | 100 | 116 ms | 5.7 ms | 115 ms | 24 ms | 0.68 ms |
| Rubik's cube | 54 | 639 ms | 37 ms | 1007 ms | 356 ms | 2.6 ms |
| cube reassembly | 54 | 1534 ms | 96 ms | 3578 ms | 1370 ms | 4.0 ms |
| McL | 275 | 1113 ms | 24 ms | 958 ms | 112 ms | 2.2 ms |
| Co3 | 276 | 2643 ms | 49 ms | 3429 ms | 259 ms | 3.2 ms |

"Before" is `main` at 983cb7c37 with
https://github.com/kim-em/hex-dev/pull/10814 applied. The GAP column is the best
of five runs of `Size(Group(gens))` on a fresh group in GAP 4.15.1 from nixpkgs,
measured on the same machine the same day.

On these observations, `Group.ofGenerators` is 1.3 to 24 times slower than
GAP. `Kernel.certify`
also runs its search for small next-level generating sets, which compares group
orders many times; it remains 6 to 340 times slower than GAP.
