# Smaller `perm_group` certificates

The kernel checker sifts one Schreier generator per level generator and orbit
point, so its work at a level is proportional to the number of level
generators. Certificates used to copy each level's generators from
`Group.ofGenerators`, whose working arrays include every inverse. The checker
no longer requires generators closed under inverses, a next-level generator may
be a product of Schreier generators, and the producer chooses, for each level, a
few such products that generate the stabilizer: one Schreier generator when the
stabilizer is cyclic, usually two or three products, and more when its
pseudo-random search fails and a greedy choice takes over.

These are exploratory observations, not measurements under the shared-host
protocol of `SPEC/benchmarking.md`: single runs, or a few, on 2026-10-06 on a
shared 96-core machine (load average about 20), one process at a time, with
HexPermGroup precompiled. "Before" is `main` at 97d1f24d0 with
https://github.com/kim-em/hex-dev/pull/10806 applied, "after" is this change on
top of it. Each figure is the profiler's cumulative type-checking time
("kernel") or interpretation time ("producer", which includes the compiled
producer called from the tactic) for a file holding the single `perm_group`
goal, run with `lake lean`. Kernel times varied by up to 50% between repeated
runs.

| goal | Schreier pairs before | after | kernel before | after | producer after |
|---|---|---|---|---|---|
| order of the Rubik's cube group (6 face turns, 54 facelets) | 2226 | 671 | about 34 s | about 5 s | 1.2 s |
| order of the group adding a corner twist, an edge flip and an edge swap (9 generators) | 1365 | 932 | not measured | about 10 s | 3.7 s |
| `bench/HexPermGroupMathlib/ProofProbe/Kernel.lean`, all examples | | | 2.25 s | 1.37 s | 0.14 s |

After the first level, which keeps the six inputs, the cube certificate's
levels have 2 or 3 generators, and the last has 1. Before, the levels had 1 to
12 generators, counting inverses.

Both orders are proved within the default heartbeat limit. Before, the cube's
order needed `maxHeartbeats` raised.
