# Smaller `perm_group` certificates

The kernel checker sifts one Schreier generator per level generator and orbit
point, so its work at a level is proportional to the number of level
generators. Certificates used to copy each level's generators from
`Group.ofGenerators`, whose working arrays include every inverse. The checker
no longer requires generators closed under inverses, and the producer now
chooses, for each level, a few Schreier generators of the level above that
generate the stabilizer.

Measured on 2026-10-06, one process at a time, with HexPermGroup precompiled.
"Kernel" is the profiler's type-checking time and "producer" its interpretation
time for the `perm_group` call.

| goal | Schreier pairs before | after | kernel before | after | producer after |
|---|---|---|---|---|---|
| order of the Rubik's cube group (six face turns, 54 facelets) | 2226 | 661 | about 34 s | 4.6 s | 1.5 s |
| `bench/HexPermGroupMathlib/ProofProbe/Kernel.lean`, all examples | | | 2.25 s | 1.37 s | 0.14 s |

Generators per nontrivial level of the cube certificate, from the first level:
6, 2, 2, 2, 2, 2, 3, 2, 2, 2, 2, 3, 3, 2, 3, 3, 2, 1. Before, they were
12, 10, 12, 8, 8, 12, 8, 8, 6, 8, 8, 8, 8, 4, 7, 7, 3, 1.

The cube order proof now succeeds within the default heartbeat limit.
