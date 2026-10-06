# Smaller `perm_group` certificates

The kernel checker sifts one Schreier generator per level generator and orbit
point, so its work at a level is proportional to the number of level
generators. Certificates used to copy each level's generators from
`Group.ofGenerators`, whose working arrays include every inverse. The checker
no longer requires generators closed under inverses, a next-level generator may
be a product of Schreier generators, and the producer chooses, for each level,
two or three such products that generate the stabilizer.

Measured on 2026-10-06 on a shared machine (load average about 20), one
process at a time, with HexPermGroup precompiled. "Kernel" is the profiler's
type-checking time and "producer" its interpretation time for the `perm_group`
call. Kernel times varied by up to 50% between repeated runs; the table gives
typical values.

| goal | Schreier pairs before | after | kernel before | after | producer after |
|---|---|---|---|---|---|
| order of the Rubik's cube group (6 face turns, 54 facelets) | 2226 | 671 | about 34 s | about 5 s | 1.2 s |
| order of the group adding a corner twist, an edge flip and an edge swap (9 generators) | 1365 | 932 | not measured | about 10 s | 3.7 s |
| `bench/HexPermGroupMathlib/ProofProbe/Kernel.lean`, all examples | | | 2.25 s | 1.37 s | 0.14 s |

The cube certificate's levels have 2 or 3 generators after the first, which
keeps the six inputs. Before, the levels had 3 to 12 generators, counting
inverses.

Both orders are proved within the default heartbeat limit. Before, the cube's
order needed `maxHeartbeats` raised.
