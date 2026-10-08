# Faster generating-set search in `Kernel.certify`

`Kernel.certify` chooses, for each certificate level, a few products of
Schreier generators that generate the point stabilizer. It used to accept a
sampled set by computing the order of the group it generates with a complete
chain, from scratch for each set. Skipping those order computations (which
yields invalid certificates, so only as a timing experiment) cut `certify` on
the Rubik's cube group from 361 ms to 44 ms, showing that they were nearly all
of its time.

A sampled set always generates a subgroup of the stabilizer, whose order is
known, so a lower bound on the subgroup's order suffices: `reachesOrder` sifts
pseudo-random elements of the subgroup into a partial stabilizer chain, whose
orbit-size product never exceeds the subgroup's order, and accepts the set once
that product reaches the stabilizer's order.

Exploratory observations, not measurements under the paired protocol of
`SPEC/benchmarking.md`: best of five runs of `Kernel.certify S` in one compiled
executable on 2026-10-08, on a shared 96-core machine (load average about 9 to
12), with the generators of `reports/data/perm-group-gap-comparison/groups.json`.
"Before" is `main` at 5e55fa10d.

| group | degree | before | after |
|---|---|---|---|
| M11 | 11 | 0.72 ms | 0.54 ms |
| M24 | 24 | 4.4 ms | 2.5 ms |
| J2 | 100 | 13 ms | 11 ms |
| HS | 100 | 24 ms | 18 ms |
| Rubik's cube | 54 | 361 ms | 59 ms |
| cube reassembly | 54 | 1382 ms | 134 ms |
| McL | 275 | 112 ms | 90 ms |
| Co3 | 276 | 261 ms | 160 ms |

Kernel checking of the resulting certificates, a single run each with
`lake lean`: M24 0.34 s, the cube 4.4 s and the reassembly group 8.0 s, within
the run-to-run variation of the previous certificates' 0.30 s, 4.5 s and 8.4 s.
