# HexPermGroup against GAP

Exploratory observations, not measurements under the paired protocol of
`SPEC/benchmarking.md`, taken on 2026-10-06 on a shared 96-core machine (load
average between about 7 and 30 during the runs), with GAP 4.15.1 from nixpkgs
and Lean v4.35.0-rc3. Only the minimum of each set of runs was recorded. The
scripts, goal files, recorded outputs and exact commands are in
`reports/data/perm-group-gap-comparison/`.
The Hex code is `main` at 983cb7c37 with
https://github.com/kim-em/hex-dev/pull/10814 applied and HexPermGroup
precompiled. Generators are the ATLAS permutation generators recorded in
`reports/bench-results/perm-group-mathlib-free.json`, and the six face turns of
the Rubik's cube on 54 stickers, with a corner twist, an edge flip and an edge
exchange added for the reassembly group.

- GAP: `Size(Group(gens))` on a fresh group, best of five. Passing
  `StabChain(G, rec(random := 1000))` first gave the same times.
- Hex compiled: `(Group.ofGenerators S).order` and `Kernel.certify S` in a
  compiled executable, best of five.
- Kernel: the profiler's type-checking time for one
  `example : HasOrder #[…] N := by perm_group` on `Perm.ofImages` generators, a
  single run.

| group | degree | order | GAP | `ofGenerators` | `Kernel.certify` | kernel check |
|---|---|---|---|---|---|---|
| M11 | 11 | 7920 | 0.13 ms | 0.57 ms | 0.93 ms | 53 ms |
| M12 | 12 | 95040 | 0.15 ms | 1.2 ms | 1.7 ms | 73 ms |
| M22 | 22 | 443520 | 0.22 ms | 2.6 ms | 3.8 ms | 0.17 s |
| M23 | 23 | 10200960 | 0.29 ms | 4.8 ms | 6.8 ms | 0.24 s |
| M24 | 24 | 244823040 | 0.43 ms | 7.1 ms | 8.4 ms | 0.30 s |
| J2 | 100 | 604800 | 0.44 ms | 51 ms | 49 ms | 1.7 s |
| HS | 100 | 44352000 | 0.68 ms | 116 ms | 115 ms | 2.6 s |
| Rubik's cube | 54 | 43252003274489856000 | 2.6 ms | 0.64 s | 1.0 s | 4.1 s |
| cube reassembly | 54 | 519024039293878272000 | 4.0 ms | 1.5 s | 3.6 s | 7.8 s |
| McL | 275 | 898128000 | 2.2 ms | 1.1 s | 0.96 s | 21 s |
| Co3 | 276 | 495766656000 | 3.2 ms | 2.6 s | 3.4 s | 35 s |

Compiled construction is 4 to 20 times slower than GAP on the Mathieu groups
and 250 to 800 times slower on the cube, McL and Co3. Kernel checking takes 2 to 60
times as long as compiled certification.

The `Co3` proof used to exceed the default heartbeat limit, because the kernel's
work on its auxiliary declarations was charged to the tactic; since the tactic
checks them on separate threads it succeeds within the default limit. Its kernel
time is from a later successful run with that change (`hex-kernel-co3.txt`); the
run recorded in `hex-kernel.txt` spent 26.8 seconds in the kernel before failing
on heartbeats.