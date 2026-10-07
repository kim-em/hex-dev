# Data for `reports/20261006-perm-group-gap-comparison.md`

Exploratory observations from 2026-10-06, not measurements under the paired
protocol of `SPEC/benchmarking.md`. Only the minimum of each set of runs was
recorded; individual samples were not retained.

- `groups.json`: the generators, as 0-based image lists, of each group.
- `cmp.g`: the GAP 4.15.1 script, run as `gap -q cmp.g` from `nix shell
  nixpkgs#gap`. It prints, for each group, the best of five times of
  `Size(Group(gens))` on a fresh group, and of the same after
  `StabChain(G, rec(random := 1000))`. Output: `gap-results.txt`.
- `CmpTime.lean.txt`: a compiled executable (registered locally as a
  `lean_exe` with `srcDir := "bench"`, not committed) printing the best of five
  times, in microseconds, of `(Group.ofGenerators S).order` and of
  `Kernel.certify S`. Output: `hex-compiled.txt`.
- `K_*.lean.txt`: one `example : HasOrder #[…] N := by perm_group` per group, on
  `Perm.ofImages` generators, with `set_option profiler true`. Each was run once
  with `lake lean` in a checkout with HexPermGroup precompiled, under a
  `systemd-run --user --scope -p MemoryMax=8G -p MemorySwapMax=0` limit, one at a
  time. `hex-kernel.txt` lists the profiler's cumulative type-checking time
  ("kernel"); its "producer" column is the profiler's interpretation time, which
  does not include the compiled producer and is not used in the report.

The Hex code was `main` at 983cb7c37 with
https://github.com/kim-em/hex-dev/pull/10814 applied.
