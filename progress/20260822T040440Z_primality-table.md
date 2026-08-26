# hex-primality: scaffolding and the committed table at 10^4

## Accomplished

- Scaffolded `HexPrimality`: `lean_lib` entry, umbrella, `libraries.yml`
  entry (`deps: [HexArith, HexBasic]`, active), `HEX_LIB_TARGETS`
  addition, and the SPEC moved to its co-located home
  `HexPrimality/SPEC/hex-primality.md` with every cross-reference
  updated.
- `HexPrimality/Table.lean`: the committed 1229-entry `primeTable` at
  `primeTableBound = 10000`, `primeTable_sorted` via a structural
  adjacent-ascent checker, `isTablePrime` by fuel-bounded binary search
  with soundness and completeness (`isTablePrime_iff`), table soundness
  `mem_primeTable_prime` (one kernel-replayed `isPrimeTrial` sweep) and
  completeness `mem_primeTable_of_prime` (five kernel-replayed balanced
  `coverOk` chunks of span 2048), and `primesIn` with `mem_primesIn`.
- Module elaborates in ~82 s, dominated by the kernel decides; within
  the few-minutes budget rule. `check_dag.py` and
  `conformance_targets.py --check` pass.

## Current frontier

Table statements are written sieve-agnostically: the planned
kernel-reducible sieve (SPEC "Initial segments") replaces the
verification internals (`coverOk`, `primeTable_all_trial`) without
touching any public statement.

## Next step

The `hotPathCandidates` migration in hex-berlekamp-zassenhaus onto a
proof-carrying view of `primeTable` restricted to `[3, 500]`.

## Blockers

Stacked on the milestone 0 hex-arith PR (kernel-facing `powModNat` and
the `isPrimeTrial`-backed `Decidable` instance).
