# HexGF2 module migration — corrected diagnosis + partial migration

## The earlier misdiagnosis (now corrected)

The claim that HexGF2 was blocked by a fundamental `precompileModules` +
`@[expose]` LCNF-codegen incompatibility was WRONG. Proof: HexArith and
HexModArith are both `precompileModules := true`, already migrated with
`@[expose]` defs, and green on main. The `"Failed to find LCNF signature for
ofWords"` / `"declaration has metavariables"` errors were a CASCADE from
exposing defs whose bodies reference `private` helpers (`trimTrailingZeroWordsList`,
`highestSetBitBelow?`) — promoting those helpers clears the cascade. Codex
concurred.

## What migrates green (7 of 10 files)

`Basic`, `Clmul`, `Multiply`, `Euclid`, `Irreducibility`, `Field`,
`RabinSoundness` build green as modules. Pattern: bulk `@[expose]` on the
computational defs + promote referenced private helpers; `public meta import
Std.Tactic.BVDecide` in Clmul (for `bv_decide`); expose the `Zero`/`OfNat`
instances and `natCast` to make `(0 : GF2nPoly)` reduce (the `Zero.toOfNat0`
vs custom `instOfNat` diamond, defeq once `natCast` is exposed); `degree?_one`/
`degree_one` proved via `degree?_eq_some_of_coeff...` + `Nat.testBit` (the
UInt64 bit-search does not reduce by `rfl`); a few `leadingCoeff 0`/structure-zero
`rfl`s rewritten to `simp`.

## The genuine remaining blocker (narrow)

`CommonIrreducibility` has 7 `decide`-based irreducibility-certificate proofs
(`aesCert_check`, GF(2^16), GHASH, ...). Under the module system, `decide`
cannot kernel-reduce `checkIrreducibilityCertificate aesModulus aesCert` to a
Bool even with the ENTIRE HexGF2 surface (all defs + DecidableEq/BEq/Zero/OfNat
instances) exposed. The reduction "gets stuck" (opacity, not a heartbeat/recursion
limit — confirmed: bumping `maxRecDepth`/`maxHeartbeats` does not help). The
stuck computation runs the `@[extern] clmul` / 64-iteration UInt64 bit-folds,
which legacy `decide` reduces but module `decide` does not. This is the same
`decide`-heavy class as HexConway. Resolving it needs either a kernel/toolchain
answer for `decide` over `@[extern]`/UInt64 under modules, or rewriting these
certificate proofs from `decide` to explicit lemmas (large effort). `Smoke` and
`CrossCheck` are untested behind it.

## Status

This is WIP on branch `module-migration-gf2` (not PR'd; not green). The
corrected, finishable part is the 7 files above; the holdout is the
`decide`-certificate proofs.

## UPDATE: exact stuck point traced (Array.ofFn)

Bisected the failing `decide` certificate proofs conjunct-by-conjunct and then
sub-expression-by-sub-expression:

- PASS under `decide`: raw UInt64 bit ops (`((5:UInt64) >>> 1) &&& 1 != 0`),
  `lowerMask`, `monomial`, `ofWords`, `normalizeWords`, `Array.replicate`.
- FAIL under `decide`: `aesModulus.degree`, `aesModulus.words`,
  `monomial 8 + ofUInt64 27` (GF2Poly `+`), `xorWords #[256] #[27]`, and the
  minimal `Array.ofFn (fun _ : Fin 1 => (0:UInt64))`.

Root cause: `GF2Poly.xorWords xs ys := Array.ofFn (fun i : Fin (max xs.size
ys.size) => xs.getD i 0 ^^^ ys.getD i 0)`. **`Array.ofFn` does not reduce under
`decide` in the module build** (its proof-carrying `Fin`/`Eq.rec` construction
is the opaque step). Every certificate computation touches GF2Poly `+`, so all
7 proofs get stuck here. This builds under legacy `decide`, so it is a
module-vs-legacy reduction difference, not a logic error.

`decide +kernel` does NOT rescue it: the tactic still runs an elaborator-side
evaluation to determine the boolean before handing the final defeq to the
kernel, and that pre-eval is exactly what's stuck (identical error).

### Fix options
1. Rewrite `xorWords` to a `decide`-reducible construction (avoid `Array.ofFn`;
   e.g. a structural recursion / List-based build), keeping `xorWords_size` etc.
   This is targeted and would unblock all 7 cert proofs (and likely the same
   pattern in HexConway). Risk: it is the executable add hot-path with dependent
   correctness lemmas.
2. Treat as a toolchain issue: `Array.ofFn` reducibility under `decide` in the
   module system (raise upstream).
