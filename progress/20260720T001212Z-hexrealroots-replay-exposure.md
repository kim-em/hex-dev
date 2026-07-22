# Stage 3a: HexRealRoots kernel-replay enablement

## Accomplished

- **`@[expose]` pass** on the thirteen kernel-replay definitions across
  `HexRealRoots/{Basic,Chain,Var}.lean` (`dyadicSign`, `evalDyadic`,
  `spemStep`, `spemAux`, `spem`, `sturmChainAux`, `sturmChain`, `signVar`,
  `sturmVarAt`, `sturmVarPosInf`, `sturmVarNegInf`, `sturmCount`, `rootCount`),
  de-privatizing `spemStep`/`spemAux`/`sturmChainAux` with engine-internal
  docstring notes.
- **`HexRealRoots/Cert.lean`** (new): `beqCoeffs` + `eq_of_beqCoeffs`,
  `certTail` + `certTail_sound`, `sturmChainCertB` / `SturmChainCert` +
  `Decidable` instance, the soundness bridge `cert_imp_eq`
  (`SturmChainCert p chain → chain = sturmChain p`, proved not decided), and the
  transport lemmas `sturmCount_eq_of_cert` / `rootCount_eq_of_cert`. Also
  `orderedAdjacent` + `ordered_of_adjacent` (transitivity walk to the all-pairs
  `RealRootIsolations.ordered` shape). Mathlib-free.
- **Cached-chain refinement** in `HexRealRoots/Refine.lean`: `refine1With`,
  `refineToWithChain`; `refine1`/`refineTo` now delegate (one chain build for a
  whole `refineTo` descent). `decide` regression showing agreement with
  `refineTo`.
- **`HexRealRoots/ReplayTest.lean`** (new, plain `public import`, NO `import
  all`): five `decide`s locking the exposure (`hasSquarefreeSturmChain`,
  `sturmCount`, `rootCount`, `SturmChainCert`, `orderedAdjacent`).
- Companion touch: `HexRealRootsMathlib/Drivers.lean`'s `refine1_isolates_same`
  now `unfold`s `refine1With` too (refine1 delegates).

## Current frontier

`lake build HexRealRoots` and `lake build HexRealRootsMathlib` (8765 jobs) both
green; ReplayTest decides reduce in the kernel without `import all` (~12ms total
elaboration). No `sorry`/`axiom`/`native_decide`/`partial`.

## Next step

Stage 3b: the `isolate_roots` term elaborator in
`HexRealRootsMathlib/IsolateRoots.lean`, consuming `SturmChainCert` +
`sturmCount_eq_of_cert` / `rootCount_eq_of_cert` + `ordered_of_adjacent` for the
replay-shape emission.

## Blockers

None on the Lean side. The full `lake build` reports native dynlib failures
(`HexBasic:shared`, `HexGF2.Basic:dynlib`) from a broken elan/nix linker wrapper
in this environment (`ld-wrapper.sh: No such file or directory`) — environmental,
unrelated to these Lean-only changes.
