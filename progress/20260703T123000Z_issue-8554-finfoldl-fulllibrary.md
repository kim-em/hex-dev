# Issue #8554: List.finRange folds → Fin.foldl, full-library migration

## Accomplished

Full-library migration of `(List.finRange n).foldl` index-folds to core
`Fin.foldl` (and `.reverse.foldl` → `Fin.foldr`), across the scoped libraries
(HexMatrix, HexDeterminant, HexGramSchmidt, HexLLL; HexBareiss had none).
Commits on `issue-8554`:

1. `fc06bfb6` — Laplace public statements → `Fin.foldl` (reader-facing), manual repoint.
2. `be3404f1` — HexLLL executable defs native: `sizeReduce` (`Fin.foldr` for the
   reverse sweep), `sizeReduceColumn`, `swapStep`, `potential`, `maxDiagBits`;
   `HexLLLMathlib/Reducer.lean` proofs ported.
3. `850f3343` — `Vector.dotProduct` → native `Fin.foldl` + graph-wide proof bridges.
4. `f91070c3` — HexDeterminant def bodies (`detProduct`, `cofactorRowPairing`,
   column-sum/choice, Cauchy-Binet coeffs) and reader-facing statements → `Fin.foldl`.
5. `a2535a92` — **Forced correction**: `dotProduct` reverted to a `List.finRange`
   reference form + `Fin.foldl` `dotProductImpl` + `@[csimp]`, because `Fin.foldl`
   uses well-founded recursion and does NOT kernel-reduce, so a native form broke
   the `Matrix.memLattice` `by decide` conformance proofs. Redundant native-form
   bridges removed graph-wide.
6. `3dddb427` — HexGramSchmidt def bodies (`prefixCombination`,
   `gramSchmidtNormProduct`, `prefixSumByRow`) and reader-facing statements → `Fin.foldl`.

## Key finding (kernel-reducibility)

`Fin.foldl`/`Fin.foldr` are well-founded recursions → the kernel cannot reduce
them → any def reached by a `by decide` PROOF breaks. `#guard` COMMANDS are fine
(elaborator whnf reduces them). Rule applied: def bodies reached by `by decide`
(only `dotProduct`, via `memLattice`) keep a `List.finRange` reference form with a
`@[csimp]` `Fin.foldl` compiled form; everything else goes native. Enumerated-list
folds (`permutationVectors`, `columnTupleVectors`) stay `List.foldl`. Proof-internal
`List.finRange` folds remain as bridge targets (they are the target of
`Fin.foldl_eq_finRange_foldl`; not allocations).

## Verification

- Full `lake build`: green (4085 jobs).
- `lake build HexConformance`: green (339 jobs) — incl. the `memLattice` `by decide`
  proofs and all `#guard`s.
- LLL bench (`runSizeReduceChecksum`): final 70.9/85.3/95.9 µs vs baseline
  73.3/87.5/96.8 µs — no regression (marginally faster), verdict consistent.
- No `sorry`/`axiom`/`native_decide`; only the one intended `@[csimp]` for `dotProduct`.

## Next step

Push, confirm CI (build + conformance + bench verify). Reader-facing statement
readability could be pushed further into the `getElem_*` bridge-interface lemmas
if desired, but those are intentionally kept in `List.finRange` form for their
downstream consumers.

## Blockers

None.
