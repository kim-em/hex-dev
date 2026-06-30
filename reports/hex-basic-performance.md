# HexBasic Performance Report

## Bench Targets

None. `HexBasic` is a proof-infrastructure library: it provides the shared
`List.foldl` algebra (`HexBasic.Fold`), the `Batteries` list-lemma
reproductions (`HexBasic.ListShim`), and the `Vector.modify` update helper.
None of these add an executable or runtime surface of their own — they are
lemmas and a thin `Array.modify` wrapper consumed by the other libraries,
whose own benches already exercise the generated code.

There is therefore nothing to benchmark at this layer, and `HexBasic` declares
no `phase4` input families or comparators in `libraries.yml`. The library is
marked fully done because its content is complete and stable; its only
forward motion is deletion, as individual lemmas migrate up to lean4.

## Verdicts

Not applicable: no Phase-4 bench targets exist for this library. Runtime
performance of the helpers is covered transitively by the benches of the
consuming libraries (`HexMatrix`, `HexRowReduce`, `HexGF2`, `HexPolyZ`, …).
