# HexGraphIso nauty campaign report

The extended conformance campaign of
[HexGraphIso/SPEC/hex-graph-iso.md](../HexGraphIso/SPEC/hex-graph-iso.md#conformance)
is streamed to the external nauty oracle rather than committed as a fixture.
It runs locally or on the scheduled profile, not in merge CI. This report is
the recorded result of that run.

## Run

| item | value |
|---|---|
| machine | `chungus2`, AMD EPYC 9455 (96 threads), Linux |
| date | 2026-09-08 |
| monorepo commit | `7a536cad3b41` (`issue-10043`, structured public search) |
| Lean toolchain | `leanprover/lean4:v4.34.0-rc2` |
| comparator | nauty 2.9.3, vendored in `vendor/nauty-2.9.3` |
| shim | cached binary keyed by the pinned shim and vendored source contents, compiled with `-O2` |
| Python | 3.14.6 |

Reproduction, from the monorepo root:

```
lake build hexgraphiso_emit_campaign
.lake/build/bin/hexgraphiso_emit_campaign | python3 scripts/oracle/graphiso_nauty.py
```

## Cases

32,798 campaign cases, from `conformance/HexGraphIso/EmitCampaign.lean`:

| group | cases |
|---|---|
| all labelled graphs at `n = 6` (`campaign/n6/m0` .. `m32767`) | 32,768 |
| deterministic families (Paley, hypercube, grid, Johnson, Kneser, triangular, complete multipartite, repeated components, circulant, Latin square) | 21 |
| pseudo-random `G(n, 1/2)` and onto 3-colourings at `n = 12, 14, 16` from both SplitMix64 corpus seeds | 9 |

Vertex counts range from 6 to 255, the comparator's dense bound. The large
rungs (`paley113`, `circulant193`, `circulant255`, `hypercube7`, `grid12`,
`kneser15-2`, `johnson15-2`, `latin13`) are the sizes that
[the second cactus series break](../HexGraphIso/SPEC/hex-graph-iso.md#benchmarks)
routes to the campaign instead of the committed fixture.

## What was compared

The emitter records the public `canonicalize` answer, so the campaign pins the
released surface: the label, the canonical upper-triangle bits, and the
visited-node count of the structured search.

`scripts/oracle/graphiso_nauty.py` then rebuilds each original graph and
colouring from the record, runs the pinned dense-nauty configuration through
`scripts/oracle/graphiso_nauty_shim.c` compiled against the vendored source,
and independently computes and compares:

- the ordered colour-cell sizes;
- the canonical upper-triangle adjacency bits;
- every entry of `canonlab`;
- the visited-node counter.

The Lean answer is never canonicalized before comparison, so an isomorphic but
non-canonical representative would fail.

## Result

All 32,798 campaign cases agree exactly with nauty 2.9.3. No mismatch or
counter disagreement occurred. Wall-clock observations with the cached shim:

| leg | elapsed |
|---|---:|
| campaign emission | 1.273 s |
| oracle comparison of the emitted records | 0.812 s |
| twin over fixtures, automorphisms and campaign | 1.684 s |

The 6,233 freshly emitted fixture records are byte-identical to
`conformance-fixtures/HexGraphIso/graphiso.jsonl`. All pass the nauty oracle,
including 205 automorphism-group records. Fixture emission took 0.121 s and
oracle comparison 0.133 s. These are local run observations, not the cactus
performance measurements.

The twin agrees over 6,028 canonical fixture cases, 205 automorphism cases,
and 32,798 campaign cases. It checks labels, rows, all seven statistics,
accepted-generator order, best codes, orbit partitions, and normal root
unwind. Both wrappers now use the same engine; independent comparison comes
from the external nauty oracle and the committed fixture.

Three negative controls confirm the comparison legs are live. Perturbing one
canonical adjacency bit of `campaign/circulant255`, incrementing the visited-node
count of `campaign/n6/m12345`, and transposing two `canonLab` entries of
`campaign/g16-col3-seed1` each make the oracle exit non-zero and name the
expected case and field.
