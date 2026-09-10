# HexGraphIso against IsoGraph

Compiled-code canonical labelling, five implementations on one corpus:
all three engines pinned nauty 2.9.3 ships — dense `densenauty`,
`sparsenauty` and `Traces` — together with `Hex.GraphIso.canonicalize`
and `IsoGraph.Canon.canonical` from
[Timeroot/IsoGraph](https://github.com/Timeroot/IsoGraph) at 7cfa2370.
No tactic, kernel-replay or `native_decide` tier appears anywhere here.

## What was measured, and on what

Every implementation reads the same corpus file, so each is timed on one
labelling of one graph rather than on whatever its own family generator
emits. `scripts/bench/graphiso_corpus.py` writes 333 instances
over 20 families, out to 3072 vertices: the ones
`bench/HexGraphIso/Cactus.lean` already sweeps, together with the
families the nauty literature names as hard, described below. The corpus
is deliberately larger than any implementation can finish.

`scripts/bench/graphiso_sweep.py` runs it under a **five-second
per-instance budget**. Each implementation gets its own process per
instance, so an instance's budget is spent on the one measurement being
judged and a search that does not terminate can be killed rather than
waited on. An instance is unsolved for an implementation when the
process is killed on wall clock or when the reported per-call time is
over budget; within a family, instances are run in increasing size and
an implementation that fails one is offered no larger instance of that
family. Solved therefore means the best of the passes came in under
budget, which is the usual best-of-N reading and leaves instances within
a few percent of the ceiling able to fall either way.

The wall-clock kill scales with instance size (`--kill` plus
`--kill-per-1000`), because the drivers read the instance and make a
warm-up call before timing anything and both grow with `n`. That was not
a free choice: a flat 25-second wall was killing searches that took 4.7
seconds, and re-running every give-up boundary with a 400-second wall
showed 7 of 25 wall kills were start-up and parsing rather than search.
Those families were re-measured.

`hexgraphiso_cactus read` times the hex columns,
`scripts/bench/IsoGraphHexCompare.lean` the IsoGraph column, and
`scripts/bench/ffi/nauty_corpus_bench.c` the three C engines, one engine
per process so that the budget and the give-up rule apply to each
separately. Measurements are pinned to one automatically selected CPU. Timing within a process
is the best of several repetitions after a warm-up; results are routed
through an opaque sink and a doubled-batch scaling self-check guards
against the compiler hoisting the timed call. Measured on chungus2 (AMD
EPYC 9455) on 2026-09-07; raw data in
`reports/bench-results/hexgraphiso-comparison-chungus2.jsonl`. Each figure is
written as an SVG, which is what the manual publishes, and as a PNG
beside it for pasting into a thread.

The nauty columns come from the standalone driver, not the in-process
FFI comparator. That distinction used to matter enormously and no longer
does; see the last section.

## Result

Five implementations, timed on the same instances: the three canonical
labelling engines nauty 2.9.3 ships — dense `densenauty`, `sparsenauty`
and `Traces` — and the two Lean libraries. Inside the budget, sparse
nauty finishes 318 of the 333 instances,
Traces 308, dense nauty 307,
`IsoGraph.Canon.canonical` 296, and
`Hex.GraphIso.canonicalize` 281.

![five-way cactus](figures/hexgraphiso-comparison-cactus.svg)

### Dense nauty is the weakest of the three C engines

This matters for reading everything else, because dense nauty is the
configuration `HexGraphIso` transcribes, and so the reference every
earlier figure was drawn against. It is also the one you would least
want to use. Against it, on the instances both finish, sparse nauty is a
median **0.36×** and Traces
**0.27×** — and neither is a small
constant on the families that matter:

| family | sparse / dense | Traces / dense | Hex / best C engine | IsoGraph / best C engine |
|---|---|---|---|---|
| cfi | 0.03× | 0.02× | 455× | 34× |
| circulant-12 | 0.11× | 0.31× | 259× | 26× |
| circulant-1248 | 0.13× | 0.31× | 246× | 23× |
| cubic | 0.23× | 0.00× | 1160× | 605× |
| grid | 0.15× | 0.24× | 193× | 30× |
| hadamard | 0.62× | 0.36× | 41× | 27× |
| hypercube | 0.23× | 0.54× | 84× | 21× |
| johnson | 0.33× | 0.27× | 63× | 30× |
| kneser | 0.70× | 0.27× | 42× | 29× |
| latin | 0.42× | 0.18× | 113× | 42× |
| lattice | 0.35× | 0.26× | 68× | 21× |
| multipede | 0.06× | 0.02× | 781× | 61× |
| paley | 0.55× | 1.36× | 57× | 35× |
| projective-plane | 0.21× | 0.41× | 110× | 53× |
| random | 0.46× | 0.32× | 218× | 50× |
| shrunken-multipede | 0.12× | 1.48× | 128× | 148× |
| sparse-random | 0.21× | 0.20× | 640× | 78× |
| steiner | 0.15× | 0.04× | 270× | 154× |
| tree | 0.52× | 0.04× | 538× | 240× |
| union | 0.17× | 0.25× | 100× | 37× |

Sparse nauty is never worse than dense — same algorithm, better data
structure. Traces is dramatically better on the sparse and the
WL-hard families (0.02× on the Cai-Fürer-Immerman graphs and the
multipedes, 0.04× on trees and Steiner systems, and on random cubic
graphs it is three orders of magnitude ahead), and *worse* than dense
nauty on exactly two: Paley graphs (1.36×) and the shrunken multipedes
(1.48×). That is McKay and Piperno's own conclusion reproduced — none of
these programs wins everywhere — and it is why the table above carries a
"best C engine" column rather than a single reference.

Against that best-of-three reference, `canonicalize` is a median
**114×** and `canonical`
**35×**, reaching 1160× and 640× on the
families where Traces is at its strongest. Against dense nauty alone the
same two numbers are 29× and
7.6×. Both framings are in the table below;
the first is the honest answer to "how far from the state of the art",
the second to "how far from the algorithm this is a transcription of".

| family | n | nauty (median) | Hex `canonicalize` | IsoGraph `canonical` | IsoGraph / Hex | Hex `runColored` | IsoGraph + build | IsoGraph / Hex, matched | sparse | Traces | Hex nodes | IsoGraph nodes |
|---|---|---|---|---|---|---|---|---|---|---|---|---|
| random | 10–3072 | 0.041 ms | 70× | 16.9× | 0.24× | 41× | 19.2× | 0.61× | 0.46× | 0.32× | 1.00× | 1.00× |
| sparse-random | 32–3072 | 0.067 ms | 98× | 14.3× | 0.13× | 32× | 18.2× | 0.83× | 0.21× | 0.20× | 1.00× | 1.00× |
| paley | 13–1181 | 0.070 ms | 35× | 20.6× | 0.61× | 24× | 21.6× | 0.95× | 0.55× | 1.36× | 1.00× | 1.00× |
| grid | 9–2304 | 0.076 ms | 32× | 4.5× | 0.15× | 18× | 6.7× | 0.45× | 0.15× | 0.24× | 1.00× | 1.50× |
| hypercube | 8–2048 | 0.142 ms | 28× | 4.9× | 0.24× | 26× | 5.6× | 0.33× | 0.23× | 0.54× | 1.00× | 1.25× |
| circulant-12 | 8–3072 | 0.166 ms | 33× | 2.9× | 0.10× | 26× | 4.3× | 0.21× | 0.11× | 0.31× | 1.00× | 1.00× |
| circulant-1248 | 17–2049 | 0.242 ms | 32× | 2.9× | 0.09× | 26× | 4.4× | 0.20× | 0.13× | 0.31× | 1.00× | 1.00× |
| tree | 16–3072 | 0.252 ms | 40× | 15.1× | 0.39× | 28× | 16.3× | 0.53× | 0.52× | 0.04× | 1.00× | 1.00× |
| projective-plane | 14–1986 | 0.354 ms | 24× | 28.8× | 1.00× | 16× | 29.6× | 1.26× | 0.21× | 0.41× | 1.00× | 1.87× |
| hadamard | 16–2048 | 1.103 ms | 21× | 9.2× | 0.47× | 21× | 9.3× | 0.58× | 0.62× | 0.36× | 1.00× | 1.13× |
| union | 32–3072 | 1.173 ms | 19× | 6.8× | 0.35× | 15× | 7.1× | 0.50× | 0.17× | 0.25× | 1.00× | 1.00× |
| lattice | 25–1849 | 1.363 ms | 18× | 5.4× | 0.30× | 17× | 5.7× | 0.34× | 0.35× | 0.26× | 1.00× | 0.57× |
| johnson | 10–2016 | 4.801 ms | 17× | 7.9× | 0.47× | 16× | 8.0× | 0.52× | 0.33× | 0.27× | 1.00× | 0.99× |
| latin | 25–2025 | 4.912 ms | 24× | 8.4× | 0.38× | 21× | 9.0× | 0.46× | 0.42× | 0.18× | 1.00× | 0.53× |
| shrunken-multipede | 36–1956 | 6.107 ms | 17× | 27.8× | 1.29× | 17× | 26.8× | 1.45× | 0.12× | 1.48× | 1.00× | 1.72× |
| kneser | 10–2016 | 11.746 ms | 17× | 7.9× | 0.51× | 16× | 7.9× | 0.60× | 0.70× | 0.27× | 1.00× | 1.49× |
| cubic | 16–2048 | 22.253 ms | 9× | 1.7× | 0.28× | 9× | 1.7× | 0.29× | 0.23× | 0.00× | 1.00× | 0.03× |
| steiner | 50–1716 | 48.744 ms | 15× | 8.3× | 0.57× | 15× | 8.6× | 0.60× | 0.15× | 0.04× | 1.00× | 0.27× |
| cfi | 42–1946 | 213.814 ms | 22× | 0.8× | 0.07× | 23× | 0.8× | 0.08× | 0.03× | 0.02× | 1.00× | 1.00× |
| multipede | 66–2046 | 285.840 ms | 17× | 1.0× | 0.09× | 17× | 1.0× | 0.09× | 0.06× | 0.02× | 1.00× | 0.42× |
| **all 333** | 8–3072 | 0.659 ms | 29× | 7.6× | 0.29× | 23× | 8.3× | 0.49× | 0.36× | 0.27× | 1.00× | 1.00× |

Ratios are per-instance medians against standalone nauty 2.9.3 on the same instance; the sixth column is the head-to-head on the public entry points and the ninth the same head-to-head with the result shapes matched — `runColored` against `canonical` charged the dense-to-native conversion, neither of them building a canonical graph to hand back. The last two are search-tree sizes against nauty's: `canonicalize` transcribes nauty's search and visits exactly its nodes on every instance, so its whole distance from nauty is per-node cost, while IsoGraph is a different search and its node count is what varies.

| family | instances | nauty dense largest n solved | nauty sparse largest n solved | Traces largest n solved | Hex `canonicalize` largest n solved | IsoGraph `canonical` largest n solved |
|---|---|---|---|---|---|---|
| random | 30 | 3072 | 3072 | 3072 | 3072 | 3072 |
| sparse-random | 8 | 3072 | 3072 | 3072 | 3072 | 3072 |
| paley | 20 | 1181 | 1181 | 1181 | 1181 | 1181 |
| grid | 16 | 2304 | 2304 | 2304 | 2304 | 2304 |
| hypercube | 9 | 2048 | 2048 | 2048 | 1024 (of 2048) | 2048 |
| circulant-12 | 29 | 3072 | 3072 | 3072 | 3072 | 3072 |
| circulant-1248 | 24 | 2049 | 2049 | 2049 | 2049 | 2049 |
| tree | 9 | 3072 | 3072 | 3072 | 2048 (of 3072) | 2048 (of 3072) |
| projective-plane | 9 | 1986 | 1986 | 1986 | 1986 | 114 (of 1986) |
| hadamard | 8 | 2048 | 2048 | 2048 | 1024 (of 2048) | 2048 |
| union | 14 | 3072 | 3072 | 3072 | 2048 (of 3072) | 3072 |
| lattice | 21 | 1849 | 1849 | 1849 | 1849 | 1849 |
| johnson | 24 | 2016 | 2016 | 2016 | 2016 | 2016 |
| latin | 10 | 2025 | 2025 | 2025 | 2025 | 2025 |
| shrunken-multipede | 21 | 420 (of 1956) | 804 (of 1956) | 324 (of 1956) | 420 (of 1956) | 228 (of 1956) |
| kneser | 24 | 2016 | 2016 | 2016 | 1326 (of 2016) | 2016 |
| cubic | 12 | 1536 (of 2048) | 2048 | 2048 | 512 (of 2048) | 1536 (of 2048) |
| steiner | 8 | 1716 | 1716 | 1716 | 1334 (of 1716) | 1334 (of 1716) |
| cfi | 18 | 1946 | 1946 | 1946 | 938 (of 1946) | 1946 |
| multipede | 19 | 1056 (of 2046) | 1716 (of 2046) | 1166 (of 2046) | 506 (of 2046) | 836 (of 2046) |

Largest instance each implementation canonicalized inside the sweep's per-instance budget; a parenthesised size is the largest the corpus offered, so the family was cut off there.

![per-family scaling](figures/hexgraphiso-comparison-families.svg)

All five on one axis per family. A cross marks where an implementation
first went over budget. On the
projective planes IsoGraph stops at 114 vertices while everything else
runs to 1986. On the shrunken multipedes — the hardest family published
— everyone stops, IsoGraph first and sparse nauty last. On random cubic
graphs dense nauty stops before IsoGraph does, while Traces never breaks
a sweat.

The two Lean libraries' entry points do not return the same thing, and
that is worth a column rather than a shrug. `canonicalize` returns the
canonical *graph* and pays a dense relabelling to build it; `canonical`
returns the packed certificate, the label and the automorphisms found.
Matching the shapes — `Nauty.runColored` against `canonical` charged the
dense-to-native conversion, neither of them handing back a graph — moves
the head-to-head from **0.29×** to **0.49×**. Both are in the table: on
the entry points a user actually calls, IsoGraph is about 3.4× faster;
on equal work returned, about 2×. The gap between those two numbers is
the price of `canonicalize` returning a graph, and it is largest exactly
where the search is cheap and the relabelling is not — 0.13× against
0.83× on sparse random graphs, 0.15× against 0.45× on grids.

## The node-count column

`canonicalize` visits **exactly nauty's search-tree nodes on every
instance both finish**, every family included — the Cai-Fürer-Immerman
graphs, the multipedes, the Hadamard and projective-plane incidence
graphs. It is a transcription of the search and it behaves like one, so
its entire distance from nauty is per-node cost, and it inherits nauty's
robustness: wherever nauty's tree stays small, `canonicalize`'s does too.
That is why it reaches 1986-vertex projective planes when IsoGraph
cannot pass 114.

IsoGraph runs a different search and its node count is what varies. It
is dramatically better on random cubic graphs and on the multipedes, and
worse on the projective planes, the Kneser graphs and the shrunken
multipedes — and those are exactly where it loses.

## Scaling

Fitted exponent of time ~ n^p by least squares in log-log, over the
instances each implementation solved:

| family | n | nauty | Hex | IsoGraph |
|---|---|---|---|---|
| random | 10–3072 | 1.98 | 1.93 | 1.92 |
| sparse-random | 32–3072 | 1.94 | 1.89 | 1.64 |
| grid | 9–2304 | 1.91 | 1.85 | 1.52 |
| paley | 13–1181 | 1.97 | 1.89 | 1.91 |
| hypercube | 8–2048 | 2.22 | 2.03 | 1.66 |
| circulant-12 | 8–3072 | 2.09 | 2.07 | 1.53 |
| tree | 16–3072 | 2.59 | 2.28 | 2.40 |
| circulant-1248 | 17–2049 | 2.14 | 2.11 | 1.45 |
| projective-plane | 14–1986 | 1.76 | 1.69 | 3.60 |
| hadamard | 16–2048 | 2.51 | 2.35 | 2.25 |
| union | 32–3072 | 2.78 | 2.41 | 2.61 |
| lattice | 25–1849 | 2.44 | 2.28 | 2.15 |
| johnson | 10–2016 | 2.29 | 2.14 | 2.09 |
| latin | 25–2025 | 2.21 | 2.23 | 2.36 |
| shrunken-multipede | 36–1956 | 4.12 | 3.74 | 4.57 |
| kneser | 10–2016 | 2.58 | 2.40 | 2.35 |
| cubic | 16–2048 | 3.00 | 2.79 | 2.30 |
| steiner | 50–1716 | 2.69 | 2.61 | 2.34 |
| cfi | 42–1946 | 3.36 | 3.01 | 2.50 |
| multipede | 66–2046 | 3.58 | 3.61 | 2.52 |

`canonicalize` tracks dense nauty's exponent everywhere. Its distance from
nauty is a constant factor, not a divergence. IsoGraph's exponent is
*lower* than nauty's on the sparse families, so on circulants, grids and
hypercubes it converges to nauty's time and around a thousand vertices
draws level with it. That is an algorithmic difference, not a
measurement artifact: IsoGraph carries neighbour lists beside the dense
matrix and refines over them, which is O(m) per splitter where dense
nauty is O(n²/64), and the families where it wins are exactly the ones
with m = O(n).

## Where IsoGraph falls over

The projective planes are the sharpest case. `IsoGraph.Canon.canonical`
**does not finish PG(2,11), on 266 vertices, in twenty minutes**, where
nauty needs 0.3 ms and 23 search nodes and `canonicalize` needs 8.0 ms;
`canonicalize` goes on to PG(2,43) on 1986 vertices inside the budget,
as do all three C engines.
These planes are exactly what nauty ships the `cellfano` and `cellfano2`
invariants for, and yet plain nauty settles them at once — because the
algebraic construction has a large automorphism group and nauty's
pruning is built to exploit it. IsoGraph's is not finding it.

The shrunken multipedes are the other end of the same story: they are
constructed to be rigid, so there is no automorphism group for anyone to
exploit, and all three implementations hit the wall within a factor of
two of each other.

## Where nauty is meant to do well, and where it is not

The families above were chosen from what the nauty documentation and the
surrounding literature say, rather than invented.

The clearest map is section 10 of the [nauty user
guide](https://users.cecs.anu.edu.au/~bdm/nauty/nug29.pdf), which
introduces the vertex invariants by naming the family each one is for.
That list *is* the list of classes on which plain refinement is not
enough:

| invariant | the guide's stated target |
| --- | --- |
| `twopaths` | regular graphs with no other structure |
| `adjtriang`, `triples`, `cliques`, `indsets` | strongly regular graphs |
| `celltrips` | bipartite graphs from block designs |
| `cellquads` | Hadamard-matrix graphs, best applied at level 2 |
| `cellcliq`, `cellind` | difficult vertex-transitive graphs, at level 2 |
| `cellfano`, `cellfano2` | projective plane graphs, and Latin square graphs |
| `distances`, `refinvar` | regular but not strongly regular graphs |
| `adjacencies` | digraphs, especially not strongly connected ones |

Section 14 of the same guide gives the two constructions that turn
combinatorial equivalence into graph isomorphism, and they are the
source of two of the families here: the Hadamard-matrix graph `G(A)` of
a ±1 matrix, whose isomorphisms are the Hadamard equivalences of `A`,
and the isotopy graph of a Latin square.

McKay and Piperno's *Practical graph isomorphism, II* is explicit about
the shape of the answer: "nauty is generally the fastest for small
graphs and some easier families, while Traces is better, sometimes in
dramatic fashion, for most of the difficult graph families", and "nauty
is still preferred for mass testing of small graphs". They also name the
one class where both lose: "graphs consisting of disjoint or
minimally-overlapping components", where conauto and bliss have
component recursion and nauty and Traces do not. That is the `union`
family here.

Neuen and Schweitzer's *Benchmark Graphs for Practical Graph
Isomorphism* supplies the other half. Their summary of the state of
play: unstructured random instances "usually turn out to be among the
easiest"; the difficult instances come from combinatorial structures —
"incidence graphs of projective planes, Hadamard matrices, or Latin
squares" — and from the Cai–Fürer–Immerman construction and Miyazaki's
adaptation of it, which was written to show that nauty is exponential in
the worst case. They add the caveat that matters for reading the results
below: the *algebraic* versions of these combinatorial structures, which
are the ones you can actually generate, "automatically have a large
automorphism group", and "the practical isomorphism solvers are tuned to
finding such automorphisms and to exploit them for search space
contraction". Their own construction — multipedes, and the shrunken
multipedes — is designed to be rigid precisely so that there is no
automorphism group to exploit.

One caveat on all of this. The configuration pinned here, and
transcribed by `HexGraphIso`, is default dense nauty with
`invarproc = NULL`: no vertex invariant at all. On the families in the
table above that is exactly the configuration the user guide tells you
to change. So these numbers are not "the best nauty can do" on the hard
families; they are what the pinned configuration does, which is the
thing `HexGraphIso` is a transcription of and therefore the only
like-for-like comparison available.

## Is IsoGraph's answer right?

Checked on this corpus rather than taken on trust.

* Every instance is canonicalised, then re-canonicalised after three
  pseudo-random relabellings; all certificates agree, the returned
  labelling is a permutation in each case, and the reported certificate
  is the one `certOf` computes at that labelling.
* All 34 pair problems of `hexgraphiso_cactus dumppairs` — whose
  polarity the hex driver revalidates at run time — are settled the same
  way by comparing IsoGraph certificates. That set includes the pairs
  built to be hard: Paley(25) against the Latin square graph on 25
  vertices (same strongly-regular parameters), Paley(61) against a
  61-vertex circulant of equal degree, and K(7,2) against J(7,2).

It is also verified in the sense that matters: `IsoGraph.Canon` has no
`sorry` and no `axiom`, and `IsoGraph.instDecidableEq` — the decision
procedure that settles `G = H` for isomorphism classes — depends only on
`propext`, `Classical.choice` and `Quot.sound`. The chain is
`canonSt_bestKey` (the search's answer satisfies the `BestKey`
specification) → `canonical_cert_relabel` (the certificate is an
isomorphism invariant) → `labellingInvariant`, with completeness coming
from the certificate being the adjacency read off at a permutation.

The difference from HexGraphIso is not in whether the algorithm is
proved but in what a user gets at the goal. IsoGraph's fast path to a
closed goal is `native_decide` against that `DecidableEq`, which puts
`Lean.ofReduceBool` in the proof term; there is no kernel-checked replay
of the canonical labelling. `graph_iso` produces a proof the kernel
checks. Its other tactics (`generate_graph_iso`, `#decompose_graph`,
`compute_invariant`, `small_graphs`, `graph_sat`,
`compute_fractional_chromNum`) are a much wider surface than
HexGraphIso's, and `generate_graph_iso` does hand back a kernel-checked
isomorphism — but by decomposing the graph against an atlas of named
constructions, not by replaying the search.

## The comparator was measuring itself

`Hex.BenchOracle.Nauty` is the in-process FFI comparator every published
hex-graph-iso figure has been drawn against. Two things it did were
`O(n²)` and had nothing to do with nauty's search, and both sat inside
the caller's timed region: the adjacency was pushed into a `ByteArray`
one byte at a time, and the canonical upper triangle came back as an
`n(n-1)/2` character `String`. That marshalling was a median **3.3×** of
what was being reported as nauty's time — so every comparison drawn
through the comparator flattered both Lean implementations by that
factor.

The fix splits the call. `prepare` marshals and is meant to run once
before the timer starts; `canonPrepared` is the timed call and decodes
only the `O(n)` labelling and the node count. The canonical form comes
back packed one bit per entry instead of one byte, and stays packed:
`CanonResult.sameForm` compares two of them without allocating, and
`CanonResult.tri` renders the `0`/`1` string only for callers outside a
timed region. The comparator's own drivers were changed to match, and
the marshalling contract is now recorded in the SPEC.

Verified unchanged by the rewrite: the canonical bits agree with the
public `canon` bit for bit (`runCanonAgree16` reports the same hash it
did before), all 34 pair polarities still hold, and the search-tree node
counts are identical on every instance.

| | median overhead over the standalone driver |
|---|---|
| before | 3.28× |
| after | 1.12× |
| after, at n ≥ 500 | 1.08× |

What is left is the dense-to-bitset fill that the standalone driver
excludes from `nauty_ns`; against the conversion-inclusive column the
comparator now runs at 1.09×.

**This changes a published number.** On the 98-instance sweep behind the
released figures, the comparator's nauty column was 4.5× the standalone
driver; it is now 1.2×. The claim that `HexGraphIso` "is about 5 to 12
times slower than nauty" was measured through the inflated comparator.
Re-measured on that same corpus, `canonicalize` is **14× to 53×** slower
than nauty through the fixed comparator, and 15× to 93× against nauty's
search alone.
