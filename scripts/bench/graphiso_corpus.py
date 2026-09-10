#!/usr/bin/env python3
"""Generate a shared graph corpus for the cross-implementation sweeps.

Writes the plain-text corpus format that `hexgraphiso_cactus read`, the
IsoGraph driver and `nauty_corpus_bench` all consume: repeated blocks of

    G <name> <family> <n>
    <n lines of n 0/1 characters>

The families are the ones `bench/HexGraphIso/Cactus.lean` sweeps, in the
same constructions, extended to larger vertex counts. Generating them
here rather than in each library is what lets every implementation be
timed on one labelling of one graph.

    python3 scripts/bench/graphiso_corpus.py --max-n 1024 > corpus.txt
"""
from __future__ import annotations

import argparse
import json
import sys
from itertools import combinations
from pathlib import Path


def circulant(n: int, offsets: list[int]) -> list[list[int]]:
    m = [[0] * n for _ in range(n)]
    for i in range(n):
        for d in offsets:
            for j in ((i + d) % n, (i - d) % n):
                if i != j:
                    m[i][j] = m[j][i] = 1
    return m


def grid(a: int, b: int) -> list[list[int]]:
    n = a * b
    m = [[0] * n for _ in range(n)]
    for r in range(a):
        for c in range(b):
            v = r * b + c
            if c + 1 < b:
                m[v][v + 1] = m[v + 1][v] = 1
            if r + 1 < a:
                m[v][v + b] = m[v + b][v] = 1
    return m


def hypercube(d: int) -> list[list[int]]:
    n = 1 << d
    m = [[0] * n for _ in range(n)]
    for v in range(n):
        for b in range(d):
            w = v ^ (1 << b)
            m[v][w] = m[w][v] = 1
    return m


def _subsets(mm: int, k: int) -> list[frozenset[int]]:
    return [frozenset(c) for c in combinations(range(mm), k)]


def kneser(mm: int, k: int) -> list[list[int]]:
    sets = _subsets(mm, k)
    n = len(sets)
    m = [[0] * n for _ in range(n)]
    for i in range(n):
        for j in range(i + 1, n):
            if not sets[i] & sets[j]:
                m[i][j] = m[j][i] = 1
    return m


def johnson(mm: int, k: int) -> list[list[int]]:
    sets = _subsets(mm, k)
    n = len(sets)
    m = [[0] * n for _ in range(n)]
    for i in range(n):
        for j in range(i + 1, n):
            if len(sets[i] & sets[j]) == k - 1:
                m[i][j] = m[j][i] = 1
    return m


def paley(q: int) -> list[list[int]]:
    sq = {(i * i) % q for i in range(q)}
    m = [[0] * q for _ in range(q)]
    for i in range(q):
        for j in range(i + 1, q):
            if (i - j) % q in sq:
                m[i][j] = m[j][i] = 1
    return m


def latin_square(k: int) -> list[list[int]]:
    """The Latin square graph of the cyclic square: cells of a k x k grid,
    adjacent when they share a row, a column, or a symbol (i + j mod k)."""
    n = k * k
    m = [[0] * n for _ in range(n)]
    for v in range(n):
        r1, c1 = divmod(v, k)
        for w in range(v + 1, n):
            r2, c2 = divmod(w, k)
            if r1 == r2 or c1 == c2 or (r1 + c1) % k == (r2 + c2) % k:
                m[v][w] = m[w][v] = 1
    return m


class Rng:
    """xorshift64*, so the corpus is reproducible from the seed alone."""

    def __init__(self, seed: int) -> None:
        self.s = (seed ^ 88172645463325252) & 0xFFFFFFFFFFFFFFFF

    def next(self) -> int:
        s = self.s
        s ^= (s << 13) & 0xFFFFFFFFFFFFFFFF
        s ^= s >> 7
        s ^= (s << 17) & 0xFFFFFFFFFFFFFFFF
        self.s = s
        return (s * 2685821657736338717) & 0xFFFFFFFFFFFFFFFF

    def below(self, m: int) -> int:
        return (self.next() >> 11) % max(m, 1)

    def perm(self, k: int) -> list[int]:
        a = list(range(k))
        for i in range(k - 1, 0, -1):
            j = self.below(i + 1)
            a[i], a[j] = a[j], a[i]
        return a


def gnp(n: int, seed: int, num: int = 1, den: int = 2) -> list[list[int]]:
    """G(n, num/den) from a deterministic xorshift64* stream."""
    r = Rng(seed)
    m = [[0] * n for _ in range(n)]
    for i in range(n):
        for j in range(i + 1, n):
            if r.below(den) < num:
                m[i][j] = m[j][i] = 1
    return m


def random_regular(n: int, d: int, seed: int) -> list[list[int]]:
    """A random d-regular graph by repeated pairing, retrying on collision."""
    r = Rng(seed)
    for _ in range(2000):
        stubs = [v for v in range(n) for _ in range(d)]
        pi = r.perm(len(stubs))
        perm = [0] * len(stubs)
        for i, p in enumerate(pi):
            perm[p] = stubs[i]
        m = [[0] * n for _ in range(n)]
        ok = True
        for i in range(0, len(perm) - 1, 2):
            a, b = perm[i], perm[i + 1]
            if a == b or m[a][b]:
                ok = False
                break
            m[a][b] = m[b][a] = 1
        if ok:
            return m
    raise SystemExit(f"random_regular({n}, {d}) did not terminate")


def random_tree(n: int, seed: int) -> list[list[int]]:
    """A uniformly random labelled tree, from a random Prufer sequence."""
    r = Rng(seed)
    m = [[0] * n for _ in range(n)]
    if n <= 1:
        return m
    code = [r.below(n) for _ in range(n - 2)]
    deg = [1] * n
    for c in code:
        deg[c] += 1
    leaves = sorted(v for v in range(n) if deg[v] == 1)
    import heapq
    heapq.heapify(leaves)
    for c in code:
        leaf = heapq.heappop(leaves)
        m[leaf][c] = m[c][leaf] = 1
        deg[c] -= 1
        if deg[c] == 1:
            heapq.heappush(leaves, c)
    a, b = heapq.heappop(leaves), heapq.heappop(leaves)
    m[a][b] = m[b][a] = 1
    return m


def lattice(k: int) -> list[list[int]]:
    """The rook's graph K_k [] K_k on k^2 cells: adjacent when they share a
    row or a column. A strongly regular graph, and the family behind the
    Traces "Grids" performance page."""
    n = k * k
    m = [[0] * n for _ in range(n)]
    for v in range(n):
        for w in range(v + 1, n):
            if v // k == w // k or v % k == w % k:
                m[v][w] = m[w][v] = 1
    return m


def _bipartite_to_matrix(left: int, right: int,
                         inc: list[list[int]]) -> list[list[int]]:
    """The incidence graph of a set system: `left` point vertices then
    `right` block vertices, joined by containment."""
    n = left + right
    m = [[0] * n for _ in range(n)]
    for b, pts in enumerate(inc):
        for pt in pts:
            m[pt][left + b] = m[left + b][pt] = 1
    return m


def hadamard(k: int) -> list[list[int]]:
    """The Hadamard-matrix graph G(A) of the Sylvester matrix of order 2^k,
    as in section 14 of the nauty user guide: vertices v_i, v_i', w_j, w_j',
    with {v_i, w_j} and {v_i', w_j'} when a_ij = 1 and {v_i, w_j'},
    {v_i', w_j} when a_ij = -1. Isomorphism of G(A) is Hadamard equivalence
    of A. `cellquads` at level 2 is the invariant nauty documents for this
    family."""
    q = 1 << k
    # Sylvester: a_ij = (-1)^popcount(i & j)
    n = 4 * q
    m = [[0] * n for _ in range(n)]

    def link(a: int, b: int) -> None:
        m[a][b] = m[b][a] = 1

    for i in range(q):
        for j in range(q):
            plus = bin(i & j).count("1") % 2 == 0
            vi, vi2, wj, wj2 = i, q + i, 2 * q + j, 3 * q + j
            if plus:
                link(vi, wj)
                link(vi2, wj2)
            else:
                link(vi, wj2)
                link(vi2, wj)
    return m


def projective_plane(q: int) -> list[list[int]]:
    """The incidence graph of PG(2, q) for prime q: 1-dimensional against
    2-dimensional subspaces of F_q^3, on 2(q^2+q+1) vertices. The family
    nauty's `cellfano`/`cellfano2` invariants are written for."""
    pts = []
    for x, y, z in [(1, b, c) for b in range(q) for c in range(q)] + \
                   [(0, 1, c) for c in range(q)] + [(0, 0, 1)]:
        pts.append((x, y, z))
    index = {p: i for i, p in enumerate(pts)}
    assert len(pts) == q * q + q + 1
    # a line is the set of points orthogonal to a fixed point of the dual
    lines = []
    for a in pts:
        lines.append([index[p] for p in pts
                      if (a[0] * p[0] + a[1] * p[1] + a[2] * p[2]) % q == 0])
    return _bipartite_to_matrix(len(pts), len(lines), lines)


def steiner_triple(mm: int) -> list[list[int]]:
    """The point-block incidence graph of the Bose Steiner triple system on
    3m points, m odd: the idempotent commutative quasigroup x*y =
    (x+y)(m+1)/2 on Z_m. Block-design incidence graphs are what nauty's
    `celltrips` and `indsets` invariants are aimed at."""
    assert mm % 2 == 1
    half = (mm + 1) // 2
    star = lambda x, y: ((x + y) * half) % mm
    pt = lambda x, i: 3 * x + i
    blocks = [[pt(x, 0), pt(x, 1), pt(x, 2)] for x in range(mm)]
    for x in range(mm):
        for y in range(x + 1, mm):
            for i in range(3):
                blocks.append([pt(x, i), pt(y, i), pt(star(x, y), (i + 1) % 3)])
    return _bipartite_to_matrix(3 * mm, len(blocks), blocks)


def union(k: int, base: list[list[int]]) -> list[list[int]]:
    """`k` disjoint copies. McKay and Piperno single this shape out as the
    one class where nauty and Traces are beaten, having no component
    recursion where bliss and conauto do."""
    t = len(base)
    n = k * t
    m = [[0] * n for _ in range(n)]
    for c in range(k):
        for i in range(t):
            for j in range(t):
                m[c * t + i][c * t + j] = base[i][j]
    return m


def _cfi_gadget_graph(vs: int, ws: int,
                      nbrs: list[list[int]], bypass: bool) -> list[list[int]]:
    """R(B) for a bipartite B = (V, W, E) with every v in V of degree 3:
    each v becomes the four middle vertices m_i(v), i in {0,1}^3 of even
    weight, each w becomes the pair a(w), b(w), and m_i(v) meets a(w_j) when
    i_j = 0 and b(w_j) otherwise (Neuen and Schweitzer, Algorithm 2).

    With `bypass`, the a and b vertices are removed and their neighbours
    joined directly, which is the vertex-count reduction of their section
    4.2."""
    evens = [i for i in range(8) if bin(i).count("1") % 2 == 0]
    mid = {}
    for v in range(vs):
        for t, i in enumerate(evens):
            mid[(v, i)] = 4 * v + t
    outer_a = {w: 4 * vs + 2 * w for w in range(ws)}
    outer_b = {w: 4 * vs + 2 * w + 1 for w in range(ws)}
    n = 4 * vs + 2 * ws
    m = [[0] * n for _ in range(n)]
    for v in range(vs):
        assert len(nbrs[v]) == 3, "R(B) needs every v in V of degree 3"
        for j, w in enumerate(nbrs[v]):
            for i in evens:
                outer = outer_a[w] if (i >> j) & 1 == 0 else outer_b[w]
                u = mid[(v, i)]
                m[u][outer] = m[outer][u] = 1
    if not bypass:
        return m
    keep = list(range(4 * vs))
    for w in range(ws):
        for outer in (outer_a[w], outer_b[w]):
            adj = [u for u in keep if m[outer][u]]
            for x in range(len(adj)):
                for y in range(x + 1, len(adj)):
                    m[adj[x]][adj[y]] = m[adj[y]][adj[x]] = 1
    return [[m[i][j] for j in keep] for i in keep]


def _cycle_with_diagonals(n: int) -> list[tuple[int, int]]:
    """G_n: the 2n-cycle with the n main diagonals, 3-regular on 2n
    vertices."""
    edges = [(i, (i + 1) % (2 * n)) for i in range(2 * n)]
    edges += [(i, i + n) for i in range(n)]
    return [(min(a, b), max(a, b)) for a, b in edges]


def cfi(n: int, twisted: bool = False) -> list[list[int]]:
    """The Cai-Furer-Immerman graph over G_n, the construction that defeats
    one-dimensional refinement: 14n vertices. `twisted` swaps a(w) and b(w)
    at one edge, giving the non-isomorphic partner."""
    edges = _cycle_with_diagonals(n)
    eidx = {e: i for i, e in enumerate(edges)}
    nbrs = [[] for _ in range(2 * n)]
    for e in edges:
        nbrs[e[0]].append(eidx[e])
        nbrs[e[1]].append(eidx[e])
    m = _cfi_gadget_graph(2 * n, len(edges), nbrs, bypass=False)
    if twisted:
        a, b = 4 * (2 * n), 4 * (2 * n) + 1
        for u in range(len(m)):
            m[u][a], m[u][b] = m[u][b], m[u][a]
        for u in range(len(m)):
            m[a][u], m[b][u] = m[b][u], m[a][u]
    return m


def _f2_pivot_rows(rows: list[int], ncols: int) -> list[int]:
    """Indices of a maximal F2-independent set of rows, by elimination."""
    pivots: dict[int, int] = {}
    chosen = []
    for idx, r in enumerate(rows):
        cur = r
        for col in sorted(pivots, reverse=True):
            if (cur >> col) & 1:
                cur ^= pivots[col]
        if cur:
            pivots[cur.bit_length() - 1] = cur
            chosen.append(idx)
            if len(chosen) == ncols:
                break
    return chosen


def _rigid_odd_base(n: int, seed: int):
    """B(G_n, sigma): V = V(G_n) x {0,1}, all of degree 3; W = E(G_n).
    Returned only when it is odd, which by Lemma 4.1 is the F2-rank of the
    incidence matrix reaching |W|."""
    edges = _cycle_with_diagonals(n)
    eidx = {e: i for i, e in enumerate(edges)}
    r = Rng(seed)
    for _ in range(64):
        sigma = r.perm(len(edges))
        nbrs = [[] for _ in range(4 * n)]
        for e in edges:
            for v in e:
                nbrs[v].append(eidx[e])
        for i, e in enumerate(edges):
            for v in edges[sigma[i]]:
                nbrs[2 * n + v].append(i)
        if any(len(x) != 3 for x in nbrs):
            continue
        rows = [sum(1 << w for w in x) for x in nbrs]
        chosen = _f2_pivot_rows(rows, len(edges))
        if len(chosen) == len(edges):
            return chosen, nbrs, len(edges)
    raise SystemExit(f"no odd base graph found for n = {n}")


def multipede(n: int, seed: int, shrunk: bool = False) -> list[list[int]]:
    """R(B(G_n, sigma)) on 22n vertices, or the shrunken multipede
    R*(B*(G_n, sigma)) on 12n vertices: the hardest published benchmark
    family for individualisation-refinement solvers (Neuen and Schweitzer
    2017). Rigid with high probability, so there are no automorphisms for
    the search to prune with."""
    chosen, nbrs, ws = _rigid_odd_base(n, seed)
    if shrunk:
        sub = [nbrs[i] for i in chosen]
        return _cfi_gadget_graph(len(sub), ws, sub, bypass=True)
    return _cfi_gadget_graph(len(nbrs), ws, nbrs, bypass=False)


def is_prime(p: int) -> bool:
    return p > 1 and all(p % d for d in range(2, int(p ** 0.5) + 1))


def corpus(max_n: int, max_hard_n: int):
    """(family, name, matrix) for every instance within the size caps.

    `max_hard_n` caps the families whose search cost grows fastest
    (kneser, johnson, latin, paley): at equal vertex count they run one
    to two orders of magnitude longer than the sparse families."""
    for n in [8, 12, 16, 20, 24, 28, 32, 40, 48, 56, 64, 96, 128, 160, 192,
              224, 255, 320, 384, 448, 512, 640, 768, 896, 1024, 1280, 1536,
              2048, 3072, 4096]:
        if n <= max_n:
            yield "circulant-12", f"circulant{n}-1-2", circulant(n, [1, 2])
    for n in [17, 25, 33, 41, 49, 57, 65, 97, 129, 161, 193, 225, 257, 321,
              385, 449, 513, 641, 769, 897, 1025, 1281, 1537, 2049, 3073]:
        if n <= max_n:
            yield ("circulant-1248", f"circulant{n}-1-2-4-8",
                   circulant(n, [1, 2, 4, 8]))
    for a in [3, 4, 5, 6, 7, 8, 10, 12, 14, 15, 18, 22, 26, 32, 40, 48, 56, 64]:
        if a * a <= max_n:
            yield "grid", f"grid{a}x{a}", grid(a, a)
    for d in range(3, 13):
        if (1 << d) <= max_n:
            yield "hypercube", f"q{d}", hypercube(d)
    mm = 5
    while True:
        n = mm * (mm - 1) // 2
        if n > max_hard_n:
            break
        yield "kneser", f"kneser{mm}-2", kneser(mm, 2)
        yield "johnson", f"johnson{mm}-2", johnson(mm, 2)
        mm += 1 if mm < 10 else 3
    # a spread of primes 1 mod 4, roughly geometric so the curve has
    # points at every scale rather than crowding the small end
    targets = [13, 17, 29, 37, 41, 53, 61, 73, 89, 113, 149, 181, 229, 293,
               373, 461, 577, 733, 929, 1181]
    for t in targets:
        q = t
        while not (q % 4 == 1 and is_prime(q)):
            q += 4
        if q <= max_hard_n:
            yield "paley", f"paley{q}", paley(q)
    for k in [5, 9, 13, 17, 21, 25, 29, 33, 39, 45]:
        if k * k <= max_hard_n:
            yield "latin", f"latin{k}", latin_square(k)
    for n in [10, 14, 18, 22, 26, 30, 36, 42, 48, 56, 64, 80, 96, 128, 160,
              192, 224, 255, 320, 384, 448, 512, 640, 768, 896, 1024, 1280,
              1536, 2048, 3072, 4096]:
        if n <= max_n:
            yield "random", f"gnp{n}-seed1", gnp(n, 1)
    # --- the families the nauty literature names as hard ---
    #
    # Per-family vertex caps, chosen so that every implementation finishes:
    # these families cost orders of magnitude more per vertex than the
    # sparse ones, and they do not agree about which of them is expensive.
    # `projective-plane` is capped hardest because IsoGraph does not
    # terminate within twenty minutes on PG(2,11) on 266 vertices, where
    # nauty needs 0.3 ms; see reports/graphiso-comparison.md.
    # The caps are the corpus's outer edge, not a difficulty judgement:
    # the sweep's per-instance time budget is what actually decides where
    # each family stops, and it stops each implementation separately.
    cap = lambda limit: min(max_hard_n, limit)
    # Strongly regular: `adjtriang`, `triples`, `cliques` and `indsets` are
    # the invariants the user guide offers for these.
    for k in list(range(5, 16)) + list(range(16, 46, 3)):
        if k * k <= cap(2048):
            yield "lattice", f"lattice{k}", lattice(k)
    # Hadamard-matrix graphs: "cellquads is powerful enough to split many
    # difficult graphs, such as hadamard-matrix graphs".
    for k in range(2, 12):
        if 4 * (1 << k) <= cap(4096):
            yield "hadamard", f"hadamard{1 << k}", hadamard(k)
    # Projective planes: what `cellfano` and `cellfano2` are written for.
    for q in [2, 3, 5, 7, 11, 13, 17, 23, 31, 41, 53, 67, 83, 101]:
        if is_prime(q) and 2 * (q * q + q + 1) <= cap(4096):
            yield "projective-plane", f"pg2-{q}", projective_plane(q)
    # Block-design incidence graphs: the target of `celltrips` and `indsets`.
    for mm in range(5, 120, 4):
        if 3 * mm + mm + 3 * mm * (mm - 1) // 2 <= cap(2048):
            yield "steiner", f"sts{3 * mm}", steiner_triple(mm)
    # Cai-Furer-Immerman: built to defeat one-dimensional refinement.
    for k in range(3, 300, 8):
        if 14 * k <= cap(4096):
            yield "cfi", f"cfi{k}", cfi(k)
    # Multipedes and their shrunken form: rigid, so there are no
    # automorphisms to prune with, and the hardest published family.
    for k in range(3, 200, 5):
        if 22 * k <= cap(4096):
            yield "multipede", f"multipede{k}", multipede(k, 12345)
    for k in range(3, 350, 8):
        if 12 * k <= cap(4096):
            yield "shrunken-multipede", f"shrunken{k}", multipede(k, 12345, True)
    # Disjoint components: the one class McKay and Piperno report nauty and
    # Traces losing on, having no component recursion.
    for k in [2, 3, 4, 6, 8, 12, 16, 24, 32, 48, 64, 96, 128, 192, 256]:
        for t, tag in [(16, "g16")]:
            if k * t <= max_n:
                yield "union", f"union{k}x{tag}", union(k, gnp(t, 7))
    # --- the easy end: what the literature says solvers scale on ---
    for n in [16, 32, 64, 128, 256, 512, 1024, 2048, 3072, 4096]:
        if n <= max_n:
            yield "tree", f"tree{n}", random_tree(n, 99)
    for n in [16, 32, 64, 128, 192, 256, 384, 512, 768, 1024, 1536, 2048]:
        if n <= max_n:
            yield "cubic", f"cubic{n}", random_regular(n, 3, 5150 + n)
    for n in [32, 64, 128, 256, 512, 1024, 2048, 3072, 4096]:
        if n <= max_n:
            yield "sparse-random", f"sparse{n}", gnp(n, 31, 10, n)


def main() -> int:
    parser = argparse.ArgumentParser()
    parser.add_argument("--max-n", type=int, default=1024)
    parser.add_argument("--max-hard-n", type=int, default=1024)
    parser.add_argument("--split", type=Path, default=None,
                        help="write one file per instance into this "
                             "directory, with an index.jsonl beside them, "
                             "so a sweep can run each under its own time "
                             "budget in its own process")
    args = parser.parse_args()

    def render(m: list[list[int]], name: str, family: str) -> str:
        return (f"G {name} {family} {len(m)}\n" +
                "".join("".join("1" if x else "0" for x in row) + "\n"
                        for row in m))

    if args.split is not None:
        args.split.mkdir(parents=True, exist_ok=True)
        index = []
        for family, name, m in corpus(args.max_n, args.max_hard_n):
            path = args.split / f"{name}.graph"
            path.write_text(render(m, name, family))
            index.append({"family": family, "name": name, "n": len(m),
                          "path": str(path)})
        (args.split / "index.jsonl").write_text(
            "".join(json.dumps(e) + "\n" for e in index))
        print(f"{len(index)} instances -> {args.split}", file=sys.stderr)
        return 0

    out = sys.stdout
    count = 0
    for family, name, m in corpus(args.max_n, args.max_hard_n):
        out.write(render(m, name, family))
        count += 1
    print(f"{count} instances", file=sys.stderr)
    return 0


if __name__ == "__main__":
    sys.exit(main())
