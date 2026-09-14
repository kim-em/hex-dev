These probes compare the packed `char_poly` frontend with the frozen original
frontend and the scalar list checker. `generate.py` uses identical signed
8-bit matrices on the dense 4, 8, 16, 32 ladder. `packed-plan.json` records the
schedule, kernel targets, baseline commit, and operational timeout;
`compare.py` retains every completed sample and records timed-out arms.
The shipping measurements are in `HexCharPolyMathlib/SPEC/hex-char-poly-mathlib.md`.

The scalar study below is retained as baseline evidence. Its rank-relative
threshold is superseded by comparison with Hex's own characteristic-polynomial
implementations and explicit kernel targets.

The prototype checks all `B * w = next` moment transitions, all scalar moments, Toeplitz columns and intermediate descending coefficient lists. Its arithmetic path is structural recursion over integer lists with direct `Int.mul`/`Int.add`; certificates contain precomputed literal vectors. It does not run `charPoly`, access `A i j`, or use `Vector`, `Fin`, `Array`, `Hex.Matrix`, or well-founded recursion during arithmetic checking. A single synchronous `mkAuxTheorem` checks each certificate, with no `Kernel.whnf` precheck. All checker proofs audit to `[propext]`. The Python generator's final coefficients agree with SymPy for all four dimensions.

Fixtures: `random.Random(10212 + n)`, entries from `randrange(-128, 128)`, dimensions 4, 8, 16, 32. Toolchain `leanprover/lean4:v4.34.0-rc2`, base `f56640371`. Shared host `chungus2`; affinity CPU leases follow the existing `/tmp/hex-bench-cpu-*.lock` convention. Host load is retained as context; no completed sample was discarded.

Diagnostic kernel `type checking` times (single profiles on each variant's recorded CPU, **not paired ratios**):

| dimension | direct list checker (CPU 95) | explicit trailing blocks (CPU 1) | constructor integer literals (CPU 28) | shipped rank on identical input (CPU 55) |
|---|---:|---:|---:|---:|
| 4 | 11 ms (initial unpinned functional probe) | 20.6 ms | not measured | 9.11 ms |
| 8 | 126 ms | 177 ms | 87 ms | 22.8 ms |
| 16 | 2.45 s | 3.32 s | 1.94 s | 156 ms |
| 32 | 38.9 s | 38.3 s | 34.2 s | 1.43 s |

The explicit-block variant checks each copied trailing block against the corresponding tails before using its literal rows in the moment checks. The constructor-literal variant uses `Int.ofNat`/`Int.negSucc` directly. Neither closes the observed gap.

A subsequent adjacent profile pair on **one CPU (90), identical dense16 input** took **2.57 s** for the constructor-literal checker and **269 ms** for the shipped rank frontend (9.55×). Six fresh-module wall-time pairs on that CPU, alternating candidate/reference and reference/candidate, yielded medians 6.434 s and 4.085 s respectively. These wall times include imports and Lake overhead and are not kernel times; this is a diagnostic runner, not the release-quality Mathlib comparator sweep. All 12 samples and the profile pair are retained in `evidence/paired.json`.

A variant that computes each moment vector as a list instead of carrying it
in the witness (`ComputedSupport.lean`) takes 337 ms at n=8 and 4.24 s at
n=16 in its diagnostic profiles on CPU 40. One subsequent adjacent dense16
pair on CPU 49 takes **2.58 s** for that checker and **256 ms** for rank
(10.08×). It also misses the bar. Both runs are retained; this variant has no
measurements at n=4 or n=32. Its moment loop explicitly uses structural
recursion on the moment list.

The scalar operation counts explain the widening gap. At trailing-block size `k`, moment verification costs `k³` multiplications and Toeplitz verification costs `(k+1)(k+4)/2`. Summed over `k=0,...,n-1`, that is 15,352 at n=16 and 252,528 at n=32. The shipped full-rank lower-bound checker performs `sum(j², j=1,...,n)`: 1,496 and 11,440, on small natural-number residues. A literal-layer bridge cannot remove these arithmetic checks.

The scalar measurements motivate packing the moment and Toeplitz products.
The rank arm remains useful operation-count context and is not the current
acceptance threshold. The scalar support sources and their exact measurement
snapshots remain available for reproduction.

Reproduce from the repository root:

```bash
python bench/HexCharPolyMathlib/ProofProbe/generate.py
lake build HexRankMathlib HexCharPolyMathlib.ProofProbe.Support HexCharPolyMathlib.ProofProbe.BlockSupport HexCharPolyMathlib.ProofProbe.ComputedSupport
python bench/HexCharPolyMathlib/ProofProbe/paired.py .cache/char-poly-premise-run
```

The output directory must be new so a completed run cannot be overwritten.
For the individual profiled modules, build
`HexCharPolyMathlib.ProofProbe.Dense{4,8,16,32}{Check,Block,Quoted,Computed,Rank}:olean`
through Lake (expand the desired dimension and variant). A fresh measurement
requires removing only that module's generated `.lake/build/lib/lean` artifacts.
`generate.py` recreates the measured input modules byte for byte. The `Check`
and `Quoted` variants use `Support.lean`; the explicit-block variant uses
`BlockSupport.lean`. The generated modules are ignored by git. The recorded
profiles, source hashes, paired samples, and raw logs live in `evidence/`.
The `.lean.txt` files there are exact snapshots of the measured support sources.
Reproduction sources prepend copyright headers to those snapshots.

To reproduce the three-arm comparison, prepare a detached checkout of the
`baseline_commit` in `packed-plan.json`, install its dependencies, and build
`HexCharPolyMathlib` there. Then, from the implementation checkout:

```bash
python3 bench/HexCharPolyMathlib/ProofProbe/generate.py
lake build HexCharPolyMathlib HexCharPolyMathlib.ProofProbe.Support
python3 bench/HexCharPolyMathlib/ProofProbe/compare.py .cache/char-poly-comparison --baseline-root /path/to/baseline
```

The runner copies only the generated `Dense*Original.lean` probes into the
baseline checkout. It removes only the measured module's build artifacts to
force each sample to be fresh. Both checkouts' imports must be built before
measurement; the output directory must not already exist. All samples enable
Lean's profiler. Each trial runs a packed/scalar pair and a packed/original
pair at each dimension, reversing the order on alternating trials. A timeout
censors that arm/dimension and skips its later pairs. The original frontend's
size-32 timeout supplies an end-to-end bound, not an invented kernel time.
