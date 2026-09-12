The proposed scalar list Berkowitz checker does not meet the issue's rank-relative performance bar in the measured prototype. This is a checker feasibility result, not a completed `char_poly` implementation or a proof that every possible Berkowitz encoding must fail.

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

The correspondence theorem `equiv_charPoly` exists and the requested mathematics is sound; the measured conflict is between the prescribed scalar moment-vector certificate and the required timing bar. Completing frontend and soundness work around this prototype would still fail the acceptance condition. The directive needs to clarify whether it permits a different verification strategy (reducing the arithmetic checked) or intends a different performance threshold. No theorem has been weakened, and no `sorry` or axiom was added.

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
