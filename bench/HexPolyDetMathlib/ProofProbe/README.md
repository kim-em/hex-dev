# Determinant proof comparisons

The measured `*Hex.lean` and `*Mathlib.lean` modules export a theorem or a certified
result. Every build elaborates it and checks the proof in Lean's kernel. They
contain no axiom printing, trace output or profiling. Both arms and their
`*Baseline.lean` modules use identical imports, so the comparison isolates theorem
work in a common environment. It is not an import-cost comparison.

Each `*Audit.lean` imports its proof module and prints the axioms of that exact
exported declaration. The runner checks these builds separately before timing;
a failed or missing audit prevents that arm from contributing timing samples.
Audit builds count towards the overall allowance but not towards proof times.
`ImportsHex.lean` and `ImportsMathlib.lean` measure each interface's own imports
separately, including Lake startup.

`OriginalQuadratic4` is the exact two-variable quadratic matrix and target from
#10320. `Tridiagonal4` and `ResultTridiagonal4` retain the simpler one-variable
tridiagonal fixture formerly called `Quadratic4` and `ResultQuadratic4`.

For the focused comparison, run from the repository root:

```sh
python3 -m scripts.bench.det_general \
  --case OriginalQuadratic4 --case Products5 --case Independent6 \
  --case RankOne10 --case ResultSymbolic3 \
  --seconds 600 --output /tmp/determinant-comparison.json
```

The schedule uses six adjacent pairs in alternating AB/BA order, serially on an
automatically leased CPU. Every process has a 60-second ceiling, and audits,
import preparation, import measurements and proof builds share the total
allowance. A timeout suppresses larger comparable inputs. Retain partial results
and failed samples; do not restart the allowance to complete a grid.

The JSON records full proof-build time, its adjacent import baseline, their
difference, separate import samples and audit output. Small or negative differences
can reflect build variation; report them without inventing a speedup. The v2 schema
keeps these components separate. Historical v1 samples included axiom audits in
proof times and used different imports in the two arms.

These are manual proof comparisons, not native computational benchmarks. No
Mathlib-importing runtime benchmark or CI timing gate is added.
