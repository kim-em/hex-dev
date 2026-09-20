# CAD sample experiments

Manual experiments for [#10301](https://github.com/kim-em/hex-dev/issues/10301).
The interpretation and retained observations are in
[the report](../../reports/cad-sample-costs.md). These targets are not default
Lake targets, released source, or CI benchmarks.

Build the experiment and its proof checks from the repository root:

```sh
lake build CadSampleCostsExperiment cad_sample_costs
```

The runtime executable separates integer-root enumeration, canonical coefficient
substitution, and `RealAlgebraicPoly.roots`. `runThunk` keeps computation between
the clocks: inspect the generated C when changing the timer (a pure `let` can
move after the second clock). The sample selection is deterministic: take the
negative root for `nlsat`, otherwise the largest real root. Every returned root
and every specialized coefficient records its primitive minimal polynomial,
degree, and maximum absolute integer coefficient.

`Emit.lean` builds untrusted RCF certificates. `Fixtures.lean` contains their
literal terms. Each matched `Literal`/`Replay` pair elaborates identical input,
certificate, and source-correspondence declarations; `Replay` additionally checks
`Certificate.check` in the kernel, applies soundness, and binds the answer to the
source sign statement. Where the source query has already eliminated a variable,
the sample theorem applies the identities in `Transport.lean`. Those reusable
identity proofs and parameter-existence proofs are built before measurements.
The corpus supplies those substitutions by hand; there is no automatic common-
field certificate exporter here.

Regenerate committed literals and carrier statistics after editing `Emit.lean`:

```sh
lake build +CadSampleCosts.Emit:olean > /tmp/cad-emit.log
python3 experiments/CadSampleCosts/generate.py /tmp/cad-emit.log
lake build CadSampleCostsExperiment cad_sample_costs
```

Build the external traced solver at its pinned revision in a separate directory:

```sh
git clone --branch z3-4.15.3 --depth 1 https://github.com/Z3Prover/z3.git /tmp/cad-z3
git -C /tmp/cad-z3 rev-parse HEAD
# Expected: a121e6c6e95c60f50d1561f03762805dabc969e1
git -C /tmp/cad-z3 apply "$PWD/experiments/CadSampleCosts/z3-trace.patch"
cmake -S /tmp/cad-z3 -B /tmp/cad-z3/build \
  -DCMAKE_BUILD_TYPE=Release -DZ3_ENABLE_TRACING_FOR_NON_DEBUG=ON \
  -DZ3_BUILD_LIBZ3_SHARED=OFF
cmake --build /tmp/cad-z3/build --target shell -j4
```

The patch adds trace statements only. `CAD_BEGIN`/`CAD_END` delimit a theory
explanation; `CAD_PROJ` records each nonconstant projected factor enqueued by
`insert_fresh_factors_in_todo`; duplicate polynomial strings count once within
an explanation. Input-core polynomials are not counted as projected factors.
`CAD_LEARNED` independently records allocated learned clauses, including
resolvents. An explanation is a cell clause usable by conflict analysis; it is
not necessarily stored as a learned clause. Counts are neither global CAD cell
counts nor counts of just the final surviving clause database. The fixtures use
original projection (`cell_sample=false`), fixed variable order and seed zero.

Commit experiment sources before collecting the fixed four-round schedule:

```sh
python3 experiments/CadSampleCosts/run.py reports/bench-results/cad-sample-costs \
  --z3 /tmp/cad-z3/build/z3
```

The output directory must not already exist. The runner acquires one automatic
CPU lease without checking whether that CPU is quiet. Runtime cases follow a
fixed trial-major order. Adjacent proof pairs alternate Literal/Replay and
Replay/Literal across four rounds. Only the measured module's build artifacts
are removed. Runtime and solver processes have a 30-second operational limit;
fresh proof builds have 120 seconds. A timeout kills that process group, retains
its partial output and records the failure; it does not trigger a retry. All
completed observations and raw logs are retained, with load as context.

`runs.jsonl` stores every observation; `meta.json` stores host, commit, toolchain,
source hashes, and the traced solver binary hash. Compressed logs contain the
full command output, including diagnostics and the theorem axiom lists. Raw
traces retain the explanation bodies and projection polynomials. No timing
from this corpus is a portable budget or an asymptotic complexity claim.

Render the report tables without rerunning measurements:

```sh
python3 experiments/CadSampleCosts/summarize.py reports/bench-results/cad-sample-costs
```
